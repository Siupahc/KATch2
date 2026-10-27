#!/usr/bin/env python3
"""Read `.nkt` files and translate them to KATch2 (`.nksynth`) and MuVal (`.hes`).

An `.nkt` file describes dup-free NetKAT problems over named fields:

    field sw 2                      // field `sw` on 2 bits: values 0..3
    def pol = (sw = 1; pt := 2) + (sw = 2; pt := 2)
    member through: (sw=1, pt=0) -> (sw=3, pt=1) in net
    equiv  summary: sw = 1; net; sw = 3 === sw = 1; sw := 3
    incl   isolated: sw = 3; net; sw = 1 <= 0

Each `member` / `equiv` / `incl` is one check, translated separately:
  * to KATch2, where every field becomes a bit range `x[a..b]`;
  * to MuVal, where every field becomes an integer argument (see README.md).

Standalone use:  python nkt.py example.nkt [--encoding direct|naive]
                 (prints the generated .nksynth and .hes)
"""

import re
from dataclasses import dataclass

# ─────────────────────────────── AST ───────────────────────────────
# ('zero',) ('one',) ('test', f, v) ('neq', f, v) ('assign', f, v)
# ('not', e) ('plus', a, b) ('seq', a, b) ('star', e)


class NktError(Exception):
    pass


@dataclass
class Check:
    name: str
    kind: str  # 'member' | 'equiv' | 'incl'
    lhs: object = None  # equiv/incl: expression; member: None
    rhs: object = None  # equiv/incl: expression; member: the program
    pkt_in: dict = None
    pkt_out: dict = None


@dataclass
class Problem:
    fields: dict  # name -> number of bits (declaration order is kept)
    checks: list


# ─────────────────────────────── Lexer ───────────────────────────────

TOKEN_RE = re.compile(
    r"\s*(?:(===|:=|==|!=|<=|->|[=+;*!(),:])|([A-Za-z_][A-Za-z0-9_]*)|(\d+))"
)
KEYWORDS = ("field", "def", "member", "equiv", "incl")


def tokenize(text):
    toks, pos = [], 0
    text = text.rstrip()
    while pos < len(text):
        m = TOKEN_RE.match(text, pos)
        if not m or m.end() == pos:
            raise NktError(f"unexpected character: {text[pos:pos + 20]!r}")
        sym, ident, num = m.groups()
        toks.append(("sym", sym) if sym else ("id", ident) if ident else ("num", int(num)))
        pos = m.end()
    return toks


class Parser:
    def __init__(self, toks, fields, defs):
        self.toks, self.i, self.fields, self.defs = toks, 0, fields, defs

    def peek(self, k=0):
        return self.toks[self.i + k] if self.i + k < len(self.toks) else (None, None)

    def eat(self, kind=None, val=None):
        tok = self.peek()
        if tok[0] is None or (kind and tok[0] != kind) or (val is not None and tok[1] != val):
            raise NktError(f"expected {val or kind}, found {tok[1]!r}")
        self.i += 1
        return tok[1]

    def at(self, val):
        return self.peek() == ("sym", val)

    def done(self):
        return self.i >= len(self.toks)

    # expr := seq ('+' seq)*     seq := unary (';' unary)*
    # unary := '!' unary | atom '*'*
    def expr(self):
        e = self.seq()
        while self.at("+"):
            self.eat()
            e = ("plus", e, self.seq())
        return e

    def seq(self):
        e = self.unary()
        while self.at(";"):
            self.eat()
            e = ("seq", e, self.unary())
        return e

    def unary(self):
        if self.at("!"):
            self.eat()
            e = self.unary()
            if not is_test(e):
                raise NktError("'!' only applies to a test")
            return ("not", e)
        e = self.atom()
        while self.at("*"):
            self.eat()
            e = ("star", e)
        return e

    def atom(self):
        kind, val = self.peek()
        if kind == "num" and val in (0, 1):
            self.eat()
            return ("zero",) if val == 0 else ("one",)
        if self.at("("):
            self.eat()
            e = self.expr()
            self.eat("sym", ")")
            return e
        if kind == "id":
            name = self.eat()
            if name in self.fields:
                op = self.eat("sym")
                v = self.eat("num")
                if v >= 2 ** self.fields[name]:
                    raise NktError(f"value {v} too large for field {name}")
                if op in ("=", "=="):
                    return ("test", name, v)
                if op == "!=":
                    return ("neq", name, v)
                if op == ":=":
                    return ("assign", name, v)
                raise NktError(f"unexpected operator after field {name}: {op}")
            if name in self.defs:
                return self.defs[name]
            raise NktError(f"unknown name: {name} (neither a field nor a def)")
        raise NktError(f"expected an expression, found {val!r}")

    def packet(self):
        self.eat("sym", "(")
        pkt = {}
        while True:
            f = self.eat("id")
            if f not in self.fields:
                raise NktError(f"unknown field: {f}")
            self.eat("sym", "=")
            pkt[f] = self.eat("num")
            if self.at(","):
                self.eat()
                continue
            break
        self.eat("sym", ")")
        missing = [f for f in self.fields if f not in pkt]
        if missing:
            raise NktError(f"incomplete packet, missing fields: {missing}")
        return pkt


def is_test(e):
    t = e[0]
    if t in ("zero", "one", "test", "neq"):
        return True
    if t == "not":
        return is_test(e[1])
    if t in ("plus", "seq"):
        return is_test(e[1]) and is_test(e[2])
    return False


def star_free(e):
    t = e[0]
    if t == "star":
        return False
    if t in ("plus", "seq"):
        return star_free(e[1]) and star_free(e[2])
    if t == "not":
        return star_free(e[1])
    return True


def parse_nkt(text):
    """Split the file into statements (a statement starts with a keyword at the
    beginning of a line and may continue on the following lines)."""
    stmts = []
    for line in text.splitlines():
        line = re.sub(r"(//|#).*", "", line)
        if not line.strip():
            continue
        first = line.split()[0].rstrip(":")
        if first in KEYWORDS:
            stmts.append(line.strip())
        elif stmts:
            stmts[-1] += " " + line.strip()
        else:
            raise NktError(f"line outside of any statement: {line.strip()!r}")

    fields, defs, checks = {}, {}, []
    for st in stmts:
        kw, rest = st.split(None, 1)
        try:
            if kw == "field":
                name, bits = rest.split()
                fields[name] = int(bits)
                continue
            if kw == "def":
                name, body = rest.split("=", 1)
                p = Parser(tokenize(body), fields, defs)
                defs[name.strip()] = p.expr()
                if not p.done():
                    raise NktError(f"trailing text: {p.peek()[1]!r}")
                continue
            name, body = rest.split(":", 1)
            name = name.strip()
            p = Parser(tokenize(body), fields, defs)
            if kw == "member":
                pin = p.packet()
                p.eat("sym", "->")
                pout = p.packet()
                p.eat("id", "in")
                checks.append(Check(name, "member", None, p.expr(), pin, pout))
            else:
                lhs = p.expr()
                p.eat("sym", "===" if kw == "equiv" else "<=")
                checks.append(Check(name, kw, lhs, p.expr()))
            if not p.done():
                raise NktError(f"trailing text: {p.peek()[1]!r}")
        except NktError as err:
            raise NktError(f"in “{st[:60]}”: {err}") from None
    if not fields:
        raise NktError("no field declared (field NAME BITS)")
    return Problem(fields, checks)


# ─────────────────────────── to KATch2 ───────────────────────────


def bit_ranges(fields):
    out, off = {}, 0
    for f, w in fields.items():
        out[f] = (off, off + w)
        off += w
    return out


def to_katch(e, rng):
    t = e[0]
    if t == "zero":
        return "0"
    if t == "one":
        return "1"
    if t in ("test", "neq", "assign"):
        a, b = rng[e[1]]
        if t == "assign":
            return f"x[{a}..{b}] := {e[2]}"
        s = f"x[{a}..{b}] ~ {e[2]}"
        return s if t == "test" else f"!({s})"
    if t == "not":
        return f"!({to_katch(e[1], rng)})"
    if t == "star":
        return f"({to_katch(e[1], rng)})*"
    op = " + " if t == "plus" else "; "
    return f"({to_katch(e[1], rng)}{op}{to_katch(e[2], rng)})"


def check_to_nksynth(prob, chk):
    rng = bit_ranges(prob.fields)
    if chk.kind == "member":
        pair = [("test", f, v) for f, v in chk.pkt_in.items()]
        pair += [("assign", f, v) for f, v in chk.pkt_out.items()]
        lhs = " ; ".join(to_katch(x, rng) for x in pair)
        return f"// {chk.name}\nassert ({lhs}) <= ({to_katch(chk.rhs, rng)})\n"
    op = "==" if chk.kind == "equiv" else "<="
    return f"// {chk.name}\nassert ({to_katch(chk.lhs, rng)}) {op} ({to_katch(chk.rhs, rng)})\n"


# ─────────────────────────── to MuVal (.hes) ───────────────────────────
# Formulas are strings; 'true' / 'false' are simplified on the fly.
# A "term" is either an int (constant) or a variable name.

TRUE, FALSE = "true", "false"


def AND(*parts):
    ps = [p for p in parts if p != TRUE]
    if FALSE in ps:
        return FALSE
    if not ps:
        return TRUE
    return ps[0] if len(ps) == 1 else " /\\ ".join(f"({p})" if " " in p else p for p in ps)


def OR(*parts):
    ps = [p for p in parts if p != FALSE]
    if TRUE in ps:
        return TRUE
    if not ps:
        return FALSE
    return ps[0] if len(ps) == 1 else " \\/ ".join(f"({p})" if " " in p else p for p in ps)


def EQ(a, b):
    if isinstance(a, int) and isinstance(b, int):
        return TRUE if a == b else FALSE
    return TRUE if a == b else f"{a} = {b}"


def NEQ(a, b):
    if isinstance(a, int) and isinstance(b, int):
        return TRUE if a != b else FALSE
    return FALSE if a == b else f"{a} != {b}"


class HesEncoder:
    """Translate NetKAT expressions into muCLP formulas.

    encoding = 'naive'  : literal translation of the rules (one `exists` per `;`);
    encoding = 'direct' : star-free parts are executed symbolically (tests and
                          assignments are composed), without `exists`.
    """

    def __init__(self, fields, encoding="direct"):
        self.fields = list(fields)
        self.encoding = encoding
        self.preds = []  # lines "Name (...): bool =mu body;"
        self.star_names = {}
        self.fresh = 0

    # -- helpers --
    def vars(self, prefix):
        return {f: f"{prefix}_{f}" for f in self.fields}

    def eqs(self, xs, ys):
        return AND(*(EQ(xs[f], ys[f]) for f in self.fields))

    def new_mid(self):
        self.fresh += 1
        return self.vars(f"m{self.fresh}")

    def exists(self, ms, body):
        if body == FALSE:
            return FALSE
        binders = " ".join(f"({ms[f]}: int)" for f in self.fields)
        return f"exists {binders}. {body}"

    def call(self, name, xs, ys):
        return " ".join([name] + [str(xs[f]) for f in self.fields] + [str(ys[f]) for f in self.fields])

    # -- tests: a formula over the packet xs --
    def test(self, e, xs, positive=True):
        t = e[0]
        if t == "zero":
            return FALSE if positive else TRUE
        if t == "one":
            return TRUE if positive else FALSE
        if t == "test":
            return EQ(xs[e[1]], e[2]) if positive else NEQ(xs[e[1]], e[2])
        if t == "neq":
            return NEQ(xs[e[1]], e[2]) if positive else EQ(xs[e[1]], e[2])
        if t == "not":
            return self.test(e[1], xs, not positive)
        a, b = self.test(e[1], xs, positive), self.test(e[2], xs, positive)
        conj = (t == "seq") == positive  # De Morgan
        return AND(a, b) if conj else OR(a, b)

    # -- normal form of a star-free expression: list of (guard, output packet) --
    def nf(self, e, xs):
        t = e[0]
        if t == "test":
            # after the test f = v we KNOW that f is v: propagate the constant,
            # which removes contradictory branches further down
            g = EQ(xs[e[1]], e[2])
            return [] if g == FALSE else [(g, {**xs, e[1]: e[2]})]
        if t == "assign":
            return [(TRUE, {**xs, e[1]: e[2]})]
        if t == "plus":
            return self.nf(e[1], xs) + self.nf(e[2], xs)
        if t == "seq":
            out = []
            for g1, x1 in self.nf(e[1], xs):
                for g2, x2 in self.nf(e[2], x1):
                    g = AND(g1, g2)
                    if g != FALSE:
                        out.append((g, x2))
            return out
        if is_test(e):  # 0, 1, f != v, !(...)
            g = self.test(e, xs)
            return [] if g == FALSE else [(g, xs)]
        raise NktError(f"nf: unexpected case {t}")

    # -- main translation: formula "e turns xs into ys" --
    def rel(self, e, xs, ys):
        t = e[0]
        if self.encoding == "direct" and star_free(e):
            return OR(*(AND(g, self.eqs(x2, ys)) for g, x2 in self.nf(e, xs)))
        if is_test(e):
            return AND(self.eqs(xs, ys), self.test(e, xs))
        if t == "assign":
            f, v = e[1], e[2]
            return AND(EQ(ys[f], v), *(EQ(xs[g], ys[g]) for g in self.fields if g != f))
        if t == "plus":
            return OR(self.rel(e[1], xs, ys), self.rel(e[2], xs, ys))
        if t == "seq":
            if self.encoding == "direct" and is_test(e[2]):
                # p ; test: no intermediate packet needed, test the output directly
                return AND(self.rel(e[1], xs, ys), self.test(e[2], ys))
            return self.seq(e[1], lambda mid: self.rel(e[2], mid, ys), xs)
        if t == "star":
            return self.call(self.star_pred(e[1]), xs, ys)
        raise NktError(f"unexpected case {t}")

    def seq(self, p, rest, xs):
        """p ; (rest): in direct mode, if p is star-free we substitute; otherwise an `exists`."""
        if self.encoding == "direct" and star_free(p):
            return OR(*(AND(g, rest(x2)) for g, x2 in self.nf(p, xs)))
        ms = self.new_mid()
        return self.exists(ms, AND(self.rel(p, xs, ms), rest(ms)))

    def star_pred(self, p):
        key = repr(p)
        if key in self.star_names:
            return self.star_names[key]
        name = f"Star{len(self.star_names) + 1}"
        self.star_names[key] = name  # before the body: the star calls itself
        i, o = self.vars("i"), self.vars("o")
        body = OR(self.eqs(i, o), self.seq(p, lambda mid: self.call(name, mid, o), i))
        params = " ".join(f"({i[f]}: int)" for f in self.fields)
        params += " " + " ".join(f"({o[f]}: int)" for f in self.fields)
        self.preds.append(f"{name} {params}: bool =mu\n  {body};")
        return name


def check_to_hes(prob, chk, encoding="direct"):
    enc = HesEncoder(prob.fields, encoding)
    i, o = enc.vars("i"), enc.vars("o")
    if chk.kind == "member":
        query = enc.rel(chk.rhs, chk.pkt_in, chk.pkt_out)
    else:
        a, b = enc.rel(chk.lhs, i, o), enc.rel(chk.rhs, i, o)
        dom = AND(*(f"0 <= {v[f]} /\\ {v[f]} <= {2 ** w - 1}"
                    for v in (i, o) for f, w in prob.fields.items()))
        binders = " ".join(f"({v[f]}: int)" for v in (i, o) for f in prob.fields)
        op = "<=>" if chk.kind == "equiv" else "=>"
        query = f"forall {binders}. ({dom}) => (({a}) {op} ({b}))"
    preds = enc.preds or ["Unused (x: int): bool =mu x = 0;"]  # the grammar requires >= 1 predicate
    return f"/* {chk.name} ({chk.kind}, {encoding} encoding) */\n{query}\ns.t.\n" + "\n".join(preds) + "\n"


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file")
    ap.add_argument("--encoding", choices=["direct", "naive"], default="direct")
    args = ap.parse_args()
    prob = parse_nkt(open(args.file, encoding="utf-8").read())
    for chk in prob.checks:
        print(f"===== {chk.name} =====")
        print("--- KATch2 (.nksynth)")
        print(check_to_nksynth(prob, chk))
        print(f"--- MuVal (.hes, {args.encoding})")
        print(check_to_hes(prob, chk, args.encoding))
