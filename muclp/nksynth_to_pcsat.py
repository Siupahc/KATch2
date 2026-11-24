#!/usr/bin/env python3
"""Translate NetKAT synthesis problems (`.nksynth`) to pfwCSP (`.smt2`) for CoAR's PCSat.

Architecture (compiler pipeline):
  Stage 0  Parse `.nksynth` (`hole`, `def`, `assert <= / ==`), partition bit-ranges into
           integer packet fields, and decompose `dup` (for dup-free hole synthesis).
  Stage 1  Pure generic translation (`T+` / `T-` over packet pairs `(p, p')`, with `St` for
           left-stars and `D` + `declare-wfp W_` for right-stars).
  Stage 2  Composable optimization passes:
             1. `subst_seq`      Eliminate intermediate packets in hole-free, star-free subterms
                                 via symbolic Guarded-Assignment Normal Form (SPP-NF) + hash-join.
             2. `hole_shape`     Infer hole input guards, output constants, preserved (frame) fields,
                                 and contextual dead-output fields (`X ; E`), optionally reducing `X`'s arity.
             3. `project_st`     Drop unused start-packet fields in left-stars (`St(p, p') -> R(p')`).
             4. `elim_exists`    Eliminate existential packet witnesses on the RHS by distributing over
                                 finite cables / pre-images and propagating hole frame equalities.
             5. `bfs_wf`         (Optional) Fix `W_` using BFS shortest-path distances on `topo`
                                 (sound, incomplete if detours are required).
             6. `compile_paths`  Exact simple-path compilation for right-stars `D`: when active
                                 location/port fields are finite and other fields are preserved,
                                 replace `D` and `W_` by the disjunction of all simple paths in the
                                 symbolic 1-step transition graph (both sound and complete).

Presets (`--preset`):
  raw       Stage 1 literal generic encoding (every `;` uses `exists`)
  generic   Pass 1 (`subst_seq`) — matches `hospital_generic.smt2`
  noexists  Passes 1 + 2(frame) + 4 (`elim_exists`) — matches `hospital_generic_noexists.smt2`
  paths     Passes 1 + 2(frame) + 4 + 6 (`compile_paths`) — matches `hospital_paths.smt2`
  all       Passes 1 + 2(frame+context+arity) + 3(`project_st`) + 4(`elim_exists`) + 6(`compile_paths`)
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path
import re
import sys
from typing import Iterable


# =============================================================================
# 0. Front-end: `.nksynth` AST, Lexer, Parser, and Bit-Range Field Partitioning
# =============================================================================


class TranslateError(Exception):
    pass


@dataclass(frozen=True)
class FieldInfo:
    idx: int
    name: str
    start: int
    end: int

    @property
    def width(self) -> int:
        return self.end - self.start

    @property
    def max_val(self) -> int:
        return (1 << self.width) - 1


# NetKAT AST nodes (hashable tuples for lightweight structural sharing):
#   ('zero',)
#   ('one',)
#   ('top',)
#   ('dup',)
#   ('hole', name)
#   ('rtest', start, end, val)      # bit-range [start..end) == val
#   ('rassign', start, end, val)    # bit-range [start..end) := val
#   ('test', f_idx, val)            # partitioned integer field == val
#   ('neq', f_idx, val)             # partitioned integer field != val
#   ('assign', f_idx, val)          # partitioned integer field := val
#   ('not', e)                      # test negation
#   ('plus', a, b)
#   ('seq', a, b)
#   ('star', e)


TOKEN_RE = re.compile(
    r"""\s*(?:
        (//[^\n]*)                              | # comment
        (:=|==|<=|\.\.|[=+;*!()\[\]~])          | # symbols
        (0b[01]+|0x[0-9a-fA-F]+|\d+)            | # integer literals
        ([A-Za-z_][A-Za-z0-9_]*)                  # identifiers / keywords
    )""",
    re.VERBOSE,
)

STATEMENT_STARTERS = {"hole", "def", "assert"}


def tokenize_nksynth(source: str) -> list[tuple[str, object]]:
    tokens: list[tuple[str, object]] = []
    source = source.rstrip()
    pos = 0
    n = len(source)
    while pos < n:
        m = TOKEN_RE.match(source, pos)
        if not m or m.end() == pos:
            snippet = source[pos : pos + 30]
            raise TranslateError(f"Unexpected syntax near: {snippet!r}")
        comment, sym, num, ident = m.groups()
        pos = m.end()
        if comment:
            continue
        if sym:
            tokens.append(("sym", sym))
        elif num:
            tokens.append(("num", int(num, 0)))
        elif ident:
            tokens.append(("id", ident))
    return tokens


class NkSynthParser:
    def __init__(self, tokens: list[tuple[str, object]]):
        self.toks = tokens
        self.i = 0
        self.holes: list[str] = []
        self.hole_set: set[str] = set()
        self.defs: dict[str, tuple] = {}
        self.asserts: list[tuple[str, tuple, tuple]] = []  # (op: '<='|'==', lhs, rhs)

    def peek(self, k: int = 0) -> tuple[str | None, object]:
        idx = self.i + k
        return self.toks[idx] if idx < len(self.toks) else (None, None)

    def eat(self, kind: str | None = None, val: object = None) -> object:
        tk, tv = self.peek()
        if tk is None or (kind and tk != kind) or (val is not None and tv != val):
            raise TranslateError(f"Expected {val or kind}, got {tv!r} (token #{self.i})")
        self.i += 1
        return tv

    def at(self, kind: str, val: object = None) -> bool:
        tk, tv = self.peek()
        return tk == kind and (val is None or tv == val)

    def parse_program(self):
        while self.peek()[0] is not None:
            kw = self.eat("id")
            if kw == "hole":
                name = str(self.eat("id"))
                if name not in self.hole_set:
                    self.holes.append(name)
                    self.hole_set.add(name)
            elif kw == "def":
                name = str(self.eat("id"))
                op = self.eat("sym")
                if op not in ("=", "=="):
                    raise TranslateError(f"Expected '=' after def {name}, got {op!r}")
                self.defs[name] = self.parse_expr()
            elif kw == "assert":
                lhs = self.parse_expr()
                op = self.eat("sym")
                if op == "<=":
                    norm_op = "<="
                elif op in ("=", "=="):
                    norm_op = "=="
                else:
                    raise TranslateError(f"Expected '<=' or '==' in assert, got {op!r}")
                rhs = self.parse_expr()
                self.asserts.append((norm_op, lhs, rhs))
            else:
                raise TranslateError(f"Expected 'hole', 'def', or 'assert', got {kw!r}")

    def parse_expr(self) -> tuple:
        parts = [self.parse_seq()]
        while self.at("sym", "+"):
            self.eat()
            parts.append(self.parse_seq())
        # Balanced reduction avoids deep Python recursion on 1000-branch policies
        while len(parts) > 1:
            nxt = []
            for j in range(0, len(parts), 2):
                if j + 1 < len(parts):
                    nxt.append(("plus", parts[j], parts[j + 1]))
                else:
                    nxt.append(parts[j])
            parts = nxt
        return parts[0]

    def parse_seq(self) -> tuple:
        parts = [self.parse_unary()]
        while self.at("sym", ";"):
            self.eat()
            parts.append(self.parse_unary())
        # Right-associate `;` so `h1 ; pol ; topo` groups as `h1 ; (pol ; topo)` and
        # adjacent hole-free SPPs compose immediately!
        e = parts[-1]
        for p in reversed(parts[:-1]):
            e = ("seq", p, e)
        return e

    def parse_unary(self) -> tuple:
        if self.at("sym", "!"):
            self.eat()
            return ("not", self.parse_unary())
        e = self.parse_atom()
        while self.at("sym", "*"):
            self.eat()
            e = ("star", e)
        return e

    def parse_atom(self) -> tuple:
        tk, tv = self.peek()
        if tk == "num":
            self.eat()
            if tv == 0:
                return ("zero",)
            if tv == 1:
                return ("one",)
            raise TranslateError(f"Standalone number {tv} is not a NetKAT expression")
        if self.at("sym", "("):
            self.eat()
            e = self.parse_expr()
            self.eat("sym", ")")
            return e
        if tk == "id":
            ident = str(self.eat())
            if ident == "T":
                return ("top",)
            if ident == "dup":
                return ("dup",)
            if ident == "if":
                cond = self.parse_expr()
                self.eat("id", "then")
                t_branch = self.parse_expr()
                self.eat("id", "else")
                e_branch = self.parse_expr()
                return ("plus", ("seq", cond, t_branch), ("seq", ("not", cond), e_branch))
            # Bit-range x[a..b]
            if ident == "x" and self.at("sym", "["):
                self.eat("sym", "[")
                start = int(self.eat("num"))
                self.eat("sym", "..")
                end = int(self.eat("num"))
                self.eat("sym", "]")
                op = str(self.eat("sym"))
                val = int(self.eat("num"))
                if end <= start:
                    raise TranslateError(f"Empty/invalid bit range x[{start}..{end}]")
                if val < 0 or val >= (1 << (end - start)):
                    raise TranslateError(f"Value {val} out of range for x[{start}..{end}]")
                if op in ("~", "=", "=="):
                    return ("rtest", start, end, val)
                if op == ":=":
                    return ("rassign", start, end, val)
                raise TranslateError(f"Unexpected operator {op!r} after x[{start}..{end}]")
            # Single bit x0, x1, ...
            if len(ident) >= 2 and ident[0] == "x" and ident[1:].isdigit():
                bit = int(ident[1:])
                # Check if followed by test/assign operator
                if self.peek()[0] == "sym" and self.peek()[1] in ("~", "=", "==", ":="):
                    op = str(self.eat("sym"))
                    val = int(self.eat("num"))
                    if val not in (0, 1):
                        raise TranslateError(f"Bit {ident} value must be 0 or 1, got {val}")
                    if op in ("~", "=", "=="):
                        return ("rtest", bit, bit + 1, val)
                    return ("rassign", bit, bit + 1, val)
            if ident in self.hole_set:
                return ("hole", ident)
            if ident in self.defs:
                return self.defs[ident]
            raise TranslateError(f"Unknown identifier: {ident!r}")
        raise TranslateError(f"Unexpected token ({tk}, {tv!r}) in expression")


def infer_comment_field_names(source: str) -> dict[tuple[int, int], str]:
    """Extract optional human-readable field names from `//` comments, e.g. `// sw = x[0..3]`."""
    mapping: dict[tuple[int, int], str] = {}
    for line in source.splitlines():
        if "//" not in line:
            continue
        comment = line.split("//", 1)[1]
        for m in re.finditer(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*x\[(\d+)\.\.(\d+)\]", comment):
            name, a, b = m.group(1), int(m.group(2)), int(m.group(3))
            mapping[(a, b)] = name
    return mapping


def collect_ranges(exprs: Iterable[tuple]) -> set[tuple[int, int]]:
    ranges: set[tuple[int, int]] = set()
    seen: set[int] = set()
    stack = list(exprs)
    while stack:
        e = stack.pop()
        eid = id(e)
        if eid in seen:
            continue
        seen.add(eid)
        tag = e[0]
        if tag in ("rtest", "rassign"):
            ranges.add((e[1], e[2]))
        elif tag == "not" or tag == "star":
            stack.append(e[1])
        elif tag in ("plus", "seq"):
            stack.append(e[1])
            stack.append(e[2])
    return ranges


def build_fields(source: str, exprs: Iterable[tuple]) -> list[FieldInfo]:
    ranges = collect_ranges(exprs)
    if not ranges:
        return [FieldInfo(0, "f0", 0, 1)]
    cuts = sorted({pt for a, b in ranges for pt in (a, b)})
    hint_names = infer_comment_field_names(source)
    # Detect Topology Zoo standard 4-field layout `(loc, dst, port, dir)` when 4 ranges end with 1-bit dir
    intervals = [(cuts[i], cuts[i + 1]) for i in range(len(cuts) - 1)]
    if (
        not hint_names
        and len(intervals) == 4
        and intervals[0][1] - intervals[0][0] == intervals[1][1] - intervals[1][0]
        and intervals[3][1] - intervals[3][0] == 1
        and "LINK:" in source
    ):
        topo_names = ["loc", "dst", "port", "dir"]
        return [
            FieldInfo(idx, topo_names[idx], a, b)
            for idx, (a, b) in enumerate(intervals)
        ]
    fields: list[FieldInfo] = []
    used_names: set[str] = set()
    for idx, (a, b) in enumerate(intervals):
        name = hint_names.get((a, b))
        if not name or name in used_names:
            name = f"x{a}" if b == a + 1 else f"f{a}_{b}"
        used_names.add(name)
        fields.append(FieldInfo(idx, name, a, b))
    return fields


def lower_ranges_to_fields(expr: tuple, fields: list[FieldInfo]) -> tuple:
    """Rewrite `rtest`/`rassign` into elementary `test`/`assign` on `FieldInfo` indices."""
    memo: dict[int, tuple] = {}

    def decompose(start: int, end: int, val: int, kind: str) -> tuple:
        # Little-endian bit slice decomposition matching KATch2's `x[start..end]`
        sub = [f for f in fields if start <= f.start and f.end <= end]
        if not sub or sub[0].start != start or sub[-1].end != end:
            raise TranslateError(f"Range [{start}..{end}) does not align with field partition")
        atoms: list[tuple] = []
        for f in sub:
            shift = f.start - start
            mask = (1 << f.width) - 1
            sub_val = (val >> shift) & mask
            atoms.append((kind, f.idx, sub_val))
        res = atoms[0]
        for a in atoms[1:]:
            res = ("seq", res, a)
        return res

    # Iterative post-order traversal with explicit stack to handle huge ASTs
    stack: list[tuple[tuple, bool]] = [(expr, False)]
    while stack:
        node, visited = stack.pop()
        nid = id(node)
        if nid in memo:
            continue
        tag = node[0]
        if tag in ("zero", "one", "top", "dup", "hole", "test", "neq", "assign"):
            memo[nid] = node
        elif tag == "rtest":
            memo[nid] = decompose(node[1], node[2], node[3], "test")
        elif tag == "rassign":
            memo[nid] = decompose(node[1], node[2], node[3], "assign")
        elif tag in ("not", "star"):
            if not visited:
                stack.append((node, True))
                stack.append((node[1], False))
            else:
                c = memo[id(node[1])]
                if tag == "not" and c[0] == "test":
                    memo[nid] = ("neq", c[1], c[2])
                else:
                    memo[nid] = (tag, c)
        elif tag in ("plus", "seq"):
            if not visited:
                stack.append((node, True))
                stack.append((node[2], False))
                stack.append((node[1], False))
            else:
                memo[nid] = (tag, memo[id(node[1])], memo[id(node[2])])
        else:
            raise TranslateError(f"Unknown AST tag: {tag}")
    return memo[id(expr)]


# =============================================================================
# AST predicates & `dup` decomposition (for dup-free hole synthesis)
# =============================================================================


def erase_dup(expr: tuple) -> tuple:
    memo: dict[int, tuple] = {}
    stack: list[tuple[tuple, bool]] = [(expr, False)]
    while stack:
        node, visited = stack.pop()
        nid = id(node)
        if nid in memo:
            continue
        tag = node[0]
        if tag == "dup":
            memo[nid] = ("one",)
        elif tag in ("zero", "one", "top", "hole", "test", "neq", "assign"):
            memo[nid] = node
        elif tag in ("not", "star"):
            if not visited:
                stack.append((node, True))
                stack.append((node[1], False))
            else:
                memo[nid] = (tag, memo[id(node[1])])
        elif tag in ("plus", "seq"):
            if not visited:
                stack.append((node, True))
                stack.append((node[2], False))
                stack.append((node[1], False))
            else:
                memo[nid] = (tag, memo[id(node[1])], memo[id(node[2])])
    return memo[id(expr)]


def has_dup(expr: tuple) -> bool:
    seen: set[int] = set()
    stack = [expr]
    while stack:
        e = stack.pop()
        eid = id(e)
        if eid in seen:
            continue
        seen.add(eid)
        if e[0] == "dup":
            return True
        if e[0] in ("not", "star"):
            stack.append(e[1])
        elif e[0] in ("plus", "seq"):
            stack.append(e[1])
            stack.append(e[2])
    return False


def split_top_level_dups(expr: tuple) -> list[tuple] | None:
    """If `expr` is a top-level sequence `e0 ; dup ; e1 ; ... ; dup ; ek` with dup-free `ei`,
    return `[e0, e1, ..., ek]`. Otherwise return `None`."""
    # Flatten top-level `seq`
    factors: list[tuple] = []
    stack = [expr]
    while stack:
        e = stack.pop()
        if e[0] == "seq":
            stack.append(e[2])
            stack.append(e[1])
        else:
            factors.append(e)

    segments: list[list[tuple]] = [[]]
    for f in factors:
        if f[0] == "dup":
            segments.append([])
        else:
            if has_dup(f):
                return None
            segments[-1].append(f)

    out: list[tuple] = []
    for seg in segments:
        if not seg:
            out.append(("one",))
        else:
            cur = seg[0]
            for item in seg[1:]:
                cur = ("seq", cur, item)
            out.append(cur)
    return out


def is_pure_test(expr: tuple) -> bool:
    stack = [expr]
    seen: set[int] = set()
    while stack:
        node = stack.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        tag = node[0]
        if tag in ("plus", "seq"):
            stack.extend((node[1], node[2]))
        elif tag == "not":
            stack.append(node[1])
        elif tag not in ("zero", "one", "test", "neq"):
            return False
    return True


def is_hole_and_star_free(expr: tuple) -> bool:
    seen: set[int] = set()
    stack = [expr]
    while stack:
        e = stack.pop()
        eid = id(e)
        if eid in seen:
            continue
        seen.add(eid)
        t = e[0]
        if t in ("hole", "star", "dup"):
            return False
        if t == "not":
            stack.append(e[1])
        elif t in ("plus", "seq"):
            stack.append(e[1])
            stack.append(e[2])
    return True


@dataclass
class ChainConstraint:
    """Inclusion `(L_0 ; dup ; ... ; L_{k-1}) <= (R_0 ; dup ; ... ; R_{k-1})` over dup-free segments.
    For standard dup-free `lhs <= rhs`, `lhs_segs = [lhs]` and `rhs_segs = [rhs]` (`k = 1`)."""

    lhs_segs: list[tuple]
    rhs_segs: list[tuple]
    note: str = ""


@dataclass
class SynthesisProblem:
    fields: list[FieldInfo]
    holes: list[str]
    constraints: list[ChainConstraint]


def parse_nksynth_problem(source: str, erase_all_dups: bool = False) -> SynthesisProblem:
    parser = NkSynthParser(tokenize_nksynth(source))
    parser.parse_program()
    raw_exprs = [lhs for _, lhs, _ in parser.asserts] + [rhs for _, _, rhs in parser.asserts]
    fields = build_fields(source, raw_exprs)

    inclusions: list[tuple[tuple, tuple, str]] = []
    for idx, (op, raw_l, raw_r) in enumerate(parser.asserts, 1):
        l = lower_ranges_to_fields(raw_l, fields)
        r = lower_ranges_to_fields(raw_r, fields)
        if op == "<=":
            inclusions.append((l, r, f"assert#{idx}"))
        else:
            inclusions.append((l, r, f"assert#{idx}_leq"))
            inclusions.append((r, l, f"assert#{idx}_geq"))

    constraints: list[ChainConstraint] = []
    for l, r, tag in inclusions:
        if l == ("zero",) or r == ("top",):
            continue
        if erase_all_dups:
            constraints.append(ChainConstraint([erase_dup(l)], [erase_dup(r)], tag))
            continue
        if r == ("zero",):
            # Trace emptiness `L <= 0` for dup-free holes is exact under dup erasure
            constraints.append(ChainConstraint([erase_dup(l)], [("zero",)], tag))
            continue
        if not has_dup(l) and not has_dup(r):
            constraints.append(ChainConstraint([l], [r], tag))
            continue
        l_segs = split_top_level_dups(l)
        r_segs = split_top_level_dups(r)
        if l_segs is not None and r_segs is not None and len(l_segs) == len(r_segs):
            constraints.append(ChainConstraint(l_segs, r_segs, tag))
        else:
            raise TranslateError(
                f"Unsupported `dup` shape in {tag} (use --erase-dup for dup-free projection)"
            )

    return SynthesisProblem(fields=fields, holes=parser.holes, constraints=constraints)


# =============================================================================
# 1. pfwCSP Formula / Clause Intermediate Representation (IR)
# =============================================================================

# Terms in SMT-LIB LIA are `int` constants or `str` variable names.
Term = int | str


@dataclass(frozen=True)
class BoolLit:
    val: bool


@dataclass(frozen=True)
class Cmp:
    op: str  # '=', '!=', '<=', '<', '>=', '>'
    lhs: Term
    rhs: Term


@dataclass(frozen=True)
class Not:
    sub: "Fml"


@dataclass(frozen=True)
class And:
    items: tuple["Fml", ...]


@dataclass(frozen=True)
class Or:
    items: tuple["Fml", ...]


@dataclass(frozen=True)
class Exists:
    vars: tuple[str, ...]
    body: "Fml"


@dataclass(frozen=True)
class PredApp:
    name: str
    args: tuple[Term, ...]


Fml = BoolLit | Cmp | Not | And | Or | Exists | PredApp

TRUE = BoolLit(True)
FALSE = BoolLit(False)


def mk_eq(a: Term, b: Term) -> Fml:
    if a == b:
        return TRUE
    if isinstance(a, int) and isinstance(b, int):
        return FALSE
    return Cmp("=", a, b)


def mk_neq(a: Term, b: Term) -> Fml:
    if a == b:
        return FALSE
    if isinstance(a, int) and isinstance(b, int):
        return TRUE
    return Cmp("!=", a, b)


def mk_cmp(op: str, a: Term, b: Term) -> Fml:
    if op == "=":
        return mk_eq(a, b)
    if op == "!=":
        return mk_neq(a, b)
    if isinstance(a, int) and isinstance(b, int):
        res = {
            "<=": a <= b,
            "<": a < b,
            ">=": a >= b,
            ">": a > b,
        }[op]
        return BoolLit(res)
    return Cmp(op, a, b)


def mk_not(f: Fml) -> Fml:
    if isinstance(f, BoolLit):
        return BoolLit(not f.val)
    if isinstance(f, Not):
        return f.sub
    if isinstance(f, Cmp):
        flip = {"=": "!=", "!=": "=", "<=": ">", "<": ">=", ">=": "<", ">": "<="}[f.op]
        return mk_cmp(flip, f.lhs, f.rhs)
    if isinstance(f, And):
        return mk_or(*(mk_not(x) for x in f.items))
    if isinstance(f, Or):
        return mk_and(*(mk_not(x) for x in f.items))
    return Not(f)


def mk_and(*parts: Fml) -> Fml:
    flat: list[Fml] = []
    seen: set[Fml] = set()
    eq_const: dict[str, int] = {}
    neq_consts: dict[str, set[int]] = defaultdict(set)
    lo_bound: dict[str, int] = {}
    hi_bound: dict[str, int] = {}

    for p in parts:
        if p == FALSE:
            return FALSE
        if p == TRUE:
            continue
        items = p.items if isinstance(p, And) else (p,)
        for it in items:
            if it == FALSE:
                return FALSE
            if it == TRUE or it in seen:
                continue
            if isinstance(it, Cmp):
                v_var: str | None = None
                c_val: int | None = None
                op = it.op
                if isinstance(it.lhs, str) and isinstance(it.rhs, int):
                    v_var, c_val = it.lhs, it.rhs
                elif isinstance(it.rhs, str) and isinstance(it.lhs, int):
                    v_var, c_val = it.rhs, it.lhs
                    op = {"=": "=", "!=": "!=", "<=": ">=", "<": ">", ">=": "<=", ">": "<"}[op]
                if v_var is not None and c_val is not None:
                    if op == "=":
                        if v_var in eq_const and eq_const[v_var] != c_val:
                            return FALSE
                        if c_val in neq_consts[v_var]:
                            return FALSE
                        if v_var in lo_bound and c_val < lo_bound[v_var]:
                            return FALSE
                        if v_var in hi_bound and c_val > hi_bound[v_var]:
                            return FALSE
                        eq_const[v_var] = c_val
                    elif op == "!=":
                        if eq_const.get(v_var) == c_val:
                            return FALSE
                        neq_consts[v_var].add(c_val)
                    elif op in (">=", ">"):
                        lb = c_val if op == ">=" else c_val + 1
                        if v_var in eq_const and eq_const[v_var] < lb:
                            return FALSE
                        lo_bound[v_var] = max(lo_bound.get(v_var, lb), lb)
                        if v_var in hi_bound and lo_bound[v_var] > hi_bound[v_var]:
                            return FALSE
                    elif op in ("<=", "<"):
                        hb = c_val if op == "<=" else c_val - 1
                        if v_var in eq_const and eq_const[v_var] > hb:
                            return FALSE
                        hi_bound[v_var] = min(hi_bound.get(v_var, hb), hb)
                        if v_var in lo_bound and lo_bound[v_var] > hi_bound[v_var]:
                            return FALSE
            seen.add(it)
            flat.append(it)

    # Drop redundant bounds/inequalities already implied by `v = const`
    if eq_const:
        pruned: list[Fml] = []
        for it in flat:
            if isinstance(it, Cmp) and it.op != "=":
                sub = subst_fml(it, eq_const)
                if sub == TRUE:
                    continue
                if sub == FALSE:
                    return FALSE
            pruned.append(it)
        flat = pruned

    if not flat:
        return TRUE
    if len(flat) == 1:
        return flat[0]
    return And(tuple(flat))


def mk_or(*parts: Fml) -> Fml:
    flat: list[Fml] = []
    seen: set[Fml] = set()
    for p in parts:
        if p == TRUE:
            return TRUE
        if p == FALSE:
            continue
        items = p.items if isinstance(p, Or) else (p,)
        for it in items:
            if it == TRUE:
                return TRUE
            if it != FALSE and it not in seen:
                seen.add(it)
                flat.append(it)
    if not flat:
        return FALSE
    if len(flat) == 1:
        return flat[0]
    return Or(tuple(flat))


def mk_exists(vars_seq: Iterable[str], body: Fml) -> Fml:
    vs = tuple(dict.fromkeys(vars_seq))
    if not vs or body in (TRUE, FALSE):
        return body
    if isinstance(body, Exists):
        vs = tuple(dict.fromkeys(vs + body.vars))
        body = body.body
    free = free_vars(body)
    kept = tuple(v for v in vs if v in free)
    if not kept:
        return body
    return Exists(kept, body)


def free_vars(f: Fml) -> set[str]:
    if isinstance(f, BoolLit):
        return set()
    if isinstance(f, Cmp):
        out: set[str] = set()
        if isinstance(f.lhs, str):
            out.add(f.lhs)
        if isinstance(f.rhs, str):
            out.add(f.rhs)
        return out
    if isinstance(f, Not):
        return free_vars(f.sub)
    if isinstance(f, (And, Or)):
        out = set()
        for it in f.items:
            out |= free_vars(it)
        return out
    if isinstance(f, Exists):
        return free_vars(f.body) - set(f.vars)
    if isinstance(f, PredApp):
        return {a for a in f.args if isinstance(a, str)}
    raise TypeError(f)


def subst_fml(f: Fml, env: dict[str, Term]) -> Fml:
    if not env:
        return f
    if isinstance(f, BoolLit):
        return f
    if isinstance(f, Cmp):
        l = env.get(f.lhs, f.lhs) if isinstance(f.lhs, str) else f.lhs
        r = env.get(f.rhs, f.rhs) if isinstance(f.rhs, str) else f.rhs
        return mk_cmp(f.op, l, r)
    if isinstance(f, Not):
        return mk_not(subst_fml(f.sub, env))
    if isinstance(f, (And, Or)):
        conjunction = isinstance(f, And)
        absorbing = FALSE if conjunction else TRUE
        parts = []
        for item in f.items:
            result = subst_fml(item, env)
            if result == absorbing:
                return absorbing
            parts.append(result)
        return mk_and(*parts) if conjunction else mk_or(*parts)
    if isinstance(f, Exists):
        sub_env = {k: v for k, v in env.items() if k not in f.vars}
        # Avoid variable capture if any replacement references a bound var
        used_in_rhs = {v for v in sub_env.values() if isinstance(v, str)}
        renaming: dict[str, str] = {}
        new_vars: list[str] = []
        for bv in f.vars:
            if bv in used_in_rhs:
                nbv = f"{bv}_r"
                while nbv in used_in_rhs or nbv in env:
                    nbv += "_"
                renaming[bv] = nbv
                new_vars.append(nbv)
            else:
                new_vars.append(bv)
        body = subst_fml(f.body, renaming) if renaming else f.body
        return mk_exists(new_vars, subst_fml(body, sub_env))
    if isinstance(f, PredApp):
        return PredApp(f.name, tuple(env.get(a, a) if isinstance(a, str) else a for a in f.args))
    raise TypeError(f)


def has_pred_app(f: Fml) -> bool:
    if isinstance(f, PredApp):
        return True
    if isinstance(f, Not):
        return has_pred_app(f.sub)
    if isinstance(f, (And, Or)):
        return any(has_pred_app(x) for x in f.items)
    if isinstance(f, Exists):
        return has_pred_app(f.body)
    return False


def pred_names_in(f: Fml) -> set[str]:
    if isinstance(f, PredApp):
        return {f.name}
    if isinstance(f, Not):
        return pred_names_in(f.sub)
    if isinstance(f, (And, Or)):
        out: set[str] = set()
        for x in f.items:
            out |= pred_names_in(x)
        return out
    if isinstance(f, Exists):
        return pred_names_in(f.body)
    return set()


@dataclass
class UnknownDecl:
    name: str
    arity: int
    is_wfp: bool = False
    comment: str = ""


@dataclass
class Clause:
    forall_vars: tuple[str, ...]
    body: Fml
    head: Fml
    tag: str = ""


@dataclass
class HoleArityMap:
    """Metadata recording how an original hole `H(p, p')` was reduced to `H(args)`."""

    hole_name: str
    in_fixed: dict[int, int]
    out_fixed: dict[int, int]
    preserved: set[int]
    read_fields: tuple[int, ...]
    write_fields: tuple[int, ...]


@dataclass
class PfwCSP:
    fields: list[FieldInfo]
    holes: list[str]
    unknowns: dict[str, UnknownDecl] = field(default_factory=dict)
    clauses: list[Clause] = field(default_factory=list)
    # Structural side-tables kept so optimization passes can inspect star bodies & hole shapes
    left_stars: dict[str, tuple] = field(default_factory=dict)  # St_name -> star body AST
    right_stars: dict[str, tuple[str, tuple]] = field(default_factory=dict)  # D_name -> (W_name, star body AST)
    hole_maps: dict[str, HoleArityMap] = field(default_factory=dict)


# =============================================================================
# 2. Symbolic Guarded-Assignment Normal Form (SPP-NF) for Pass 1 (`subst_seq`)
# =============================================================================

# Effect on field `f`:
#   ('keep',)       -> output field equals input field `p.f`
#   ('const', c)    -> output field equals integer constant `c`
#   ('any',)        -> output field is unconstrained (`T`)
Effect = tuple

# Guard on field `f`: `frozenset[int]` of allowed values in `0..max_val`!
# Representing field guards over finite NetKAT bit-domains as bitmasks (Python ints!)
# makes conjunction (`&`), disjunction (`|`), negation, emptiness (`== 0`), and
# tautology (`== full_mask`) O(1) exact bit operations, AND automatically simplifies
# `(pt=0 + ... + pt=7)` to `full_mask` (unconstrained)!


@dataclass(frozen=True)
class SppBranch:
    """A conjunctive guard `∏_f (p.f ∈ mask[f])` paired with per-field output effects:
    `out_mask[f]` is either:
      - `None`: output `p'.f` equals input `p.f` (`keep`), or
      - `int` bitmask (non-zero): output `p'.f` can be any value in `out_mask[f]`
        (singleton `1 << c` means deterministic assignment `p'.f := c`;
         `full_mask` means arbitrary value in `0..2^w-1`)."""

    in_masks: tuple[int, ...]
    out_masks: tuple[int | None, ...]


class SppCompiler:
    """Compile any hole-free, star-free NetKAT expression into a compact list of `SppBranch`es."""

    def __init__(self, fields: list[FieldInfo]):
        self.fields = fields
        self.m = len(fields)
        self.full_masks = tuple((1 << f.width) - 1 for f in fields)
        # Note: a `w`-bit field has values `0 .. 2^w - 1`, i.e., `2^w` distinct values!
        self.all_vals_masks = tuple((1 << (1 << f.width)) - 1 for f in fields)
        self.id_branch = SppBranch(self.all_vals_masks, (None,) * self.m)
        self.top_branch = SppBranch(self.all_vals_masks, self.all_vals_masks)
        self._memo: dict[int, list[SppBranch]] = {}

    def compile(self, expr: tuple) -> list[SppBranch]:
        eid = id(expr)
        if eid in self._memo:
            return self._memo[eid]

        stack: list[tuple[tuple, bool]] = [(expr, False)]
        node_leaves_cache: dict[int, list[tuple]] = {}
        while stack:
            node, vis = stack.pop()
            nid = id(node)
            if nid in self._memo:
                continue
            t = node[0]
            if t == "zero":
                self._memo[nid] = []
            elif t == "one":
                self._memo[nid] = [self.id_branch]
            elif t == "top":
                self._memo[nid] = [self.top_branch]
            elif t == "test":
                f_idx, val = node[1], node[2]
                in_m = list(self.all_vals_masks)
                in_m[f_idx] = 1 << val
                self._memo[nid] = [SppBranch(tuple(in_m), (None,) * self.m)]
            elif t == "neq":
                f_idx, val = node[1], node[2]
                in_m = list(self.all_vals_masks)
                in_m[f_idx] &= ~(1 << val)
                self._memo[nid] = (
                    [SppBranch(tuple(in_m), (None,) * self.m)] if in_m[f_idx] else []
                )
            elif t == "assign":
                f_idx, val = node[1], node[2]
                out_m: list[int | None] = [None] * self.m
                out_m[f_idx] = 1 << val
                self._memo[nid] = [SppBranch(self.all_vals_masks, tuple(out_m))]
            elif t == "not":
                if not vis:
                    stack.append((node, True))
                    stack.append((node[1], False))
                else:
                    self._memo[nid] = self._negate_test(self._memo[id(node[1])])
            elif t == "plus":
                # Flatten nested `plus` trees so `_compact` runs ONCE on the whole union
                # (crucial on 200-node Topology Zoo policies with ~40,000 rules!).
                if not vis:
                    leaves: list[tuple] = []
                    p_stack = [node]
                    while p_stack:
                        cur_p = p_stack.pop()
                        if cur_p[0] == "plus" and id(cur_p) not in self._memo:
                            p_stack.append(cur_p[2])
                            p_stack.append(cur_p[1])
                        else:
                            leaves.append(cur_p)
                    node_leaves_cache[nid] = leaves
                    stack.append((node, True))
                    for lf in reversed(leaves):
                        if id(lf) not in self._memo:
                            stack.append((lf, False))
                else:
                    combined: list[SppBranch] = []
                    for lf in node_leaves_cache[nid]:
                        combined.extend(self._memo[id(lf)])
                    self._memo[nid] = self._compact(combined)
            elif t == "seq":
                if not vis:
                    stack.append((node, True))
                    stack.append((node[2], False))
                    stack.append((node[1], False))
                else:
                    self._memo[nid] = self._seq(
                        self._memo[id(node[1])], self._memo[id(node[2])]
                    )
            else:
                raise TranslateError(f"SppCompiler cannot compile non-SPP construct: {t}")
        return self._memo[eid]

    def _negate_test(self, branches: list[SppBranch]) -> list[SppBranch]:
        # Start from full cube `[all_vals_masks]` and subtract each test cube
        cubes: list[tuple[int, ...]] = [self.all_vals_masks]
        for br in branches:
            next_cubes: list[tuple[int, ...]] = []
            for c in cubes:
                # If `c` and `br.in_masks` are disjoint on some field, `c` is untouched
                if any((c[i] & br.in_masks[i]) == 0 for i in range(self.m)):
                    next_cubes.append(c)
                    continue
                # Split `c \ br`: for each i, keep `c[i] & ~br[i]` and intersect earlier coords with `br`
                prefix = list(c)
                for i in range(self.m):
                    diff = prefix[i] & ~br.in_masks[i]
                    if diff:
                        piece = list(prefix)
                        piece[i] = diff
                        next_cubes.append(tuple(piece))
                    prefix[i] &= br.in_masks[i]
                    if not prefix[i]:
                        break
            cubes = next_cubes
        return self._compact([SppBranch(c, (None,) * self.m) for c in cubes])

    def _seq(self, b1: list[SppBranch], b2: list[SppBranch]) -> list[SppBranch]:
        if not b1 or not b2:
            return []
        # Fast hash-join when there is a field constantly assigned by all of b1 and tested to singletons in b2,
        # or generally index b2 by fields where b2 tests a single value:
        out: list[SppBranch] = []
        # Group b2 by singleton-tested fields if b2 is large
        if len(b1) * len(b2) > 256:
            # Pick field with highest singleton selectivity in b2
            best_f = -1
            best_distinct = 1
            for f_idx in range(self.m):
                vals = {br.in_masks[f_idx] for br in b2}
                if len(vals) > best_distinct and all((v & (v - 1)) == 0 for v in vals):
                    best_distinct = len(vals)
                    best_f = f_idx
            if best_f >= 0:
                by_val: dict[int, list[SppBranch]] = defaultdict(list)
                for br2 in b2:
                    by_val[br2.in_masks[best_f]].append(br2)
                for br1 in b1:
                    om1 = br1.out_masks[best_f]
                    possible = om1 if om1 is not None else br1.in_masks[best_f]
                    for val_bit, group in by_val.items():
                        if possible & val_bit:
                            for br2 in group:
                                comp = self._compose_one(br1, br2)
                                if comp is not None:
                                    out.append(comp)
                return self._compact(out)

        for br1 in b1:
            for br2 in b2:
                comp = self._compose_one(br1, br2)
                if comp is not None:
                    out.append(comp)
        return self._compact(out)

    def _compose_one(self, br1: SppBranch, br2: SppBranch) -> SppBranch | None:
        in_m = list(br1.in_masks)
        out_m = list(br1.out_masks)
        for i in range(self.m):
            m2 = br2.in_masks[i]
            om1 = br1.out_masks[i]
            if om1 is None:
                # Field `i` passed through from input: restrict input guard, and if `m2` is singleton,
                # keep `None` (since `p.i` is already constrained to that singleton!).
                inter = in_m[i] & m2
                if not inter:
                    return None
                in_m[i] = inter
                if br2.out_masks[i] is not None:
                    out_m[i] = br2.out_masks[i]
            else:
                # `br1` wrote a value from `om1`; `br2` requires it to lie in `m2`
                inter = om1 & m2
                if not inter:
                    return None
                out_m[i] = br2.out_masks[i] if br2.out_masks[i] is not None else inter
        return SppBranch(tuple(in_m), tuple(out_m))

    def _compact(self, branches: list[SppBranch]) -> list[SppBranch]:
        if len(branches) <= 1:
            return branches
        # Normalize singleton input + identical singleton output to `None` (`keep`) so branches merge cleanly!
        normed: list[SppBranch] = []
        for br in branches:
            om = list(br.out_masks)
            changed = False
            for i in range(self.m):
                im = br.in_masks[i]
                if om[i] is not None and (im & (im - 1)) == 0 and om[i] == im:
                    # Wait: keeping explicit singleton assignment `loc:=2` vs `keep` when `loc=2`:
                    # both denote the exact same `(p, p')` relation (`p.i = c /\ p'.i = c`)!
                    om[i] = None
                    changed = True
            normed.append(SppBranch(br.in_masks, tuple(om)) if changed else br)

        # Merge branches that differ in AT MOST ONE coordinate (either one `in_masks[k]` or one `out_masks[k]`)!
        # Repeat until fixpoint so e.g. `(pt:=0 + ... + pt:=7)` collapses to a single `out_masks[pt] = full`!
        cur = list(dict.fromkeys(normed))
        while True:
            merged_any = False
            # 1) Merge identical `in_masks` that differ in only one `out_masks` position (where neither is None)
            by_in: dict[tuple[int, ...], list[tuple[int | None, ...]]] = defaultdict(list)
            for br in cur:
                by_in[br.in_masks].append(br.out_masks)
            nxt: list[SppBranch] = []
            for im, oms in by_in.items():
                if len(oms) > 1:
                    for k in range(self.m):
                        buckets: dict[tuple, int] = defaultdict(int)
                        passthrough: list[tuple[int | None, ...]] = []
                        for om in oms:
                            if om[k] is None:
                                passthrough.append(om)
                            else:
                                key = om[:k] + om[k + 1 :]
                                buckets[key] |= om[k]
                        rebuilt = list(passthrough)
                        for key, mask in buckets.items():
                            rebuilt.append(key[:k] + (mask,) + key[k:])
                        if len(rebuilt) < len(oms):
                            oms = rebuilt
                            merged_any = True
                for om in oms:
                    nxt.append(SppBranch(im, om))

            # 2) Merge identical `out_masks` that differ in only one `in_masks` position
            by_out: dict[tuple[int | None, ...], list[tuple[int, ...]]] = defaultdict(list)
            for br in nxt:
                by_out[br.out_masks].append(br.in_masks)
            nxt2: list[SppBranch] = []
            for om, ims in by_out.items():
                if len(ims) > 1:
                    for k in range(self.m):
                        buckets2: dict[tuple[int, ...], int] = defaultdict(int)
                        for im in ims:
                            key = im[:k] + im[k + 1 :]
                            buckets2[key] |= im[k]
                        if len(buckets2) < len(ims):
                            ims = [key[:k] + (mask,) + key[k:] for key, mask in buckets2.items()]
                            merged_any = True
                for im in ims:
                    nxt2.append(SppBranch(im, om))

            cur = nxt2
            if not merged_any:
                break
        return cur

    def mask_to_fml(self, var: Term, mask: int, f_idx: int, unbounded: bool = True) -> Fml:
        full = self.all_vals_masks[f_idx]
        if mask == 0:
            return FALSE
        if mask == full:
            if unbounded:
                return TRUE
            return mk_and(mk_cmp("<=", 0, var), mk_cmp("<=", var, self.fields[f_idx].max_val))
        # Always check singleton (`= c`) BEFORE complement (`!= c`) so 1-bit fields emit `= 0` / `= 1`!
        if (mask & (mask - 1)) == 0:
            return mk_eq(var, mask.bit_length() - 1)
        # Check if single excluded value (`!= c`) when unbounded (for fields of width >= 2)
        inv = full & ~mask
        if unbounded and (inv & (inv - 1)) == 0:
            excluded = inv.bit_length() - 1
            return mk_neq(var, excluded)
        # Decompose `mask` into contiguous integer intervals `[lo, hi]`
        vals = [v for v in range(self.fields[f_idx].max_val + 1) if (mask >> v) & 1]
        intervals: list[tuple[int, int]] = []
        for v in vals:
            if intervals and v == intervals[-1][1] + 1:
                intervals[-1] = (intervals[-1][0], v)
            else:
                intervals.append((v, v))
        disj: list[Fml] = []
        for lo, hi in intervals:
            if lo == hi:
                disj.append(mk_eq(var, lo))
            elif hi == lo + 1:
                disj.append(mk_or(mk_eq(var, lo), mk_eq(var, hi)))
            else:
                disj.append(mk_and(mk_cmp("<=", lo, var), mk_cmp("<=", var, hi)))
        return mk_or(*disj)

    def branch_to_fml(
        self, br: SppBranch, p_in: list[Term], p_out: list[Term], unbounded: bool = True
    ) -> Fml:
        parts: list[Fml] = []
        for i in range(self.m):
            parts.append(self.mask_to_fml(p_in[i], br.in_masks[i], i, unbounded=unbounded))
            om = br.out_masks[i]
            if om is None:
                parts.append(mk_eq(p_out[i], p_in[i]))
            else:
                # Note: if `om == all_vals_masks[i]` (e.g. `T` or `(pt:=0 + ... + pt:=7)`),
                # in unbounded mode `mask_to_fml` yields `TRUE` (unconstrained output field `pt2`),
                # matching `hospital_generic.smt2`!
                parts.append(self.mask_to_fml(p_out[i], om, i, unbounded=unbounded))
        return mk_and(*parts)

    def expr_to_fml(
        self, expr: tuple, p_in: list[Term], p_out: list[Term], unbounded: bool = True
    ) -> Fml:
        branches = self.compile(expr)
        return mk_or(*(self.branch_to_fml(br, p_in, p_out, unbounded=unbounded) for br in branches))

    def branch_is_deterministic(self, br: SppBranch) -> bool:
        return all(om is None or (om & (om - 1)) == 0 for om in br.out_masks)

    def apply_deterministic_branch(
        self, br: SppBranch, p_in: list[Term], unbounded: bool = True
    ) -> tuple[Fml, list[Term]]:
        guards: list[Fml] = []
        out_pkt: list[Term] = []
        for i in range(self.m):
            im = br.in_masks[i]
            guards.append(self.mask_to_fml(p_in[i], im, i, unbounded=unbounded))
            om = br.out_masks[i]
            if om is not None:
                assert (om & (om - 1)) == 0
                out_pkt.append(om.bit_length() - 1)
            elif (im & (im - 1)) == 0:
                out_pkt.append(im.bit_length() - 1)
            else:
                out_pkt.append(p_in[i])
        return mk_and(*guards), out_pkt


# =============================================================================
# 3. Stage 1 — Generic Translation (`T+` and `T-`) + Clause Normalization
# =============================================================================


class GenericTranslator:
    """Translates a `SynthesisProblem` to `PfwCSP` following Sections 3–4 of
    `NetKAT synthesis to pfwCSP: the generic translation`, with optional Pass 1 (`subst_seq`)."""

    def __init__(
        self,
        prob: SynthesisProblem,
        subst_seq: bool = True,
        unbounded: bool = True,
        share_left_stars: bool = True,
    ):
        self.prob = prob
        self.fields = prob.fields
        self.m = len(self.fields)
        self.subst_seq = subst_seq
        self.unbounded = unbounded
        self.share_left_stars = share_left_stars
        self.spp = SppCompiler(self.fields)
        self.csp = PfwCSP(fields=self.fields, holes=list(prob.holes))
        self._fresh_id = 0
        self._st_cache: dict[tuple, str] = {}
        self._d_count = 0
        self._st_count = 0

        for h in prob.holes:
            self.csp.unknowns[h] = UnknownDecl(h, 2 * self.m, is_wfp=False, comment="hole")

    def fresh_pkt(self, prefix: str = "q") -> list[str]:
        self._fresh_id += 1
        k = self._fresh_id
        return [f"{f.name}_{prefix}{k}" for f in self.fields]

    def named_pkt(self, suffix: str) -> list[str]:
        return [f"{f.name}{suffix}" for f in self.fields]

    def domain_guard(self, pkt: list[Term]) -> Fml:
        if self.unbounded:
            return TRUE
        return mk_and(
            *(
                mk_and(mk_cmp("<=", 0, pkt[i]), mk_cmp("<=", pkt[i], self.fields[i].max_val))
                for i in range(self.m)
            )
        )

    def translate_test(self, expr: tuple, pkt: list[Term], pos: bool = True) -> Fml:
        t = expr[0]
        if t == "zero":
            return FALSE if pos else TRUE
        if t == "one":
            return TRUE if pos else FALSE
        if t == "test":
            return mk_eq(pkt[expr[1]], expr[2]) if pos else mk_neq(pkt[expr[1]], expr[2])
        if t == "neq":
            return mk_neq(pkt[expr[1]], expr[2]) if pos else mk_eq(pkt[expr[1]], expr[2])
        if t == "not":
            return self.translate_test(expr[1], pkt, not pos)
        if t in ("plus", "seq"):
            a = self.translate_test(expr[1], pkt, pos)
            b = self.translate_test(expr[2], pkt, pos)
            is_conj = (t == "seq") == pos
            return mk_and(a, b) if is_conj else mk_or(a, b)
        raise TranslateError(f"Invalid test expression: {t}")

    def translate(self, expr: tuple, p_in: list[Term], p_out: list[Term], polarity: str) -> Fml:
        """`polarity` is `'+'` (left of `<=`, over-approx) or `'-'` (right of `<=`, under-approx)."""
        if self.subst_seq and is_hole_and_star_free(expr):
            return self.spp.expr_to_fml(expr, p_in, p_out, unbounded=self.unbounded)

        t = expr[0]
        if t == "zero":
            return FALSE
        if t == "one":
            return mk_and(*(mk_eq(p_out[i], p_in[i]) for i in range(self.m)))
        if t == "top":
            return self.domain_guard(p_out)
        if is_pure_test(expr):
            return mk_and(
                self.translate_test(expr, p_in, True),
                *(mk_eq(p_out[i], p_in[i]) for i in range(self.m)),
            )
        if t == "assign":
            f_idx, val = expr[1], expr[2]
            return mk_and(
                mk_eq(p_out[f_idx], val),
                *(mk_eq(p_out[i], p_in[i]) for i in range(self.m) if i != f_idx),
            )
        if t == "hole":
            return PredApp(expr[1], tuple(p_in) + tuple(p_out))
        if t == "plus":
            return mk_or(
                self.translate(expr[1], p_in, p_out, polarity),
                self.translate(expr[2], p_in, p_out, polarity),
            )
        if t == "seq":
            return self._translate_seq(expr[1], expr[2], p_in, p_out, polarity)
        if t == "star":
            if polarity == "+":
                st_name = self._ensure_left_star(expr[1])
                return PredApp(st_name, tuple(p_in) + tuple(p_out))
            else:
                d_name = self._ensure_right_star(expr[1])
                return PredApp(d_name, tuple(p_in) + tuple(p_out))
        raise TranslateError(f"Unsupported AST construct in translate: {t}")

    def _translate_seq(
        self, e1: tuple, e2: tuple, p_in: list[Term], p_out: list[Term], polarity: str
    ) -> Fml:
        if self.subst_seq:
            # Right-test shortcut: `e1 ; b` -> `T(e1)(p_in, p_out) /\ b(p_out)` (no intermediate packet!)
            if is_pure_test(e2):
                return mk_and(
                    self.translate(e1, p_in, p_out, polarity),
                    self.translate_test(e2, p_out, True),
                )
            # Left deterministic SPP shortcut: `e1 ; e2` -> substitute `e1`'s output directly into `e2`
            if is_hole_and_star_free(e1):
                branches = self.spp.compile(e1)
                if all(self.spp.branch_is_deterministic(br) for br in branches):
                    disj: list[Fml] = []
                    for br in branches:
                        g, mid_pkt = self.spp.apply_deterministic_branch(
                            br, p_in, unbounded=self.unbounded
                        )
                        disj.append(mk_and(g, self.translate(e2, mid_pkt, p_out, polarity)))
                    return mk_or(*disj)

        q = self.fresh_pkt("q")
        return mk_exists(
            q,
            mk_and(
                self.domain_guard(q),
                self.translate(e1, p_in, q, polarity),
                self.translate(e2, q, p_out, polarity),
            ),
        )

    def _ensure_left_star(self, body_expr: tuple) -> str:
        if self.share_left_stars and body_expr in self._st_cache:
            return self._st_cache[body_expr]
        self._st_count += 1
        st_name = "St" if self._st_count == 1 else f"St{self._st_count}"
        if self.share_left_stars:
            self._st_cache[body_expr] = st_name
        self.csp.unknowns[st_name] = UnknownDecl(
            st_name, 2 * self.m, is_wfp=False, comment="star on the LEFT of <= (over-approx.)"
        )
        self.csp.left_stars[st_name] = body_expr

        # (St-0)  1 <= St :  forall p. St(p, p)
        p = self.named_pkt("")
        self.csp.clauses.append(
            Clause(
                forall_vars=tuple(p),
                body=self.domain_guard(p),
                head=PredApp(st_name, tuple(p) + tuple(p)),
                tag=f"{st_name}-init",
            )
        )
        # (St-1)  St ; e <= St
        p_in = self.named_pkt("")
        r = self.named_pkt("_r")
        p_out = self.named_pkt("2")
        step_fml = self.translate(body_expr, r, p_out, "+")
        prem = mk_and(
            self.domain_guard(p_in),
            self.domain_guard(r),
            self.domain_guard(p_out),
            PredApp(st_name, tuple(p_in) + tuple(r)),
            step_fml,
        )
        for idx, cl in enumerate(
            normalize_implication(p_in + r + p_out, prem, PredApp(st_name, tuple(p_in) + tuple(p_out)), f"{st_name}-step")
        ):
            self.csp.clauses.append(cl)
        return st_name

    def _ensure_right_star(self, body_expr: tuple) -> str:
        self._d_count += 1
        d_name = "D" if self._d_count == 1 else f"D{self._d_count}"
        w_name = "W_" if self._d_count == 1 else f"W_{self._d_count}"
        self.csp.unknowns[d_name] = UnknownDecl(
            d_name, 2 * self.m, is_wfp=False, comment="star on the RIGHT of <= (under-approx.)"
        )
        self.csp.unknowns[w_name] = UnknownDecl(
            w_name, 4 * self.m, is_wfp=True, comment=f"well-founded progress for {d_name}"
        )
        self.csp.right_stars[d_name] = (w_name, body_expr)

        p_in = self.named_pkt("")
        p_out = self.named_pkt("2")
        r = self.named_pkt("_r")
        eq_fml = mk_and(*(mk_eq(p_out[i], p_in[i]) for i in range(self.m)))
        step_fml = self.translate(body_expr, p_in, r, "-")
        rec = mk_exists(
            r,
            mk_and(
                self.domain_guard(r),
                step_fml,
                PredApp(d_name, tuple(r) + tuple(p_out)),
                PredApp(w_name, tuple(p_in) + tuple(p_out) + tuple(r) + tuple(p_out)),
            ),
        )
        # Flatten nested `exists q` inside `step_fml` into a single `exists (q, r)` block
        rec = hoist_positive_exists(rec)
        self.csp.clauses.append(
            Clause(
                forall_vars=tuple(p_in + p_out),
                body=mk_and(
                    self.domain_guard(p_in),
                    self.domain_guard(p_out),
                    PredApp(d_name, tuple(p_in) + tuple(p_out)),
                ),
                head=mk_or(eq_fml, rec),
                tag=f"{d_name}-step",
            )
        )
        return d_name

    def run(self) -> PfwCSP:
        for c in self.prob.constraints:
            k = len(c.lhs_segs)
            if k == 1:
                pkts = [self.named_pkt(""), self.named_pkt("2")]
            else:
                pkts = [self.named_pkt(f"_s{j}") for j in range(k + 1)]
            all_vars = [v for pkt in pkts for v in pkt]
            lhs_conj = [self.domain_guard(pkt) for pkt in pkts]
            rhs_conj: list[Fml] = []
            for j in range(k):
                lhs_conj.append(self.translate(c.lhs_segs[j], pkts[j], pkts[j + 1], "+"))
                rhs_conj.append(self.translate(c.rhs_segs[j], pkts[j], pkts[j + 1], "-"))
            prem = mk_and(*lhs_conj)
            conc = mk_and(*rhs_conj)
            for cl in normalize_implication(all_vars, prem, conc, c.note):
                self.csp.clauses.append(cl)
        return self.csp


def hoist_positive_exists(f: Fml) -> Fml:
    """Pull `Exists` nested under `And` into a single outer `Exists`:
    `Exists(r, And(Exists(q, A), B))` -> `Exists(q + r, And(A, B))`."""
    if isinstance(f, Exists):
        sub = hoist_positive_exists(f.body)
        if isinstance(sub, Exists):
            return mk_exists(list(f.vars) + list(sub.vars), sub.body)
        return mk_exists(f.vars, sub)
    if isinstance(f, And):
        items = [hoist_positive_exists(x) for x in f.items]
        if not any(isinstance(x, Exists) for x in items):
            return mk_and(*items)
        extra_vars: list[str] = []
        conj: list[Fml] = []
        used = set().union(*(free_vars(x) for x in items))
        for it in items:
            if isinstance(it, Exists):
                ren: dict[str, str] = {}
                for bv in it.vars:
                    nbv = bv
                    while nbv in used:
                        nbv = f"{nbv}_"
                    if nbv != bv:
                        ren[bv] = nbv
                    used.add(nbv)
                    extra_vars.append(nbv)
                conj.append(subst_fml(it.body, ren) if ren else it.body)
            else:
                conj.append(it)
        return mk_exists(extra_vars, mk_and(*conj))
    if isinstance(f, Or):
        return mk_or(*(hoist_positive_exists(x) for x in f.items))
    return f


def lift_premise_exists(f: Fml, avoid: set[str]) -> tuple[list[str], Fml]:
    """Convert `Exists` in a clause premise (left of `=>`) into fresh universal variables."""
    if isinstance(f, Exists):
        ren: dict[str, str] = {}
        lifted: list[str] = []
        for bv in f.vars:
            nbv = bv
            while nbv in avoid:
                nbv = f"{nbv}_"
            ren[bv] = nbv
            avoid.add(nbv)
            lifted.append(nbv)
        sub = subst_fml(f.body, ren) if ren else f.body
        more, clean = lift_premise_exists(sub, avoid)
        return lifted + more, clean
    if isinstance(f, And):
        lifted = []
        parts = []
        for it in f.items:
            vs, clean = lift_premise_exists(it, avoid)
            lifted.extend(vs)
            parts.append(clean)
        return lifted, mk_and(*parts)
    if isinstance(f, Or):
        lifted = []
        parts = []
        for it in f.items:
            vs, clean = lift_premise_exists(it, avoid)
            lifted.extend(vs)
            parts.append(clean)
        return lifted, mk_or(*parts)
    return [], f


def split_premise_pred_or(prem: Fml) -> list[Fml]:
    r"""Split `(A \/ B)` in a premise ONLY when a disjunct contains an unknown `PredApp`
    (e.g. splitting `Pol0 \/ (sw=S /\ X)` into `(St-1)` and `(St-2)`, while keeping pure
    arithmetic disjunctions like `Link` compact!)."""
    if isinstance(prem, Or) and has_pred_app(prem):
        out: list[Fml] = []
        for it in prem.items:
            out.extend(split_premise_pred_or(it))
        return out
    if isinstance(prem, And):
        choices: list[list[Fml]] = [split_premise_pred_or(it) for it in prem.items]
        acc = [TRUE]
        for ch in choices:
            acc = [mk_and(a, b) for a in acc for b in ch]
        return [x for x in acc if x != FALSE]
    return [] if prem == FALSE else [prem]


def normalize_implication(
    base_vars: Iterable[str], prem: Fml, conc: Fml, tag: str
) -> list[Clause]:
    if prem == FALSE or conc == TRUE:
        return []
    avoid = set(base_vars) | free_vars(prem) | free_vars(conc)
    extra_vs, clean_prem = lift_premise_exists(prem, avoid)
    all_vs = list(dict.fromkeys(list(base_vars) + extra_vs))
    prem_branches = split_premise_pred_or(clean_prem)
    conc_conjuncts = list(conc.items) if isinstance(conc, And) else [conc]

    clauses: list[Clause] = []
    for p_br in prem_branches:
        for c_it in conc_conjuncts:
            if p_br == FALSE or c_it == TRUE:
                continue
            head = hoist_positive_exists(c_it)
            used = free_vars(p_br) | free_vars(head)
            fvars = tuple(v for v in all_vs if v in used)
            clauses.append(Clause(fvars, p_br, head, tag))
    return clauses


# =============================================================================
# 4. Stage 2 — Optimization Passes
# =============================================================================


def simplify_clause_equalities(cl: Clause) -> Clause:
    """Propagate `v = term` equalities in `cl.body` for universally quantified variables `v`
    when `v` is an intermediate variable (or `v = const` when `v` does not appear in `PredApp`s?
    Even better: substitute ANY universal variable `v` in `v = t` across `body` and `head`!)."""
    fvars = set(cl.forall_vars)
    body = cl.body
    head = cl.head

    # Propagate equalities `v = term` in `body` where `v in fvars` (prefer eliminating `_q`, `_r`, `_s` intermediates first)
    def var_priority(v: str) -> tuple[int, str]:
        is_mid = any(s in v for s in ("_q", "_r", "_s"))
        return (0 if is_mid else 1, v)

    while True:
        items = list(body.items) if isinstance(body, And) else [body]
        subst: tuple[str, Term] | None = None
        for it in items:
            if isinstance(it, Cmp) and it.op == "=":
                l, r = it.lhs, it.rhs
                if isinstance(l, str) and l in fvars and l != r:
                    if isinstance(r, str) and r in fvars and var_priority(r) < var_priority(l):
                        subst = (r, l)
                    else:
                        subst = (l, r)
                    break
                if isinstance(r, str) and r in fvars and l != r:
                    subst = (r, l)
                    break
        if subst is None:
            break
        var, rep = subst
        env = {var: rep}
        body = subst_fml(body, env)
        head = subst_fml(head, env)
        fvars.discard(var)

    head = simplify_exists_equalities(head)
    if body == FALSE or head == TRUE:
        return Clause((), FALSE, TRUE, cl.tag)
    # Check if every disjunct of `body` syntactically contains `head` (e.g. `(A /\ sw=1) \/ (B /\ sw=1) => sw=1`)
    body_disj = list(body.items) if isinstance(body, Or) else [body]
    if all(
        head in (set(bd.items) if isinstance(bd, And) else {bd})
        or (
            isinstance(head, Or)
            and any(
                h_it in (set(bd.items) if isinstance(bd, And) else {bd})
                for h_it in head.items
            )
        )
        for bd in body_disj
    ):
        return Clause((), FALSE, TRUE, cl.tag)
    used = free_vars(body) | free_vars(head)
    kept = tuple(v for v in cl.forall_vars if v in fvars and v in used)
    return Clause(kept, body, head, cl.tag)


def simplify_exists_equalities(f: Fml) -> Fml:
    """Inside `Exists(vars, And(...))`, eliminate any bound variable `v` constrained by `v = term`."""
    if isinstance(f, Or):
        return mk_or(*(simplify_exists_equalities(x) for x in f.items))
    if isinstance(f, And):
        return mk_and(*(simplify_exists_equalities(x) for x in f.items))
    if isinstance(f, Exists):
        f = hoist_positive_exists(f)
        if not isinstance(f, Exists):
            return simplify_exists_equalities(f)
        bvars = set(f.vars)
        body = simplify_exists_equalities(f.body)
        while True:
            items = list(body.items) if isinstance(body, And) else [body]
            subst: tuple[str, Term] | None = None
            for it in items:
                if isinstance(it, Cmp) and it.op == "=":
                    l, r = it.lhs, it.rhs
                    if isinstance(l, str) and l in bvars and l != r:
                        subst = (l, r)
                        break
                    if isinstance(r, str) and r in bvars and l != r:
                        subst = (r, l)
                        break
            if subst is None:
                break
            var, rep = subst
            body = subst_fml(body, {var: rep})
            bvars.discard(var)
        return mk_exists([v for v in f.vars if v in bvars], body)
    return f


# ---- Pass 2: Hole Shape, Frame & Contextual Dead-Output Inference ----


@dataclass
class HoleShapeInfo:
    hole: str
    in_masks: list[int]
    out_masks: list[int]  # union of allowed output values (`all_vals` if unconstrained)
    preserved: set[int]  # field indices `i` where `p_out[i] == p_in[i]` always holds
    exact_upper_clauses: list[int]  # indices of `X <= U` clauses fully captured by this shape


def find_contextual_successors(prob: SynthesisProblem, hole: str) -> list[tuple] | None:
    """If EVERY occurrence of `hole` across the entire problem is immediately followed in a `seq`
    by a hole-free, star-free expression `E` (e.g. `hop = h1 ; pol ; topo`), return the list of
    all such successor expressions `E`. If `hole` ever appears without such a successor (e.g. at
    the end of an assertion like `assert hS <= ...`, excluding pure `hole <= U` shape assertions),
    return `None`."""
    successors: list[tuple] = []

    def check_expr(expr: tuple, after: tuple | None) -> bool:
        t = expr[0]
        if t == "hole":
            if expr[1] != hole:
                return True
            if after is not None and is_hole_and_star_free(after):
                successors.append(after)
                return True
            return False
        if t in ("zero", "one", "top", "dup", "test", "neq", "assign"):
            return True
        if t == "not":
            return check_expr(expr[1], None)
        if t == "plus":
            return check_expr(expr[1], after) and check_expr(expr[2], after)
        if t == "seq":
            # In `(a ; b)` followed by `after`, `b` is followed by `after`, and `a` is followed by `b ; after`
            b_after = ("seq", expr[2], after) if after is not None else expr[2]
            return check_expr(expr[1], b_after) and check_expr(expr[2], after)
        if t == "star":
            # Inside `e*`, the end of `e` can either exit the star or repeat `e`, so no guaranteed `after` at tail
            return check_expr(expr[1], None)
        return False

    for c in prob.constraints:
        # Skip explicit `hole <= U` upper-bound assertions (they constrain `hole` itself)
        if (
            len(c.lhs_segs) == 1
            and c.lhs_segs[0] == ("hole", hole)
            and is_hole_and_star_free(c.rhs_segs[0])
        ):
            continue
        for seg in c.lhs_segs + c.rhs_segs:
            if not check_expr(seg, None):
                return None
    return successors if successors else None


def infer_hole_shapes(
    prob: SynthesisProblem,
    csp: PfwCSP,
    use_context: bool = True,
) -> dict[str, HoleShapeInfo]:
    spp = SppCompiler(prob.fields)
    m = len(prob.fields)
    shapes: dict[str, HoleShapeInfo] = {}

    for h in prob.holes:
        in_masks = list(spp.all_vals_masks)
        out_masks = list(spp.all_vals_masks)
        preserved: set[int] = set()
        captured_clauses: list[int] = []

        # 1. Explicit upper-bound constraints `h <= U` where `U` is hole-free and star-free
        for c in prob.constraints:
            if (
                len(c.lhs_segs) == 1
                and c.lhs_segs[0] == ("hole", h)
                and is_hole_and_star_free(c.rhs_segs[0])
            ):
                branches = spp.compile(c.rhs_segs[0])
                if not branches:
                    in_masks = [0] * m
                    out_masks = [0] * m
                    preserved = set(range(m))
                    break
                u_in = [0] * m
                u_out = [0] * m
                u_pres = set(range(m))
                for br in branches:
                    for i in range(m):
                        u_in[i] |= br.in_masks[i]
                        if br.out_masks[i] is None:
                            u_out[i] |= br.in_masks[i]
                        else:
                            u_out[i] |= br.out_masks[i]
                            # Check if singleton input == singleton output
                            if not (
                                (br.in_masks[i] & (br.in_masks[i] - 1)) == 0
                                and br.out_masks[i] == br.in_masks[i]
                            ):
                                u_pres.discard(i)
                for i in range(m):
                    in_masks[i] &= u_in[i]
                    out_masks[i] &= u_out[i]
                preserved |= u_pres

        # 2. Contextual specialization (`h ; E` across all non-shape occurrences, e.g. `h1 ; pol ; topo`)
        if use_context:
            succs = find_contextual_successors(prob, h)
            if succs:
                # Union over all successor contexts `E` of:
                # - allowed intermediate values `q.i` (anything outside is dropped by `E` anyway!)
                # - whether `E` is completely oblivious to `q.i` (`in_masks[i] == all_vals` and `out_masks[i] is not None` in EVERY branch of `E`)
                ctx_q_allowed = [0] * m
                oblivious = set(range(m))
                for s_expr in succs:
                    s_branches = spp.compile(s_expr)
                    for br in s_branches:
                        for i in range(m):
                            ctx_q_allowed[i] |= br.in_masks[i]
                            if br.in_masks[i] != spp.all_vals_masks[i] or br.out_masks[i] is None:
                                oblivious.discard(i)
                for i in range(m):
                    out_masks[i] &= ctx_q_allowed[i]
                # Any field `i` to which every successor `E` is oblivious is a dead output of `h`:
                # keeping `q.i = p.i` is 100% sound and complete!
                for i in oblivious:
                    if in_masks[i] & out_masks[i]:
                        preserved.add(i)

        shapes[h] = HoleShapeInfo(
            hole=h,
            in_masks=in_masks,
            out_masks=out_masks,
            preserved=preserved,
            exact_upper_clauses=captured_clauses,
        )
    return shapes


def apply_pass_hole_shape(
    prob: SynthesisProblem,
    csp: PfwCSP,
    reduce_arity: bool = False,
    use_context: bool = True,
    unbounded: bool = True,
) -> dict[str, HoleShapeInfo]:
    """Propagate hole frame & constant constraints to all `PredApp(h, ...)` sites, and optionally
    reduce the arity of `h` to `(read_fields, write_fields)`."""
    shapes = infer_hole_shapes(prob, csp, use_context=use_context)
    spp = SppCompiler(prob.fields)
    m = len(prob.fields)

    arity_maps: dict[str, HoleArityMap] = {}
    for h, sh in shapes.items():
        in_fixed: dict[int, int] = {}
        out_fixed: dict[int, int] = {}
        for i in range(m):
            im = sh.in_masks[i]
            om = sh.out_masks[i]
            if im and (im & (im - 1)) == 0:
                in_fixed[i] = im.bit_length() - 1
            if om and (om & (om - 1)) == 0:
                out_fixed[i] = om.bit_length() - 1
        pres = {i for i in sh.preserved if i not in out_fixed}
        read_f = tuple(i for i in range(m) if i not in in_fixed)
        write_f = tuple(i for i in range(m) if i not in out_fixed and i not in pres)
        arity_maps[h] = HoleArityMap(
            hole_name=h,
            in_fixed=in_fixed,
            out_fixed=out_fixed,
            preserved=pres,
            read_fields=read_f,
            write_fields=write_f,
        )
        if reduce_arity:
            csp.hole_maps[h] = arity_maps[h]
            csp.unknowns[h] = UnknownDecl(
                h,
                len(read_f) + len(write_f),
                is_wfp=False,
                comment=(
                    f"hole (reduced: in=({','.join(prob.fields[i].name for i in read_f)}) "
                    f"out=({','.join(prob.fields[i].name for i in write_f)}))"
                ),
            )

    def frame_guard(h: str, p_in: tuple[Term, ...], p_out: tuple[Term, ...]) -> Fml:
        am = arity_maps[h]
        sh = shapes[h]
        parts: list[Fml] = []
        for i in range(m):
            if sh.in_masks[i] == 0 or sh.out_masks[i] == 0:
                return FALSE
            if i in am.in_fixed:
                parts.append(mk_eq(p_in[i], am.in_fixed[i]))
            else:
                parts.append(spp.mask_to_fml(p_in[i], sh.in_masks[i], i, unbounded=unbounded))
            if i in am.out_fixed:
                parts.append(mk_eq(p_out[i], am.out_fixed[i]))
            elif i in am.preserved:
                parts.append(mk_eq(p_out[i], p_in[i]))
            else:
                parts.append(spp.mask_to_fml(p_out[i], sh.out_masks[i], i, unbounded=unbounded))
        return mk_and(*parts)

    def rewrite_calls(f: Fml, is_hole_upper_clause: bool = False) -> Fml:
        if isinstance(f, PredApp) and f.name in arity_maps and len(f.args) == 2 * m:
            p_in = f.args[:m]
            p_out = f.args[m:]
            am = arity_maps[f.name]
            new_app = (
                PredApp(
                    f.name,
                    tuple(p_in[i] for i in am.read_fields)
                    + tuple(p_out[i] for i in am.write_fields),
                )
                if reduce_arity
                else f
            )
            if is_hole_upper_clause and not reduce_arity:
                return new_app
            return mk_and(frame_guard(f.name, p_in, p_out), new_app)
        if isinstance(f, Not):
            return mk_not(rewrite_calls(f.sub, is_hole_upper_clause))
        if isinstance(f, And):
            return mk_and(*(rewrite_calls(x, is_hole_upper_clause) for x in f.items))
        if isinstance(f, Or):
            return mk_or(*(rewrite_calls(x, is_hole_upper_clause) for x in f.items))
        if isinstance(f, Exists):
            return mk_exists(f.vars, rewrite_calls(f.body, is_hole_upper_clause))
        return f

    new_clauses: list[Clause] = []
    for cl in csp.clauses:
        # Detect pure `X(p, p') => U_fml` upper-bound clauses
        is_upper = isinstance(cl.body, PredApp) and cl.body.name in arity_maps and not has_pred_app(cl.head)
        n_body = rewrite_calls(cl.body, is_hole_upper_clause=is_upper)
        n_head = rewrite_calls(cl.head, is_hole_upper_clause=False)
        n_cl = simplify_clause_equalities(Clause(cl.forall_vars, n_body, n_head, cl.tag))
        if n_cl.body == FALSE or n_cl.head == TRUE:
            continue
        # If `reduce_arity` baked the exact Cartesian product of `X <= U` into `frame_guard`,
        # check if `n_body` syntactically implies `n_head` (e.g. `sw=2 /\ sw2=2 => sw=2 /\ sw2=2`)
        if is_upper and reduce_arity:
            b_set = set(n_body.items) if isinstance(n_body, And) else {n_body}
            h_set = set(n_head.items) if isinstance(n_head, And) else {n_head}
            if h_set.issubset(b_set):
                continue
        new_clauses.append(n_cl)
    csp.clauses = new_clauses
    return shapes


# ---- Pass 3: Project Left-Stars `St(p, p') -> R(p_kept, p')` ----


def apply_pass_project_st(csp: PfwCSP) -> None:
    """Project out start-packet fields of left-star predicates `St` when goals do not relate `p` to `p'`."""
    m = len(csp.fields)
    for st_name in list(csp.left_stars.keys()):
        if st_name not in csp.unknowns:
            continue
        # Find all goal clauses where `st_name` appears in `body` and NOT in `head`
        goal_indices: list[int] = []
        other_uses = False
        for idx, cl in enumerate(csp.clauses):
            in_body = st_name in pred_names_in(cl.body)
            in_head = st_name in pred_names_in(cl.head)
            if in_body and not in_head:
                goal_indices.append(idx)
            elif in_head and not cl.tag.startswith(f"{st_name}-"):
                other_uses = True
        if other_uses or not goal_indices:
            continue

        # Check each goal clause: must have a single `PredApp(st_name, args)` in `body`
        # and extract `(init_u_args, pre_fml_on_u, post_fml_on_rest, head_fml, kept_indices)`
        parsed_goals: list[tuple[int, list[Term], tuple[Term, ...], Fml, Fml, Fml, set[int]]] = []
        possible = True
        for idx in goal_indices:
            cl = csp.clauses[idx]
            items = list(cl.body.items) if isinstance(cl.body, And) else [cl.body]
            st_apps = [it for it in items if isinstance(it, PredApp) and it.name == st_name]
            if len(st_apps) != 1:
                possible = False
                break
            app = st_apps[0]
            u_args = list(app.args[:m])
            v_args = app.args[m:]
            u_vars = [a for a in u_args if isinstance(a, str)]
            # String variables in `u_args` must be distinct and not appear in `v_args` unless kept
            if len(set(u_vars)) != len(u_vars):
                possible = False
                break
            u_set = set(u_vars)
            u_idx_of = {u_args[i]: i for i in range(m) if isinstance(u_args[i], str)}
            pre_items: list[Fml] = []
            post_items: list[Fml] = []
            kept: set[int] = set()
            for v in set(v_args) & u_set:
                kept.add(u_idx_of[v])
            for it in items:
                if it == app:
                    continue
                fv = free_vars(it)
                if fv and fv.issubset(u_set) and not has_pred_app(it):
                    pre_items.append(it)
                else:
                    post_items.append(it)
                    for v in fv & u_set:
                        kept.add(u_idx_of[v])
            for v in free_vars(cl.head) & u_set:
                kept.add(u_idx_of[v])
            if len(kept) == m:
                possible = False
                break
            parsed_goals.append(
                (idx, u_args, v_args, mk_and(*pre_items), mk_and(*post_items), cl.head, kept)
            )

        if not possible:
            continue

        # Grab the original step clauses of `st_name`
        step_clauses = [
            cl for cl in csp.clauses if cl.tag.startswith(f"{st_name}-step")
        ]
        remove_indices = set(goal_indices) | {
            i for i, cl in enumerate(csp.clauses) if cl.tag.startswith(f"{st_name}-")
        }

        new_clauses: list[Clause] = [
            cl for i, cl in enumerate(csp.clauses) if i not in remove_indices
        ]
        del csp.unknowns[st_name]

        for g_num, (_, u_args, v_args, pre_fml, post_fml, head_fml, kept_set) in enumerate(
            parsed_goals, 1
        ):
            kept_t = tuple(sorted(kept_set))
            r_name = (
                ("R" if st_name == "St" else f"R_{st_name}")
                if len(parsed_goals) == 1
                else f"R{g_num}"
            )
            while r_name in csp.unknowns:
                r_name += "_"
            csp.unknowns[r_name] = UnknownDecl(
                r_name,
                len(kept_t) + m,
                is_wfp=False,
                comment=f"projected reachability from {st_name} (arity {2 * m} -> {len(kept_t) + m})",
            )

            # 1) Init clause: `Pre(u) => R(u|_K, u)`
            init_head = PredApp(r_name, tuple(u_args[i] for i in kept_t) + tuple(u_args))
            init_vars = tuple(dict.fromkeys(v for v in u_args if isinstance(v, str)))
            new_clauses.append(
                simplify_clause_equalities(
                    Clause(init_vars, pre_fml, init_head, f"{r_name}-init")
                )
            )
            # 2) Step clauses: replace `st_name(p, r)` -> `r_name(p|_K, r)` and `st_name(p, p2)` -> `r_name(p|_K, p2)`
            for scl in step_clauses:
                def proj_st_app(f: Fml, r_nm: str = r_name, kt: tuple[int, ...] = kept_t) -> Fml:
                    if isinstance(f, PredApp) and f.name == st_name:
                        p_part = f.args[:m]
                        q_part = f.args[m:]
                        return PredApp(r_nm, tuple(p_part[i] for i in kt) + q_part)
                    if isinstance(f, And):
                        return mk_and(*(proj_st_app(x, r_nm, kt) for x in f.items))
                    if isinstance(f, Or):
                        return mk_or(*(proj_st_app(x, r_nm, kt) for x in f.items))
                    return f

                nb = proj_st_app(scl.body)
                nh = proj_st_app(scl.head)
                used = free_vars(nb) | free_vars(nh)
                nfv = tuple(v for v in scl.forall_vars if v in used)
                new_clauses.append(
                    simplify_clause_equalities(Clause(nfv, nb, nh, f"{r_name}-step"))
                )
            # 3) Goal clause: `R(u|_K, v) /\ Post(u|_K, v) => head`
            goal_body = mk_and(
                PredApp(r_name, tuple(u_args[i] for i in kept_t) + tuple(v_args)),
                post_fml,
            )
            used_g = free_vars(goal_body) | free_vars(head_fml)
            g_vars = tuple(
                dict.fromkeys(
                    v for v in list(u_args) + list(v_args) if isinstance(v, str) and v in used_g
                )
            )
            new_clauses.append(
                simplify_clause_equalities(Clause(g_vars, goal_body, head_fml, f"{r_name}-bad"))
            )

        csp.clauses = new_clauses


# ---- Pass 4: Eliminate Existential Packet Witnesses on RHS (`elim_exists`) ----


def distribute_and_eliminate_exists(f: Fml, max_dnf_branches: int = 128) -> Fml:
    """Eliminate `Exists` on the RHS by distributing `And` over `Or` (up to `max_dnf_branches`)
    and substituting all `v = term` equalities (e.g. cable endpoints + hole frames)."""
    if isinstance(f, Or):
        return mk_or(*(distribute_and_eliminate_exists(x, max_dnf_branches) for x in f.items))
    if isinstance(f, And):
        return mk_and(*(distribute_and_eliminate_exists(x, max_dnf_branches) for x in f.items))
    if not isinstance(f, Exists):
        return f

    f = simplify_exists_equalities(hoist_positive_exists(f))
    if not isinstance(f, Exists):
        return f

    # Convert `f.body` to DNF ONLY across `Or`s that constrain at least one bound variable of `f.vars`!
    bvars = set(f.vars)

    def to_targeted_dnf(sub: Fml) -> list[Fml]:
        if isinstance(sub, Or) and (free_vars(sub) & bvars):
            res: list[Fml] = []
            for it in sub.items:
                res.extend(to_targeted_dnf(it))
                if len(res) > max_dnf_branches:
                    return [sub]
            return res
        if isinstance(sub, And):
            acc: list[Fml] = [TRUE]
            for it in sub.items:
                ch = to_targeted_dnf(it)
                if len(acc) * len(ch) > max_dnf_branches:
                    acc = [mk_and(a, it) for a in acc]
                else:
                    acc = [mk_and(a, b) for a in acc for b in ch if mk_and(a, b) != FALSE]
            return acc
        return [sub]

    dnf_branches = to_targeted_dnf(f.body)
    disj: list[Fml] = []
    for br in dnf_branches:
        # Also expand small bounded integer intervals `lo <= v <= hi` (with `hi - lo <= 8`) for remaining bound vars!
        sim = simplify_exists_equalities(mk_exists(f.vars, br))
        sim = expand_small_bounded_exists(sim, max_span=8)
        if sim != FALSE:
            disj.append(sim)
    return mk_or(*disj)


def expand_small_bounded_exists(f: Fml, max_span: int = 8) -> Fml:
    if not isinstance(f, Exists):
        return f
    items = list(f.body.items) if isinstance(f.body, And) else [f.body]
    for bv in f.vars:
        lo: int | None = None
        hi: int | None = None
        for it in items:
            if isinstance(it, Cmp):
                if it.op == "<=" and isinstance(it.lhs, int) and it.rhs == bv:
                    lo = it.lhs if lo is None else max(lo, it.lhs)
                elif it.op == "<=" and it.lhs == bv and isinstance(it.rhs, int):
                    hi = it.rhs if hi is None else min(hi, it.rhs)
                elif it.op == ">=" and it.lhs == bv and isinstance(it.rhs, int):
                    lo = it.rhs if lo is None else max(lo, it.rhs)
                elif it.op == ">=" and isinstance(it.lhs, int) and it.rhs == bv:
                    hi = it.lhs if hi is None else min(hi, it.lhs)
        if lo is not None and hi is not None and 0 <= hi - lo <= max_span:
            rem_vars = [v for v in f.vars if v != bv]
            cases = [
                expand_small_bounded_exists(
                    simplify_exists_equalities(mk_exists(rem_vars, subst_fml(f.body, {bv: val}))),
                    max_span=max_span,
                )
                for val in range(lo, hi + 1)
            ]
            return mk_or(*cases)
    return f


def apply_pass_elim_exists(csp: PfwCSP) -> None:
    new_clauses: list[Clause] = []
    for cl in csp.clauses:
        n_head = distribute_and_eliminate_exists(cl.head)
        n_cl = simplify_clause_equalities(Clause(cl.forall_vars, cl.body, n_head, cl.tag))
        if n_cl.body != FALSE and n_cl.head != TRUE:
            new_clauses.append(n_cl)
    csp.clauses = new_clauses


# ---- Pass 5 (Optional): Fix `W_` via BFS Shortest-Path Distances (`bfs_wf`) ----


def extract_step_graph(
    prob: SynthesisProblem, step_expr: tuple, loc_field: int = 0
) -> dict[int, set[int]]:
    """Extract directed switch adjacency `u -> {v}` solely from the star step expression `step_expr`
    (never from `Spec` assertions, which teleport ingress directly to egress!)."""
    spp = SppCompiler(prob.fields)
    adj: dict[int, set[int]] = defaultdict(set)

    def scan(e: tuple) -> None:
        if is_hole_and_star_free(e):
            for br in spp.compile(e):
                im = br.in_masks[loc_field]
                om = br.out_masks[loc_field]
                if om is not None and (im & (im - 1)) == 0 and (om & (om - 1)) == 0:
                    u = im.bit_length() - 1
                    v = om.bit_length() - 1
                    if u != v:
                        adj[u].add(v)
            return
        if e[0] in ("not", "star"):
            scan(e[1])
        elif e[0] in ("plus", "seq"):
            scan(e[1])
            scan(e[2])

    scan(step_expr)
    return adj


def apply_pass_bfs_wf(prob: SynthesisProblem, csp: PfwCSP, loc_field: int = 0) -> None:
    """Replace `declare-wfp W_` with BFS distance decrease `0 <= dist(r.sw, p2.sw) < dist(p.sw, p2.sw)`."""
    if not csp.right_stars:
        return
    m = len(prob.fields)
    for d_name, (w_name, step_expr) in list(csp.right_stars.items()):
        adj = extract_step_graph(prob, step_expr, loc_field=loc_field)
        if not adj:
            continue
        nodes = sorted(set(adj.keys()) | {v for vs in adj.values() for v in vs})
        rev_adj: dict[int, set[int]] = defaultdict(set)
        for u, vs in adj.items():
            for v in vs:
                rev_adj[v].add(u)

        dist: dict[tuple[int, int], int] = {}
        for dst in nodes:
            q = deque([(dst, 0)])
            seen = {dst}
            while q:
                u, d = q.popleft()
                dist[(u, dst)] = d
                for prev in rev_adj[u]:
                    if prev not in seen:
                        seen.add(prev)
                        q.append((prev, d + 1))

        def wfp_fml(p_sw: Term, r_sw: Term, dst_sw: Term) -> Fml:
            triples: list[Fml] = []
            for (u, d), du in dist.items():
                for v in nodes:
                    dv = dist.get((v, d))
                    if dv is not None and dv < du:
                        triples.append(
                            mk_and(mk_eq(p_sw, u), mk_eq(r_sw, v), mk_eq(dst_sw, d))
                        )
            return mk_or(*triples)

        def replace_w(f: Fml, wn: str = w_name) -> Fml:
            if isinstance(f, PredApp) and f.name == wn and len(f.args) == 4 * m:
                p_sw = f.args[loc_field]
                dst_sw = f.args[m + loc_field]
                r_sw = f.args[2 * m + loc_field]
                return wfp_fml(p_sw, r_sw, dst_sw)
            if isinstance(f, Not):
                return mk_not(replace_w(f.sub, wn))
            if isinstance(f, And):
                return mk_and(*(replace_w(x, wn) for x in f.items))
            if isinstance(f, Or):
                return mk_or(*(replace_w(x, wn) for x in f.items))
            if isinstance(f, Exists):
                return mk_exists(f.vars, replace_w(f.body, wn))
            return f

        csp.clauses = [
            simplify_clause_equalities(Clause(cl.forall_vars, cl.body, replace_w(cl.head), cl.tag))
            for cl in csp.clauses
        ]
        csp.unknowns.pop(w_name, None)


# ---- Pass 6: Simple-Path Compilation for Right-Stars `D` (`compile_paths`) ----


def extract_conjunct_atoms(f: Fml) -> frozenset[Fml]:
    return frozenset(f.items) if isinstance(f, And) else frozenset([f])


def absorb_disjuncts(conj_formulas: list[Fml]) -> Fml:
    r"""Apply Boolean absorption `A \/ (A /\ B) == A` across path conjunctions!
    Any path whose atom set is a superset of another path's atom set is soundly & completely redundant."""
    unique: list[tuple[frozenset[Fml], Fml]] = []
    for cf in conj_formulas:
        if cf == TRUE:
            return TRUE
        if cf == FALSE:
            continue
        atoms = extract_conjunct_atoms(cf)
        unique.append((atoms, cf))

    unique.sort(key=lambda pair: len(pair[0]))
    kept: list[tuple[frozenset[Fml], Fml]] = []
    for atoms, cf in unique:
        if any(prev_atoms.issubset(atoms) for prev_atoms, _ in kept):
            continue
        kept.append((atoms, cf))
    return mk_or(*(cf for _, cf in kept))


def apply_pass_compile_paths(
    prob: SynthesisProblem,
    csp: PfwCSP,
    shapes: dict[str, HoleShapeInfo] | None = None,
    unbounded: bool = True,
    max_simple_paths: int = 512,
    max_active_states: int = 2048,
) -> None:
    """Compile right-stars `D_e` into exact simple-path formulas when active state space is finite
    and remaining header fields are invariant under `e`."""
    if not csp.right_stars:
        return
    if shapes is None:
        shapes = infer_hole_shapes(prob, csp, use_context=True)

    spp = SppCompiler(prob.fields)
    m = len(prob.fields)

    def expr_preserves_field(e: tuple, f_idx: int) -> bool:
        if is_hole_and_star_free(e):
            for br in spp.compile(e):
                if br.out_masks[f_idx] is not None:
                    return False
            return True
        t = e[0]
        if t == "hole":
            sh = shapes.get(e[1])
            return sh is not None and f_idx in sh.preserved
        if t in ("not", "star"):
            return expr_preserves_field(e[1], f_idx)
        if t in ("plus", "seq"):
            return expr_preserves_field(e[1], f_idx) and expr_preserves_field(e[2], f_idx)
        return False

    for d_name, (w_name, step_expr) in list(csp.right_stars.items()):
        inv_fields = [i for i in range(m) if expr_preserves_field(step_expr, i)]
        act_fields = [i for i in range(m) if i not in inv_fields]
        # Allow large finite active domains since transitions are sparse
        act_domain_size = 1
        for i in act_fields:
            act_domain_size *= 1 << prob.fields[i].width
        if act_domain_size > 1 << 24:
            continue

        # Find goal clauses with `D_name(p, p2)` in `head` (and not `d_name-step`)
        goal_indices = [
            idx
            for idx, cl in enumerate(csp.clauses)
            if not cl.tag.startswith(f"{d_name}-")
            and isinstance(cl.head, PredApp)
            and cl.head.name == d_name
        ]
        if not goal_indices:
            continue

        # Symbolic variables for invariant fields `z`
        z_vars = {i: prob.fields[i].name for i in inv_fields}

        # Helper to translate one step of `step_expr` from concrete active state `u_act` to all reachable `v_act`
        # using our `GenericTranslator` + `HoleShape` + `distribute_and_eliminate_exists`!
        sub_gt = GenericTranslator(prob, subst_seq=True, unbounded=unbounded)
        sub_gt.csp.hole_maps = dict(csp.hole_maps)

        def rewrite_hole_app_for_csp(f: Fml) -> Fml:
            if isinstance(f, PredApp) and f.name in shapes and len(f.args) == 2 * m:
                sh = shapes[f.name]
                p_in, p_out = f.args[:m], f.args[m:]
                fg_parts: list[Fml] = []
                for i in range(m):
                    if sh.in_masks[i] == 0 or sh.out_masks[i] == 0:
                        return FALSE
                    fg_parts.append(spp.mask_to_fml(p_in[i], sh.in_masks[i], i, unbounded=unbounded))
                    if i in sh.preserved:
                        fg_parts.append(mk_eq(p_out[i], p_in[i]))
                    else:
                        fg_parts.append(
                            spp.mask_to_fml(p_out[i], sh.out_masks[i], i, unbounded=unbounded)
                        )
                if f.name in csp.hole_maps:
                    am = csp.hole_maps[f.name]
                    app = PredApp(
                        f.name,
                        tuple(p_in[i] for i in am.read_fields)
                        + tuple(p_out[i] for i in am.write_fields),
                    )
                else:
                    app = f
                return mk_and(*fg_parts, app)
            if isinstance(f, Not):
                return mk_not(rewrite_hole_app_for_csp(f.sub))
            if isinstance(f, And):
                return mk_and(*(rewrite_hole_app_for_csp(x) for x in f.items))
            if isinstance(f, Or):
                return mk_or(*(rewrite_hole_app_for_csp(x) for x in f.items))
            if isinstance(f, Exists):
                return mk_exists(f.vars, rewrite_hole_app_for_csp(f.body))
            return f

        # Cache 1-step transition map: `u_state -> dict[v_state, Fml(z)]`
        trans_cache: dict[tuple[int, ...], dict[tuple[int, ...], Fml]] = {}

        def get_transitions(u_state: tuple[int, ...]) -> dict[tuple[int, ...], Fml] | None:
            if u_state in trans_cache:
                return trans_cache[u_state]
            p_in: list[Term] = [0] * m
            for pos, f_idx in enumerate(act_fields):
                p_in[f_idx] = u_state[pos]
            for f_idx in inv_fields:
                p_in[f_idx] = z_vars[f_idx]

            out_act_vars = {f_idx: f"_oa_{f_idx}" for f_idx in act_fields}
            p_out: list[Term] = [0] * m
            for f_idx in act_fields:
                p_out[f_idx] = out_act_vars[f_idx]
            for f_idx in inv_fields:
                p_out[f_idx] = z_vars[f_idx]

            raw_step = sub_gt.translate(step_expr, p_in, p_out, "-")
            step_shaped = rewrite_hole_app_for_csp(raw_step)
            step_noex = distribute_and_eliminate_exists(step_shaped, max_dnf_branches=1024)
            if isinstance(step_noex, Exists):
                return None

            # Collect candidate output values directly from equality atoms `(= _oa_f c)` when constrained!
            eq_mentions: dict[str, set[int]] = defaultdict(set)
            unconstrained_vars: set[str] = set()

            def collect_eq_vals(sub: Fml) -> None:
                if isinstance(sub, Cmp) and sub.op == "=":
                    if isinstance(sub.lhs, str) and isinstance(sub.rhs, int):
                        eq_mentions[sub.lhs].add(sub.rhs)
                    elif isinstance(sub.rhs, str) and isinstance(sub.lhs, int):
                        eq_mentions[sub.rhs].add(sub.lhs)
                    else:
                        for t in (sub.lhs, sub.rhs):
                            if isinstance(t, str):
                                unconstrained_vars.add(t)
                elif isinstance(sub, Cmp):
                    for t in (sub.lhs, sub.rhs):
                        if isinstance(t, str):
                            unconstrained_vars.add(t)
                elif isinstance(sub, PredApp):
                    for t in sub.args:
                        if isinstance(t, str):
                            unconstrained_vars.add(t)
                elif isinstance(sub, Not):
                    for v in free_vars(sub):
                        unconstrained_vars.add(v)
                elif isinstance(sub, (And, Or)):
                    for x in sub.items:
                        collect_eq_vals(x)

            collect_eq_vals(step_noex)
            cand_vals: list[list[int]] = []
            for f_idx in act_fields:
                ov = out_act_vars[f_idx]
                if ov in eq_mentions and ov not in unconstrained_vars:
                    cand_vals.append(sorted(eq_mentions[ov]))
                else:
                    cand_vals.append(list(range(prob.fields[f_idx].max_val + 1)))

            succ_map: dict[tuple[int, ...], Fml] = {}

            def enum_v(idx: int, cur_v: list[int], cur_fml: Fml) -> None:
                if cur_fml == FALSE:
                    return
                if idx == len(act_fields):
                    succ_map[tuple(cur_v)] = cur_fml
                    return
                f_idx = act_fields[idx]
                ov = out_act_vars[f_idx]
                for val in cand_vals[idx]:
                    nxt_fml = subst_fml(cur_fml, {ov: val})
                    if nxt_fml != FALSE:
                        cur_v.append(val)
                        enum_v(idx + 1, cur_v, nxt_fml)
                        cur_v.pop()

            enum_v(0, [], step_noex)
            trans_cache[u_state] = succ_map
            return succ_map

        # Compile each goal clause `cl.body => D_name(p, p2)`
        compiled_clauses: dict[int, list[Clause]] = {}
        all_compiled = True

        for idx in goal_indices:
            cl = csp.clauses[idx]
            assert isinstance(cl.head, PredApp)
            d_in_orig = cl.head.args[:m]
            d_out_orig = cl.head.args[m:]

            # Split `cl.body` across top-level `Or` disjuncts first so per-branch equalities
            # (like `(= dst2 dst)` and `(= typ2 typ)` inside `Spec`) simplify before checking `d_in == d_out`!
            raw_disjuncts = list(cl.body.items) if isinstance(cl.body, Or) else [cl.body]
            goal_replacements: list[Clause] = []
            pair_failed = False

            for raw_br in raw_disjuncts:
                sub_cl = simplify_clause_equalities(
                    Clause(cl.forall_vars, raw_br, cl.head, cl.tag)
                )
                if sub_cl.body == FALSE or sub_cl.head == TRUE:
                    continue
                assert isinstance(sub_cl.head, PredApp)
                d_in = sub_cl.head.args[:m]
                d_out = sub_cl.head.args[m:]
                body = sub_cl.body

                env_inv: dict[str, Term] = {}
                inv_ok = True
                for i in inv_fields:
                    a_in, a_out = d_in[i], d_out[i]
                    if a_in == a_out:
                        if isinstance(a_in, str):
                            env_inv[a_in] = z_vars[i]
                    else:
                        inv_ok = False
                        break
                if not inv_ok:
                    pair_failed = True
                    break

                body_z = subst_fml(body, env_inv)
                # Add any constant value of `d_in[i]` (when `a_in == a_out == const`) as `z_vars[i] == const`
                inv_const_guards = [
                    mk_eq(z_vars[i], d_in[i])
                    for i in inv_fields
                    if isinstance(d_in[i], int)
                ]
                body_z = mk_and(body_z, *inv_const_guards)
                d_in_z = [env_inv.get(a, a) if isinstance(a, str) else a for a in d_in]
                d_out_z = [env_inv.get(a, a) if isinstance(a, str) else a for a in d_out]

                # Enumerate concrete `(u_in, u_out)` pairs over active fields where `body_z` is satisfiable
                act_pairs: list[tuple[tuple[int, ...], tuple[int, ...], Fml]] = []

                def enum_io(
                    pos: int,
                    u_in_acc: list[int],
                    u_out_acc: list[int],
                    cur_b: Fml,
                ) -> None:
                    if cur_b == FALSE:
                        return
                    if pos == len(act_fields):
                        act_pairs.append((tuple(u_in_acc), tuple(u_out_acc), cur_b))
                        return
                    f_idx = act_fields[pos]
                    tin = d_in_z[f_idx]
                    tout = d_out_z[f_idx]
                    in_dom = (
                        [tin]
                        if isinstance(tin, int)
                        else list(range(prob.fields[f_idx].max_val + 1))
                    )
                    for vin in in_dom:
                        b1 = subst_fml(cur_b, {tin: vin}) if isinstance(tin, str) else cur_b
                        if b1 == FALSE:
                            continue
                        tout_now = vin if tout == tin else tout
                        out_dom = (
                            [tout_now]
                            if isinstance(tout_now, int)
                            else list(range(prob.fields[f_idx].max_val + 1))
                        )
                        for vout in out_dom:
                            b2 = (
                                subst_fml(b1, {tout_now: vout})
                                if isinstance(tout_now, str)
                                else b1
                            )
                            if b2 != FALSE:
                                u_in_acc.append(vin)
                                u_out_acc.append(vout)
                                enum_io(pos + 1, u_in_acc, u_out_acc, b2)
                                u_in_acc.pop()
                                u_out_acc.pop()

                enum_io(0, [], [], body_z)

                for u_start, u_goal, guard_z in act_pairs:
                    # Extract any constant equalities `z_var = c` from `guard_z` to specialize edge conditions on the fly!
                    z_const_env: dict[str, Term] = {}
                    gz_items = list(guard_z.items) if isinstance(guard_z, And) else [guard_z]
                    for git in gz_items:
                        if isinstance(git, Cmp) and git.op == "=":
                            if isinstance(git.lhs, str) and isinstance(git.rhs, int):
                                z_const_env[git.lhs] = git.rhs
                            elif isinstance(git.rhs, str) and isinstance(git.lhs, int):
                                z_const_env[git.rhs] = git.lhs

                    path_formulas: list[Fml] = []

                    def dfs_paths(
                        cur: tuple[int, ...],
                        visited: set[tuple[int, ...]],
                        conds: list[Fml],
                    ) -> bool:
                        if (
                            len(visited) > max_active_states
                            or len(path_formulas) > max_simple_paths
                        ):
                            return False
                        if cur == u_goal:
                            path_formulas.append(mk_and(*conds))
                            return True
                        succs = get_transitions(cur)
                        if succs is None:
                            return False
                        for nxt, raw_edge_cond in succs.items():
                            if nxt in visited:
                                continue
                            edge_cond = (
                                subst_fml(raw_edge_cond, z_const_env)
                                if z_const_env
                                else raw_edge_cond
                            )
                            if edge_cond == FALSE or mk_and(guard_z, *conds, edge_cond) == FALSE:
                                continue
                            visited.add(nxt)
                            conds.append(edge_cond)
                            if not dfs_paths(nxt, visited, conds):
                                return False
                            conds.pop()
                            visited.remove(nxt)
                        return True

                    if not dfs_paths(u_start, {u_start}, []):
                        pair_failed = True
                        break

                    reach_fml = absorb_disjuncts(path_formulas)
                    # Substitute any `z_vars[i] == const` in `guard_z` directly into `reach_fml`!
                    used_vs = free_vars(guard_z) | free_vars(reach_fml)
                    fvs = tuple(
                        dict.fromkeys(
                            v
                            for v in [z_vars[i] for i in inv_fields] + list(sub_cl.forall_vars)
                            if v in used_vs
                        )
                    )
                    goal_replacements.append(
                        simplify_clause_equalities(
                            Clause(fvs, guard_z, reach_fml, f"{cl.tag}-paths")
                        )
                    )
                if pair_failed:
                    break

            if pair_failed:
                all_compiled = False
                break
            compiled_clauses[idx] = [
                c for c in goal_replacements if c.body != FALSE and c.head != TRUE
            ]

        if not all_compiled:
            continue

        # Replace goal clauses and check if `d_name` is used anywhere else
        updated_clauses: list[Clause] = []
        for idx, cl in enumerate(csp.clauses):
            if idx in compiled_clauses:
                updated_clauses.extend(compiled_clauses[idx])
            else:
                updated_clauses.append(cl)

        still_used = any(
            not cl.tag.startswith(f"{d_name}-")
            and (d_name in pred_names_in(cl.body) or d_name in pred_names_in(cl.head))
            for cl in updated_clauses
        )
        if not still_used:
            updated_clauses = [
                cl for cl in updated_clauses if not cl.tag.startswith(f"{d_name}-")
            ]
            csp.unknowns.pop(d_name, None)
            csp.unknowns.pop(w_name, None)
            csp.right_stars.pop(d_name, None)
        csp.clauses = updated_clauses


# =============================================================================
# 5. SMT-LIB 2 Printer & PCSat Solution Extractor (`.nksol` back-translation)
# =============================================================================


def fml_to_smt2(f: Fml) -> str:
    if isinstance(f, BoolLit):
        return "true" if f.val else "false"
    if isinstance(f, Cmp):
        if f.op == "!=":
            return f"(not (= {f.lhs} {f.rhs}))"
        return f"({f.op} {f.lhs} {f.rhs})"
    if isinstance(f, Not):
        return f"(not {fml_to_smt2(f.sub)})"
    if isinstance(f, And):
        return f"(and {' '.join(fml_to_smt2(x) for x in f.items)})"
    if isinstance(f, Or):
        return f"(or {' '.join(fml_to_smt2(x) for x in f.items)})"
    if isinstance(f, Exists):
        binders = " ".join(f"({v} Int)" for v in f.vars)
        return f"(exists ({binders}) {fml_to_smt2(f.body)})"
    if isinstance(f, PredApp):
        if not f.args:
            return f.name
        return f"({f.name} {' '.join(str(a) for a in f.args)})"
    raise TypeError(f)


def emit_smt2(csp: PfwCSP, header_comment: str = "") -> str:
    lines: list[str] = []
    if header_comment:
        for ln in header_comment.strip().splitlines():
            lines.append(f"; {ln}")
    field_desc = ", ".join(f"{f.name}:x[{f.start}..{f.end}]" for f in csp.fields)
    lines.append(f"; Packet fields ({len(csp.fields)}): {field_desc}")
    lines.append("(set-logic HORN)")
    lines.append("")

    for decl in csp.unknowns.values():
        kw = "declare-wfp" if decl.is_wfp else "declare-fun"
        sorts = " ".join(["Int"] * decl.arity)
        cmt = f"  ; {decl.comment}" if decl.comment else ""
        lines.append(f"({kw} {decl.name} ({sorts}) Bool){cmt}")
    lines.append("")

    for cl in csp.clauses:
        if cl.body == FALSE or cl.head == TRUE:
            continue
        if cl.tag:
            lines.append(f"; [{cl.tag}]")
        implication = (
            fml_to_smt2(cl.head)
            if cl.body == TRUE
            else f"(=> {fml_to_smt2(cl.body)} {fml_to_smt2(cl.head)})"
        )
        if cl.forall_vars:
            binders = " ".join(f"({v} Int)" for v in cl.forall_vars)
            lines.append(f"(assert (forall ({binders})\n  {implication}))")
        else:
            lines.append(f"(assert {implication})")
        lines.append("")

    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


# ---- S-expression evaluator to turn PCSat's `(define-fun |h| ...)` into `.nksol` ----


def parse_sexp(text: str) -> list:
    toks = re.findall(r"\(|\)|\|[^|]*\||[^\s()]+", text)
    stack: list[list] = [[]]
    for tok in toks:
        if tok == "(":
            sub: list = []
            stack[-1].append(sub)
            stack.append(sub)
        elif tok == ")":
            if len(stack) > 1:
                stack.pop()
        else:
            if tok.startswith("|") and tok.endswith("|"):
                tok = tok[1:-1]
            stack[-1].append(tok)
    return stack[0]


def eval_smt_expr(expr: object, env: dict[str, int]) -> int | bool:
    if isinstance(expr, str):
        if expr == "true":
            return True
        if expr == "false":
            return False
        if expr.lstrip("-").isdigit():
            return int(expr)
        return env[expr]
    assert isinstance(expr, list) and expr
    op = expr[0]
    if op == "-" and len(expr) == 2:
        return -int(eval_smt_expr(expr[1], env))
    if op == "not":
        return not bool(eval_smt_expr(expr[1], env))
    if op == "and":
        return all(bool(eval_smt_expr(a, env)) for a in expr[1:])
    if op == "or":
        return any(bool(eval_smt_expr(a, env)) for a in expr[1:])
    if op == "=>":
        return (not bool(eval_smt_expr(expr[1], env))) or bool(eval_smt_expr(expr[2], env))
    if op == "ite":
        return (
            eval_smt_expr(expr[2], env)
            if bool(eval_smt_expr(expr[1], env))
            else eval_smt_expr(expr[3], env)
        )
    if op == "+":
        return sum(int(eval_smt_expr(a, env)) for a in expr[1:])
    if op == "-" and len(expr) > 2:
        first = int(eval_smt_expr(expr[1], env))
        return first - sum(int(eval_smt_expr(a, env)) for a in expr[2:])
    if op == "*":
        prod = 1
        for a in expr[1:]:
            prod *= int(eval_smt_expr(a, env))
        return prod
    if op in ("=", "distinct", "<=", "<", ">=", ">"):
        a = int(eval_smt_expr(expr[1], env))
        b = int(eval_smt_expr(expr[2], env))
        return {
            "=": a == b,
            "distinct": a != b,
            "<=": a <= b,
            "<": a < b,
            ">=": a >= b,
            ">": a > b,
        }[op]
    if op == "let":
        new_env = dict(env)
        for bname, bval in expr[1]:
            new_env[bname] = eval_smt_expr(bval, env)  # type: ignore[assignment]
        return eval_smt_expr(expr[2], new_env)
    raise TranslateError(f"Unsupported SMT operator in model extraction: {op!r}")


def pcsat_model_to_nksol(
    csp: PfwCSP, smt2_model_text: str, max_tuples: int = 262144
) -> str:
    """Convert PCSat's `(define-fun ...)` lines into a `.nksol` NetKAT definition file
    verifiable by `nksynth problem.nksynth --check sol.nksol`."""
    sexps = parse_sexp(smt2_model_text)
    defs_by_name: dict[str, tuple[list[str], object]] = {}
    for item in sexps:
        if isinstance(item, list) and len(item) >= 5 and item[0] == "define-fun":
            name = str(item[1])
            params = [str(p[0]) for p in item[2]]
            body = item[4]
            defs_by_name[name] = (params, body)

    m = len(csp.fields)
    spp = SppCompiler(csp.fields)
    out_lines: list[str] = []

    for h in csp.holes:
        if h not in defs_by_name:
            raise TranslateError(f"Hole `{h}` missing from PCSat output")
        params, body = defs_by_name[h]
        am = csp.hole_maps.get(h)
        if am is None:
            read_f = tuple(range(m))
            write_f = tuple(range(m))
            in_fixed: dict[int, int] = {}
            out_fixed: dict[int, int] = {}
            preserved: set[int] = set()
        else:
            read_f = am.read_fields
            write_f = am.write_fields
            in_fixed = am.in_fixed
            out_fixed = am.out_fixed
            preserved = am.preserved

        total = 1
        for i in read_f:
            total *= csp.fields[i].max_val + 1
        for i in write_f:
            total *= csp.fields[i].max_val + 1
        if total > max_tuples:
            raise TranslateError(
                f"Domain of `{h}` has {total} > {max_tuples} tuples; use Z3 model verification instead"
            )

        branches: list[SppBranch] = []

        def enum_tuples(pos: int, vals: list[int]) -> None:
            if pos == len(read_f) + len(write_f):
                env = {params[k]: vals[k] for k in range(len(params))}
                if bool(eval_smt_expr(body, env)):
                    in_m = [0] * m
                    out_m: list[int | None] = [None] * m
                    for k, fi in enumerate(read_f):
                        in_m[fi] = 1 << vals[k]
                    for fi, fv in in_fixed.items():
                        in_m[fi] = 1 << fv
                    offset = len(read_f)
                    for k, fi in enumerate(write_f):
                        out_m[fi] = 1 << vals[offset + k]
                    for fi, fv in out_fixed.items():
                        out_m[fi] = 1 << fv
                    for fi in preserved:
                        out_m[fi] = None
                    branches.append(SppBranch(tuple(in_m), tuple(out_m)))
                return
            fi = read_f[pos] if pos < len(read_f) else write_f[pos - len(read_f)]
            for v in range(csp.fields[fi].max_val + 1):
                vals.append(v)
                enum_tuples(pos + 1, vals)
                vals.pop()

        enum_tuples(0, [])
        compact_brs = spp._compact(branches)
        if not compact_brs:
            out_lines.append(f"def {h} = 0")
            continue

        terms_str: list[str] = []
        for br in compact_brs:
            atoms: list[str] = []
            for i, fld in enumerate(csp.fields):
                rng = f"x[{fld.start}..{fld.end}]"
                im = br.in_masks[i]
                full = spp.all_vals_masks[i]
                if im != full:
                    inv = full & ~im
                    if (im & (im - 1)) == 0:
                        atoms.append(f"{rng}~{im.bit_length() - 1}")
                    elif (inv & (inv - 1)) == 0:
                        atoms.append(f"!({rng}~{inv.bit_length() - 1})")
                    else:
                        vs = [v for v in range(fld.max_val + 1) if (im >> v) & 1]
                        atoms.append("(" + " + ".join(f"{rng}~{v}" for v in vs) + ")")
                om = br.out_masks[i]
                if om is not None:
                    if (om & (om - 1)) == 0:
                        atoms.append(f"{rng}:={om.bit_length() - 1}")
                    else:
                        vs = [v for v in range(fld.max_val + 1) if (om >> v) & 1]
                        atoms.append("(" + " + ".join(f"{rng}:={v}" for v in vs) + ")")
            terms_str.append("(" + "; ".join(atoms) + ")" if atoms else "1")
        out_lines.append(f"def {h} = " + " + ".join(terms_str))

    return "\n".join(out_lines) + "\n"


# =============================================================================
# 6. Pipeline Presets & CLI Entrypoint
# =============================================================================

PRESETS = ("raw", "generic", "noexists", "ctx", "proj", "paths", "all", "bfs")


def compile_nksynth_to_pcsat(
    source: str,
    preset: str = "all",
    passes: list[str] | None = None,
    unbounded: bool = True,
    erase_all_dups: bool = False,
) -> tuple[SynthesisProblem, PfwCSP, str]:
    """Run Stage 0 + Stage 1 + Stage 2 passes and return `(problem, csp, smt2_text)`."""
    prob = parse_nksynth_problem(source, erase_all_dups=erase_all_dups)

    if passes is not None:
        active = set(passes)
    elif preset == "raw":
        active = set()
    elif preset == "generic":
        active = {"subst_seq"}
    elif preset == "noexists":
        active = {"subst_seq", "hole_frame", "elim_exists"}
    elif preset == "ctx":
        active = {"subst_seq", "hole_frame", "hole_context", "elim_exists"}
    elif preset == "proj":
        active = {"subst_seq", "hole_frame", "hole_context", "project_st", "elim_exists"}
    elif preset == "paths":
        active = {"subst_seq", "hole_frame", "elim_exists", "compile_paths"}
    elif preset == "bfs":
        active = {"subst_seq", "hole_frame", "hole_context", "hole_arity", "project_st", "elim_exists", "bfs_wf"}
    elif preset == "all":
        active = {
            "subst_seq",
            "hole_frame",
            "hole_context",
            "hole_arity",
            "project_st",
            "elim_exists",
            "compile_paths",
        }
    else:
        raise TranslateError(f"Unknown preset: {preset}")

    gt = GenericTranslator(
        prob,
        subst_seq=("subst_seq" in active),
        unbounded=unbounded,
        share_left_stars=True,
    )
    csp = gt.run()

    shapes: dict[str, HoleShapeInfo] | None = None
    if "hole_frame" in active or "hole_arity" in active or "hole_context" in active:
        shapes = apply_pass_hole_shape(
            prob,
            csp,
            reduce_arity=("hole_arity" in active),
            use_context=("hole_context" in active),
            unbounded=unbounded,
        )

    if "project_st" in active:
        apply_pass_project_st(csp)

    if "elim_exists" in active:
        apply_pass_elim_exists(csp)

    if "bfs_wf" in active:
        apply_pass_bfs_wf(prob, csp)

    if "compile_paths" in active:
        apply_pass_compile_paths(prob, csp, shapes=shapes, unbounded=unbounded)

    # Final clause equality cleanup if any optimizations enabled
    if active:
        csp.clauses = [
            c
            for c in (simplify_clause_equalities(cl) for cl in csp.clauses)
            if c.body != FALSE and c.head != TRUE
        ]

    header = (
        f"Generated by nksynth_to_pcsat.py (preset={preset if passes is None else 'custom'}, "
        f"passes={sorted(active)}, domain={'unbounded' if unbounded else 'bounded'})"
    )
    return prob, csp, emit_smt2(csp, header_comment=header)


def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("input", type=Path, help="Input `.nksynth` synthesis problem")
    ap.add_argument("-o", "--output", type=Path, help="Output `.smt2` file (default: stdout)")
    ap.add_argument(
        "--preset",
        choices=PRESETS,
        default="all",
        help="Optimization preset (default: all)",
    )
    ap.add_argument(
        "--passes",
        nargs="*",
        choices=[
            "subst_seq",
            "hole_frame",
            "hole_context",
            "hole_arity",
            "project_st",
            "elim_exists",
            "bfs_wf",
            "compile_paths",
        ],
        help="Explicit list of optimization passes (overrides --preset)",
    )
    ap.add_argument(
        "--domain",
        choices=["unbounded", "bounded"],
        default="unbounded",
        help="Integer field domain semantics (default: unbounded)",
    )
    ap.add_argument(
        "--erase-dup",
        action="store_true",
        help="Replace all `dup` occurrences with `1` (pure packet-relation projection)",
    )
    ap.add_argument(
        "--extract-nksol",
        type=Path,
        help="Read PCSat `(define-fun ...)` lines from this file and print `.nksol`",
    )
    args = ap.parse_args()

    source = args.input.read_text(encoding="utf-8")
    _, csp, smt2 = compile_nksynth_to_pcsat(
        source,
        preset=args.preset,
        passes=args.passes,
        unbounded=(args.domain == "unbounded"),
        erase_all_dups=args.erase_dup,
    )

    if args.extract_nksol:
        model_txt = args.extract_nksol.read_text(encoding="utf-8")
        nksol = pcsat_model_to_nksol(csp, model_txt)
        if args.output:
            args.output.write_text(nksol, encoding="utf-8")
        else:
            sys.stdout.write(nksol)
        return

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(smt2, encoding="utf-8", newline="\n")
    else:
        sys.stdout.write(smt2)


if __name__ == "__main__":
    main()
