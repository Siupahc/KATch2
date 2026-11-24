"""Emit the generic hospital SMT-LIB with optional CoAR candidate atoms."""

import argparse
from pathlib import Path


def declaration(predicate, atoms, progress=False):
    # (s,i,d,t) is the input packet, (b,j,e,u) the output.
    # For W_, (r,k,f,v) and (c,l,g,w) are the next pair of packets.
    fields = "s i d t b j e u"
    if progress:
        fields += " r k f v c l g w"
    parameters = " ".join(f"({name} Int)" for name in fields.split())
    return f"(set-info :candidates ({predicate} ({parameters})\n  ({' '.join(atoms)})))"


def candidates(profile):
    frame = ["(= d e)", "(= t u)"]
    values = ["(= s 2)", "(= b 2)", "(= j 2)", "(= j 3)",
              "(= d 3)", "(= d 4)", "(= t 21)"]
    if profile == "structural":
        return [declaration("X", frame + values),
                declaration("D", frame + ["(= s b)", "(= i j)", "(= b d)"]),
                declaration("St", frame + ["(= s 1)", "(= i 1)", "(= b 3)", "(= u 21)"])]

    # A witness-informed diagnostic. From ingress, the required paths are
    # G -> S -> destination. Identity closes the induction for D.
    route = "(or (and (= d 4) (= j 3)) (and (= d 3) (distinct t 21) (= j 2)))"
    hole = f"(and (= s 2) (= b 2) (= d e) (= t u) {route})"
    safe = "(not (and (= s 1) (= i 1) (= b 3) (= u 21)))"
    if profile == "projected":
        # This stronger invariant only refers to fields kept in St_shared.
        safe = "(not (and (= s 1) (= b 3) (= u 21)))"
    # Fixed policies never send a packet to M directly and X guards that port.
    identity = "(and (= s b) (= i j) (= d e) (= t u))"
    path = ("(and (or (= s 1) (= s 2)) (= i 1) (= j 1) (= b d) "
            "(= d e) (= t u) (or (= d 4) (and (= d 3) (distinct t 21))))")
    rank = "(or (and (= s 1) (= r 2)) (and (= s 2) (or (= r 3) (= r 4))))"
    return [declaration("X", [hole]), declaration("St", [safe]),
            declaration("D", [f"(or {identity} {path})"]),
            declaration("W_", [rank], progress=True)]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", choices=["structural", "witness", "projected"])
    args = parser.parse_args()
    source = Path(__file__).with_name("hospital_generic.smt2").read_text()
    before, check, after = source.partition("(check-sat)")
    if not check:
        parser.error("missing check-sat in generic encoding")
    print(before + "\n".join(candidates(args.profile)) + "\n" + check + after, end="")
