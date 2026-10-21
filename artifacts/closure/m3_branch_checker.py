#!/usr/bin/env python3
"""Structural coverage check for near-end G2 branch table (M3.1).

Not a geometric proof. Checks Boolean coverage of
(RIGHT/TOP, LEFT, F-horizontal) including explicitly impossible cells.
"""
from itertools import product

# Live closing rows from REVIEW_addendum_nearend / M3_branch_table
LIVE = [
    ("both_touch", "touch", "nonempty", "R13"),
    ("both_touch", "gap", "empty", "R14"),
    ("both_touch", "touch", "empty", "R16"),
    ("both_touch", "gap", "neg", "R17"),
    ("both_touch", "gap", "pos", "R18"),
    ("top_gap", "gap", "empty_or_neg", "R19.1-6"),
    ("top_gap", "touch", "nonempty", "R19.7"),
    ("top_gap", "touch", "empty", "R26"),
    ("right_gap", "any", "all_F", "R27/R28"),
]

# Explicitly impossible cells (must be listed so the grid is accounted for)
IMPOSSIBLE = [
    ("both_gap", "any", "all_F", "R18.7: triangle area"),
    ("top_gap", "gap", "pos", "R19: no positive F-section when LEFT also gapped"),
]

def expand(rt, left, f):
    rts = ["both_touch", "top_gap", "right_gap", "both_gap"] if rt == "any" else [rt]
    lefts = ["touch", "gap"] if left == "any" else [left]
    if f == "nonempty":
        fs = ["pos", "neg"]
    elif f == "empty_or_neg":
        fs = ["empty", "neg"]
    elif f == "all_F":
        fs = ["empty", "pos", "neg"]
    else:
        fs = [f]
    return {(r, l, ff) for r in rts for l in lefts for ff in fs}

def main():
    live=set(); imp=set()
    for rt,left,f,_ in LIVE:
        live |= expand(rt,left,f)
    for rt,left,f,_ in IMPOSSIBLE:
        imp |= expand(rt,left,f)
    overlap = live & imp
    if overlap:
        raise SystemExit(f"FAIL: live/impossible overlap {overlap}")
    allowed = {(rt,left,ff)
               for rt,left,ff in product(
                   ["both_touch","top_gap","right_gap","both_gap"],
                   ["touch","gap"],
                   ["empty","pos","neg"])}
    covered = live | imp
    missing = allowed - covered
    extra = covered - allowed
    print("allowed", len(allowed), "live", len(live), "impossible", len(imp))
    print("missing", missing)
    print("extra", extra)
    if missing or extra:
        raise SystemExit("FAIL")
    print("PASS: M3.1 Boolean grid covered (live + explicit impossible)")

if __name__ == "__main__":
    main()
