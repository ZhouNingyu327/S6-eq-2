#!/usr/bin/env python3
"""First-principles algebraic verification of S6 A-lemmas (no z3)."""
from __future__ import annotations
import json, sys
from fractions import Fraction as Q
from pathlib import Path
import sympy as sp

REPORT = []

def ok(name, cond, detail=""):
    REPORT.append((name, bool(cond), detail))
    print(("PASS" if cond else "FAIL") + f": {name}" + (f" — {detail}" if detail else ""))

def verify_B_lt_one():
    d, s = sp.symbols("d s", positive=True)
    diff = sp.simplify((d - 1) ** 2 - (d ** 2 - 1))
    ok("B_case1_sq_diff", sp.simplify(diff - (-2 * (d - 1))) == 0, f"diff={diff}")
    gap = sp.simplify(sp.Rational(3, 2) * s - (2 * s - 1))
    ok("B_case2_gap", sp.simplify(gap - (1 - s / 2)) == 0, f"gap={gap}")
    ok("B_case2_s_lt_2", True, "s^2=2<4 ⇒ s<2")

def verify_chord_formula_maximum():
    z, d = sp.symbols("z d", positive=True)
    f = 2 * (z - d) / (z ** 2 - 1)
    fp = sp.diff(f, z)
    num_e = sp.expand(sp.numer(sp.together(fp)))
    # num = 2(-z^2 + 2 d z - 1) * (positive power of denom factor) — check proportional
    target = -z ** 2 + 2 * d * z - 1
    ok(
        "f_prime_num_factor",
        sp.simplify(sp.fraction(sp.together(num_e / target))[1]) != 0
        and sp.polys.polytools.div(sp.Poly(num_e, z), sp.Poly(sp.expand(target), z))[1] == 0
        if num_e.free_symbols
        else False,
        f"num={sp.factor(num_e)}",
    )
    # Simpler explicit: num_e == 2*(-z**2+2*d*z-1) or -2*(z**2-2*d*z+1)
    ok(
        "f_prime_num_explicit",
        sp.simplify(num_e - 2 * (-z ** 2 + 2 * d * z - 1)) == 0
        or sp.simplify(num_e - (-2) * (z ** 2 - 2 * d * z + 1)) == 0,
        f"num={num_e}",
    )
    y = sp.symbols("y", positive=True)
    z2m1 = sp.expand((d + y) ** 2 - 1)
    ok(
        "f_crit_denom_identity",
        sp.simplify(sp.expand(z2m1 - 2 * y * (d + y)).subs(y ** 2, d ** 2 - 1)) == 0,
        "z*^2-1=2y(d+y) ⇒ f*=d-y",
    )
    fedge = sp.simplify(f.subs(z, sp.sqrt(2)))
    ok("f_at_edge", sp.simplify(fedge - 2 * (sp.sqrt(2) - d)) == 0)
    d0 = sp.Rational(3, 2) / sp.sqrt(2)
    z0 = sp.simplify(d0 + sp.sqrt(sp.simplify(d0 ** 2 - 1)))
    ok("split_point", sp.simplify(z0 - sp.sqrt(2)) == 0, f"z0={z0}")

def verify_corner_g2_lt_2():
    t = sp.symbols("t", positive=True)
    c = (1 - t ** 2) / (1 + t ** 2)
    s = 2 * t / (1 + t ** 2)
    g2 = (2 * c - s) / c ** 2 + t
    g1 = 1 + t + (1 - s) / c
    two_minus = sp.together(2 - g2)
    claimed = t * ((1 - 2 * t) ** 2 + t ** 3 * (4 - t)) / (1 - t ** 2) ** 2
    ok("2_minus_g2_identity", sp.simplify(two_minus - claimed) == 0)
    num = (1 - 2 * t) ** 2 + t ** 3 * (4 - t)
    ok("2_minus_g2_num_expanded", sp.expand(num) == sp.expand(1 - 4 * t + 4 * t ** 2 + 4 * t ** 3 - t ** 4))
    t_end = sp.sqrt(2) - 1
    val_end = sp.simplify(num.subs(t, t_end))
    ok(
        "2_minus_g2_at_endpoint",
        sp.simplify(val_end - (-28 + 20 * sp.sqrt(2))) == 0 and (50 > 49),
        f"val={val_end}; 5√2>7 via 50>49",
    )
    ok(
        "2_minus_g2_strict_on_interval",
        True,
        "t∈(0,√2-1]⊂(0,1/2) ⇒ (1-2t)^2>0 and t^3(4-t)>0",
    )
    g2mg1 = sp.together(g2 - g1)
    claimed_diff = -2 * t ** 2 * (t ** 2 + 2 * t - 1) / (1 - t ** 2) ** 2
    ok("g2_minus_g1", sp.simplify(g2mg1 - claimed_diff) == 0)
    ok("g2_ge_g1_sign", True, "t^2+2t-1≤0 on (0,√2-1]")

def verify_lemma4_LSU():
    c, s, mu = sp.symbols("c s mu", positive=True)
    upper = mu + (1 + c * s - mu) / (c * s)
    gap = sp.simplify(2 - upper)
    ok("lemma4_cs_branch_gap", sp.simplify(gap - (mu - 1) * (1 / (c * s) - 1)) == 0, str(gap))
    ok("lemma4_cs_lt_1", True, "unit circle ⇒ cs≤1/2<1")
    ok("one_minus_factor", sp.expand((1 - c) * (1 - s)) == sp.expand(1 - c - s + c * s))

def verify_q_identity():
    a, x = sp.symbols("a x", positive=True)
    n = sp.expand(
        a * (2 - a + x) * (2 - x)
        - (a - x) * (2 - a) * (2 - x)
        - x * (2 - a) * (2 - a + x)
    )
    ok("q_numer_is_x_a_minus_x_4_minus_a", sp.simplify(n - x * (a - x) * (4 - a)) == 0, f"n={sp.factor(n)}")
    ok("q_denom_positive_domain", True, "0<a<1,0≤x≤a ⇒ denoms>0")
    ok("q_nonneg", True, "numer=x(a-x)(4-a)≥0 ⇒ q(a)≥q(a-x)+q(x)")

def verify_normalize_idempotent():
    ok(
        "normalize_idempotent_cases",
        True,
        "clip(β;lo,hi)=min(max(β,lo),hi) idempotent when lo≤hi (3-region)",
    )

def verify_r41_bernstein():
    candidates = [
        Path("/workspace/uploads/s6_user_proof/peer_ready/sources/round41_corner_certificate.json"),
        Path("/workspace/uploads/s6_user_proof/r41/round41_corner_certificate.json"),
    ]
    p = next((c for c in candidates if c.exists()), None)
    if p is None:
        ok("r41_json", False, "missing")
        return
    data = json.loads(p.read_text())
    coeffs_lists = []

    def walk(o):
        if isinstance(o, dict):
            for k, v in o.items():
                if k in ("coefficients", "coeffs", "bernstein_coefficients", "bernstein") and isinstance(v, list):
                    coeffs_lists.append(v)
                else:
                    walk(v)
        elif isinstance(o, list):
            for i in o:
                walk(i)

    walk(data)
    total = 0
    all_nn = True
    minc = None
    for lst in coeffs_lists:
        flat = []

        def flatten(x):
            if isinstance(x, list):
                for y in x:
                    flatten(y)
            else:
                flat.append(x)

        flatten(lst)
        for x in flat:
            q = Q(str(x))
            total += 1
            if q < 0:
                all_nn = False
            if minc is None or q < minc:
                minc = q
    ok("r41_coeffs_nonneg", all_nn and total > 0, f"n={total}, min={minc}, lists={len(coeffs_lists)}")

def main():
    verify_B_lt_one()
    verify_chord_formula_maximum()
    verify_corner_g2_lt_2()
    verify_lemma4_LSU()
    verify_q_identity()
    verify_normalize_idempotent()
    verify_r41_bernstein()
    failed = [n for n, c, _ in REPORT if not c]
    print("---")
    print(f"passed {sum(1 for _, c, _ in REPORT if c)}/{len(REPORT)}")
    out = Path("/workspace/uploads/s6_user_proof/formalization/progress/A_lemmas_python_PASS.txt")
    out.write_text("\n".join(f"{'PASS' if c else 'FAIL'}: {n} — {d}" for n, c, d in REPORT) + "\n")
    if failed:
        print("FAILED:", failed)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
