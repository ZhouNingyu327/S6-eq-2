"""Exact checks for a short analytic exclusion, not a placement search.

The proof is in S6_attack_round17.md.  These queries check individual scalar
lemmas and the symbolic identities in that proof; no angle subdivisions,
sample points, interval tree, or full covering model occur here.
"""
from pathlib import Path
import json
import time

import sympy as sp
import z3


def query(name, assumptions, theory="QF_NRA"):
    solver = z3.SolverFor(theory)
    solver.set(timeout=20000)
    solver.add(*assumptions)
    start = time.perf_counter()
    answer = solver.check()
    row = {"name": name, "theory": theory, "result": str(answer),
           "seconds": time.perf_counter() - start}
    if answer != z3.unsat:
        row["detail"] = str(solver.model()) if answer == z3.sat else solver.reason_unknown()
    return row


def main():
    rows = []
    t, L = z3.Reals("r17_t r17_L")
    corner = [t > 0, t < 1, L > 1, L*L <= 2,
              L*(1-t*t) <= 1+t*t, 2*t*L <= 1+t*t]
    rows.append(query("corner kappa < t", corner + [L-1 >= t*(3-L)]))
    rows.append(query("corner kappa < 1-t", corner + [L-1 >= (1-t)*(3-L)]))

    y, delta = z3.Reals("r17_y r17_delta")
    den = (1-y*y)*(1-3*y*y)
    rows.append(query("cascade delta < y^2", [y > 0, 15*y < 4,
        delta*den == 2*y**4, delta >= y*y]))

    mu, S, L4 = z3.Reals("r17_mu r17_S r17_L4")
    rows.append(query("two gap endpoints exceed the unit diagonal", [mu > 1,
        delta > 0, delta < 1, S >= 0, S <= 1-delta,
        L4 >= 0, L4 <= 1+delta,
        (2*mu-S)**2 + (2*mu-L4)**2 <= 2]))

    x, w = z3.Reals("r17_x r17_w")
    rows.append(query("bottom host short leg S < 1-x", [x > 0, x < w,
        w < 1, S >= 0, S*(1+w) < 1-w, S+x >= 1]))

    j, v, d = z3.Reals("r17_j r17_v r17_d")
    rows.append(query("shared midpoint, W longer: d > x-delta", [mu > 1,
        delta > 0, x+w < 1, j < w, v <= j, d+j >= mu,
        d <= x-delta], "QF_LRA"))
    rows.append(query("shared midpoint, F longer: d > x-delta", [mu > 1,
        S+x < 1, v < S+delta, v >= j, d+v >= mu,
        d <= x-delta], "QF_LRA"))

    rows.append(query("small-angle cascade y+delta < x/2", [x > 0, 3*x < 1,
        y > 0, 5*y < 6*x*x, delta < y*y, 2*(y+delta) >= x]))

    rho = z3.Real("r17_rho")
    rows.append(query("C projection contradicts rho >= x/2", [x > 0, 3*x < 1,
        y >= 0, 2*y <= x, 2*rho >= x, 12*rho <= 5,
        (1-y)**2*rho*(2+rho) <= (x+rho)**2]))

    # These identities are also checked algebraically in the written proof.
    X, R, C, H, M, E, RR, UU = sp.symbols("x rho c s mu e r u")
    f = (1-X/2)**2*R*(2+R)-(X+R)**2
    a, b = X/2, sp.Rational(5, 12)
    identities = {
        "F(x/2)": sp.factor(f.subs(R, a)),
        "F(5/12)": sp.expand(f.subs(R, b)),
        "F(5/12) at x=1/3": f.subs({R: b, X: sp.Rational(1, 3)}),
        "quadratic coefficient": sp.expand(f).coeff(R, 2),
    }
    assert sp.expand(identities["F(x/2)"]-X*(1-3*X+X**3/16)) == 0
    assert sp.expand(identities["F(5/12)"]-(sp.Rational(5,6)
        -sp.Rational(265,144)*X-sp.Rational(431,576)*X**2)) == 0
    assert identities["F(5/12) at x=1/3"] == sp.Rational(709,5184)
    chord = ((b-R)*f.subs(R,a)+(R-a)*f.subs(R,b))/(b-a)
    assert sp.cancel(f-chord-((1-X/2)**2-1)*(R-a)*(R-b)) == 0
    identities["concavity chord identity"] = "exactly zero"

    first = C*(M+RR)-H*E
    second = H*M+C*(E+UU)
    assert sp.expand(C*first+H*second
        -((C*C+H*H)*M+C*C*RR+C*H*UU)) == 0
    identities["exterior-point elimination"] = "exactly zero"

    Y, Z = sp.symbols("y z")
    g = Y**2/(1-2*Y**2)
    assert sp.cancel((1+g*g)/(1-g*g)-1
        -2*Y**4/((1-Y**2)*(1-3*Y**2))) == 0
    identities["top-to-left cascade identity"] = "exactly zero"

    exact = {
        "19 sqrt(2) < 27": 19**2*2 < 27**2,
        "sqrt(2)-1 < 5/12": 2*12**2 < 17**2,
        "26/15 > sqrt(2)": 26**2 > 2*15**2,
        "193/225 > 5/6": sp.Rational(193,225) > sp.Rational(5,6),
        "34/75 < 1/2": sp.Rational(34,75) < sp.Rational(1,2),
        "709/5184 > 0": sp.Rational(709,5184) > 0,
    }
    assert all(exact.values())
    result = {
        "classification": "exact checks of scalar steps in an analytic proof",
        "scope": "near G2, right/top corner meeting, F on negative horizontal half-axis",
        "all_queries_unsat": all(row["result"] == "unsat" for row in rows),
        "queries": rows,
        "query_count": len(rows),
        "NRA_queries": sum(row["theory"] == "QF_NRA" for row in rows),
        "LRA_queries": sum(row["theory"] == "QF_LRA" for row in rows),
        "symbolic_checks": {key: str(value) for key,value in identities.items()},
        "rational_checks": {key: bool(value) for key,value in exact.items()},
        "no_search": "no covering-point enumeration, angle sampling, interval subdivision, or placement optimization",
        "dependency_limit": "whole-branch closure also uses the audited round13 three-meeting theorem",
        "not_proved": "positive horizontal phase; all G2; G3/G4; S(6)=2",
    }
    target = Path(__file__).with_name("round17_analytic_negative_checks.json")
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(result, ensure_ascii=False, indent=2))
    assert result["all_queries_unsat"], "A scalar check failed or timed out; inspect the result."


if __name__ == "__main__":
    main()
