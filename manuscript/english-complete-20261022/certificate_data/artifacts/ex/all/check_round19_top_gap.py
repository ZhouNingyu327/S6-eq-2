"""Exact scalar checks for the new top-gap argument.

No covering enumeration, angle sampling, interval partition, or placement
optimization.  The geometric provenance is reviewed separately.
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
    x, z, mu, r, T, S4 = z3.Reals("r19_x r19_z r19_mu r19_r r19_T r19_S4")
    rows.append(query("top exterior point and right ray force z < x/(2-x)", [
        x > 0, x < 1, z > 0, z < 1, mu > 1, r > 1-x,
        T == mu-S4, S4 >= 0, S4*(1+z) < 1-z,
        (r+T)**2+mu**2 <= 2, z*(2-x) >= x]))

    delta, L4 = z3.Reals("r19_delta r19_L4")
    rows.append(query("cosine cap gives L4 < 1+Delta(x)", [
        x > 0, x < 1, z > 0, z*(2-x) < x,
        L4*(1-z*z) <= 1+z*z,
        2*(1-x)*delta == x*x, L4 >= 1+delta]))

    S2 = z3.Real("r19_S2")
    rows.append(query("two gap endpoints force x < 1/3", [
        x > 0, x < 1, mu > 1, S2 >= 0, S2*(1+x) < 1-x,
        (2*mu-S2)**2 <= 2, 3*x >= 1]))
    rows.append(query("x < 1/3 implies S2 < 1-Delta", [
        x > 0, 3*x < 1, S2 >= 0, S2*(1+x) < 1-x,
        2*(1-x)*delta == x*x, S2+delta >= 1]))
    rows.append(query("two actual gap endpoints cannot fit the unit diagonal", [
        mu > 1, delta > 0, delta < 1, S2 >= 0, S2 < 1-delta,
        L4 >= 0, L4 < 1+delta,
        (2*mu-S2)**2+(2*mu-L4)**2 <= 2]))

    t, L = z3.Reals("r19_t r19_L")
    corner = [t > 0, t < 1, L > 1, L*L <= 2,
              L*(1-t*t) <= 1+t*t, 2*t*L <= 1+t*t]
    rows.append(query("corner kappa < t", corner + [L-1 >= t*(3-L)]))
    rows.append(query("corner kappa < 1-t", corner + [L-1 >= (1-t)*(3-L)]))

    y = z3.Real("r19_y")
    rows.append(query("new first-order angle relation gives y+Delta < x/2", [
        x > 0, 15*x < 4, y > 0, y*(1-2*x*x) < x*x,
        2*(1-x)*delta == x*x, 2*(y+delta) >= x]))

    w, S1 = z3.Reals("r19_w r19_S1")
    rows.append(query("bottom host S1 < 1-x", [
        x > 0, x < w, w < 1, S1 >= 0, S1*(1+w) < 1-w, S1+x >= 1]))
    j, v, d = z3.Reals("r19_j r19_v r19_d")
    rows.append(query("shared midpoint, W longer: d > x-Delta", [
        mu > 1, delta > 0, x+w < 1, j < w, v <= j, d+j >= mu,
        d <= x-delta], "QF_LRA"))
    rows.append(query("shared midpoint, F longer: d > x-Delta", [
        mu > 1, S1+x < 1, v < S1+delta, v >= j, d+v >= mu,
        d <= x-delta], "QF_LRA"))

    rho = z3.Real("r19_rho")
    rows.append(query("C projection contradicts rho >= x/2", [
        x > 0, 3*x < 1, y >= 0, 2*y <= x, 2*rho >= x, 12*rho <= 5,
        (1-y)**2*rho*(2+rho) <= (x+rho)**2]))

    # A separate remaining case uses the audited round13 adjacent-corner bound.
    h, gT, B, A, D, H, J = z3.Reals("r19_h r19_gT r19_B r19_A r19_D r19_H r19_J")
    L3, U2, U4, S4r, E = z3.Reals("r19_L3 r19_U2 r19_U4 r19_S4r r19_E")
    rows.append(query("top gap, left meeting, F empty forces a long bottom chord", [
        mu > 1, B < 1, E >= 0, h+gT <= B,
        h+H+U2+U4 >= 2*mu, gT == 2*mu-L3-S4r,
        L4+S4r+U4 < 2, L4+D >= 2*mu, A+D+H+J <= 2,
        L3+S2+U2+E < 2,
        A+S2+J+E >= B-6*(mu-1)], "QF_LRA"))

    X, Y, R = sp.symbols("x y rho")
    cap = X/(2-X)
    identities = {
        "new top-to-left angle relation":
            sp.cancel(2*cap**2/(1-cap**2)),
        "Delta(x/3 scale)":
            sp.cancel(X**2/(2*(1-X))/X),
        "angle coefficient sum": sp.Rational(7,6)+sp.Rational(15,22),
    }
    assert sp.cancel(identities["new top-to-left angle relation"]-X**2/(2*(1-X))) == 0
    assert identities["angle coefficient sum"] == sp.Rational(61,33)
    f=(1-X/2)**2*R*(2+R)-(X+R)**2
    a,b=X/2,sp.Rational(5,12)
    identities["F(x/2)"]=sp.factor(f.subs(R,a))
    identities["F(5/12)"]=sp.expand(f.subs(R,b))
    identities["F(5/12) at x=1/3"]=f.subs({R:b,X:sp.Rational(1,3)})
    assert sp.expand(identities["F(x/2)"]-X*(1-3*X+X**3/16)) == 0
    assert sp.expand(identities["F(5/12)"]-(sp.Rational(5,6)
        -sp.Rational(265,144)*X-sp.Rational(431,576)*X**2)) == 0
    assert identities["F(5/12) at x=1/3"] == sp.Rational(709,5184)
    chord=((b-R)*f.subs(R,a)+(R-a)*f.subs(R,b))/(b-a)
    assert sp.cancel(f-chord-((1-X/2)**2-1)*(R-a)*(R-b)) == 0
    identities["concavity chord identity"]="exactly zero"
    identities["short-leg deficit minus Delta"]=sp.factor(
        2*X/(1+X)-X**2/(2*(1-X)))
    assert sp.cancel(identities["short-leg deficit minus Delta"]
        -X*(4-5*X-X**2)/(2*(1-X)*(1+X))) == 0
    constants={
        "sqrt(2) < 3/2": 2*2**2 < 3**2,
        "19 sqrt(2) < 27": 19**2*2 < 27**2,
        "26/15 > sqrt(2)": 26**2 > 2*15**2,
        "225/193 < 7/6": sp.Rational(225,193)<sp.Rational(7,6),
        "244/495 < 1/2": sp.Rational(244,495)<sp.Rational(1,2),
        "sqrt(2)-1 < 5/12": 2*12**2 < 17**2,
        "709/5184 > 0": sp.Rational(709,5184)>0,
    }
    assert all(constants.values())
    result={
        "classification":"exact scalar checks of a hand geometric proof",
        "new_scope":"near G2, C fills top gap: left gap impossible; nonempty F horizontal impossible",
        "remaining_scope":"top C gap requires left/right corner meeting and F horizontal empty",
        "all_queries_unsat":all(row["result"]=="unsat" for row in rows),
        "query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "queries":rows,
        "symbolic_checks":{key:str(value) for key,value in identities.items()},
        "constant_checks":{key:bool(value) for key,value in constants.items()},
        "historical_limit":"the new conditional exclusion has a hand proof; the remaining long-chord condition uses the audited round13 adjacent-corner certificate",
        "not_proved":"the final top-gap empty-horizontal case; other near/far G2; all G2; G3/G4; S(6)=2",
        "no_search":"no point enumeration, angle sampling, interval subdivision, or placement optimization",
    }
    Path(__file__).with_name("round19_top_gap_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)
    assert result["all_queries_unsat"],"Inspect any SAT or UNKNOWN; it does not prove a covering claim."


if __name__=="__main__":
    main()
