"""Exact checks of a hand proof for the positive-horizontal residual branch.

No placement search, point sampling, or interval subdivision.  The written
proof supplies the geometric ownership of endpoints.
"""
from pathlib import Path
import json
import time

import sympy as sp
import z3


def query(name, assumptions, theory="QF_NRA"):
    p = z3.SolverFor(theory)
    p.set(timeout=20000)
    p.add(*assumptions)
    start = time.perf_counter()
    a = p.check()
    row = {"name": name, "theory": theory, "result": str(a),
           "seconds": time.perf_counter()-start}
    if a != z3.unsat:
        row["detail"] = str(p.model()) if a == z3.sat else p.reason_unknown()
    return row


def main():
    c,s,y = z3.Reals("r18_c r18_s r18_y")
    rows = [query("C positive principal rotation cannot contain left/up points",
        [c>=s, s>=0, c*c+s*s==1, y>0, 15*y<4, c+s*(1-y)<1])]
    h = z3.Real("r18_h")
    rows.append(query("C negative rotation: half-angle h < y/(2-y)",
        [h>0, h<1, y>0, y<1,
         2*h+(1-h*h)*(1-y)<1+h*h, h*(2-y)>=y]))

    delta,rho,q,r = z3.Reals("r18_delta r18_rho r18_q r18_r")
    rows.append(query("C right-ray bound is less than y^2",
        [y>0, 15*y<4, delta>=0, delta<y*y,
         rho>=0, 2*(1-y)*rho<=y*y,
         q>=0, 2*(1-y)*q<=y*(2-y),
         r<=rho+q*delta, r>=y*y]))

    x,w,D,S = z3.Reals("r18_x r18_w r18_D r18_S")
    rows.append(query("bottom meeting would make W left leg D < 1-x",
        [x>0, x<w, w<1, S>=D, S*(1+w)<1-w, D>=1-x]))

    mu,L4,g,u,d = z3.Reals("r18_mu r18_L4 r18_g r18_u r18_d")
    rows.append(query("C left/vertical traces force W left leg D > 1-y-delta",
        [mu>1, L4<1+delta, g==2*mu-L4-D, g>0,
         u>1-y, d>=0, g+u+d<1, D<=1-y-delta], "QF_LRA"))

    rows.append(query("bottom meeting scalar bounds are incompatible",
        [x>0, 2*(y+delta)<x, D>1-y-delta, D<1-x], "QF_LRA"))

    rows.append(query("small-angle cascade y+delta < x/2",
        [x>0, 3*x<1, y>0, 5*y<6*x*x, delta<y*y,
         2*(y+delta)>=x]))

    # The final positive budget holds for the entire x in (0,1), not only
    # the hypothetical small x in the already-rejected bottom-meeting case.
    rows.append(query("residual budget: y^2 < x(1-x)/(1+x)",
        [x>0, x<1, y>0, y<x, y<1-x, 15*y<4,
         y*y*(1+x)>=x*(1-x)]))
    b,rr,alpha = z3.Reals("r18_b r18_rr r18_alpha")
    rows.append(query("F bottom/horizontal lengths exceed one",
        [x>0, x<1, y>0, y*y*(1+x)<x*(1-x),
         b*(1+x)>2*x, rr>1-x, alpha<y*y,
         b+rr-alpha<=1]))

    Y,H = sp.symbols("y h")
    half_limit=Y/(2-Y)
    rho_h=2*H**2/(1-H**2)
    q_h=2*H/(1-H**2)
    symbolic = {}
    assert sp.cancel(rho_h.subs(H,half_limit)-Y**2/(2*(1-Y)))==0
    symbolic["rho at half-angle cap"]="exact identity"
    assert sp.cancel(q_h.subs(H,half_limit)-Y*(2-Y)/(2*(1-Y)))==0
    symbolic["s/c at half-angle cap"]="exact identity"
    assert sp.expand(2*H+(1-H**2)*(1-Y)-(1+H**2)
        -(1-H)*(H*(2-Y)-Y)) == 0
    symbolic["C rotation factorization"]="exact identity"
    A=Y**2*(1+2*Y-Y**2)/(2*(1-Y))
    assert sp.cancel(Y**2-A-Y**2*(1-4*Y+Y**2)/(2*(1-Y)))==0
    symbolic["C right-ray margin factorization"]="exact identity"
    X=sp.symbols("x")
    assert sp.cancel(2*X/(1+X)+1-X-1-X*(1-X)/(1+X))==0
    symbolic["F total trace budget identity"]="exact identity"
    M,E,T=sp.symbols("mu e t")
    assert sp.expand(sp.det(sp.Matrix([[M,E],[-T,M]]))-M*M-E*T)==0
    symbolic["right-upper/top-left residual triangle"]="exact identity"
    assert sp.expand(sp.det(sp.Matrix([[-T,M],[-M,-E]]))-M*M-E*T)==0
    symbolic["top-left/left-lower residual triangle"]="exact identity"
    exact = {
        "positive cap polynomial at y=4/15": str(
            (1-4*Y+Y**2).subs(Y,sp.Rational(4,15))),
        "4/15 < 1/3": bool(sp.Rational(4,15)<sp.Rational(1,3)),
        "4/15 < 1/2": bool(sp.Rational(4,15)<sp.Rational(1,2)),
    }
    assert exact["positive cap polynomial at y=4/15"]=="1/225"
    assert exact["4/15 < 1/3"] and exact["4/15 < 1/2"]
    result = {
        "classification":"scalar and identity checks of an analytic branch exclusion",
        "scope":"near G2 right/top meeting with F positive horizontal nonempty",
        "all_queries_unsat":all(row["result"]=="unsat" for row in rows),
        "queries":rows, "query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "symbolic_checks":symbolic, "constant_checks":exact,
        "no_search":"no placement enumeration, angle sampling, or subdivision",
        "not_proved":"other near meeting patterns; remaining far G2; entire G2; G3/G4; S(6)=2",
    }
    path=Path(__file__).with_name("round18_positive_projection_checks.json")
    path.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))
    assert result["all_queries_unsat"]


if __name__=="__main__":
    main()
