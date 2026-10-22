"""Exact checks for the hand lower bound J>t4/3 in remaining diagonal G4."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def query(name, premises, theory="QF_NRA"):
    solver=z3.SolverFor(theory)
    solver.set(timeout=30000)
    solver.add(*premises)
    start=time.perf_counter()
    answer=solver.check()
    row={"name":name,"theory":theory,"result":str(answer),
        "seconds":time.perf_counter()-start}
    if answer!=z3.unsat:
        row["detail"]=str(solver.model()) if answer==z3.sat else solver.reason_unknown()
    return row


def main():
    rows=[]
    x,J,z,mu,c,s,u,h,r,d=z3.Reals("a21_x a21_J a21_z a21_mu a21_c a21_s a21_u a21_h a21_r a21_d")
    base=[x>0,15*x<4,J>=0,3*J<=x,z==x+J,mu>1]
    normals=[c>0,s>0,c>=s,c*c+s*s==1]
    rows.append(query("small floating J gives u>29/45",base+[u>1-z,45*u<=29],"QF_LRA"))
    rows.append(query("small floating J excludes C positive orientation",
        base+normals+[u>1-z,c*mu+s*u<=1]))
    rows.append(query("negative C orientation gives h<z/(2-z)",
        base+normals+[u>1-z,s*mu+c*u<=1,h*(1+c)==s,(2-z)*h>=z]))
    delta=z3.Real("a21_delta")
    rows.append(query("r<Delta(z)",
        base+[h>=0,(2-z)*h<z,2*(1-z)*delta==z*z,
            (1-h*h)*(mu+r)<=1+h*h,r>=delta]))
    L2,L4,S2,U2,A,D,H=z3.Reals("a21_L2 a21_L4 a21_S2 a21_U2 a21_A a21_D a21_H")
    cosine_excess=z3.Real("a21_cosine_excess")
    rows.append(query("real top/right meets and positive axis give S2+J<cosine_excess+r",[
        mu>1,A+L4>=2*mu,D+L2>=2*mu,
        A+D+H+J<=2,r+H+U2>=mu,
        L2+S2+U2<2,L4<=1+cosine_excess,
        S2+J>=cosine_excess+r],"QF_LRA"))
    rows.append(query("2x^2/(1-x^2)<(120/209)x",[
        x>0,15*x<4,cosine_excess*(1-x*x)==2*x*x,
        209*cosine_excess>=120*x]))
    rows.append(query("Delta(z)<(32/87)x for z<=4x/3",
        base+[2*(1-z)*delta==z*z,87*delta>=32*x]))
    q=z3.Real("a21_q")
    rows.append(query("q>6x/(2+3x)>(15/7)x",[
        x>0,15*x<4,q*(2+3*x)>6*x,7*q<=15*x]))
    # Gamma=z/(2-z). The square term is evaluated at Gamma, not at actual d.
    gamma,psi=z3.Reals("a21_gamma a21_psi")
    rows.append(query("Gamma^2-z^2 identity and psi bound",
        base+[gamma*(2-z)==z,psi*(2-z)**2==z*z*(1-z),1369*psi>=240*x]))
    rows.append(query("S2+2d-d^2<q from the joint floating bound",
        base+[d>=0,(2-z)*d<z,
            cosine_excess*(1-x*x)==2*x*x,
            2*(1-z)*delta==z*z,
            S2+J<cosine_excess+delta,q*(2+3*x)>6*x,
            S2+2*d-d*d>=q]))
    b,v=z3.Reals("a21_b a21_v")
    rows.append(query("bottom chord and vertical ray contradict unit parabolic budget",[
        d>=0,d<1,v>1-d,b>1+q-S2,S2+2*d-d*d<q,b+v*v<=2]))

    X,Z=sp.symbols("x z")
    Gamma=Z/(2-Z)
    assert sp.cancel(2*Gamma-Gamma*Gamma-Z-Z*Z*(1-Z)/(2-Z)**2)==0
    assert sp.cancel(2*(Z/(2-Z))**2/(1-(Z/(2-Z))**2)-Z*Z/(2*(1-Z)))==0
    coefficient=sp.Rational(120,209)+sp.Rational(32,87)+1+sp.Rational(240,1369)
    margin=sp.Rational(15,7)-coefficient
    assert margin>0
    constants={
        "4/3 *4/15 =16/45":sp.Rational(4,3)*sp.Rational(4,15)==sp.Rational(16,45),
        "29/45 >sqrt(2)-1":sp.Rational(29,45)>sp.sqrt(2)-1,
        "15/7 minus joint coefficient positive":margin>0,
        "8/37 <1":sp.Rational(8,37)<1,
    }
    assert all(constants.values())
    result={"status":"all exact checks passed" if all(row["result"]=="unsat" for row in rows) else "inspect",
        "queries":rows,"query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "symbolic_identity_checks":2,"constant_checks":{key:bool(value) for key,value in constants.items()},
        "joint_coefficient":str(coefficient),"positive_margin":str(margin),
        "scope":"Remaining G4 diagonal (top TL/right BR), nonpositive F horizontal: J>t4/3",
        "historical_round13_pair_certificate_needed_for_new_bound":False,
        "no_search":"no poses, target points, angle sampling or interval partition",
        "not_proved":"J>t4/3 remainder; other G4 representative; remaining G2/G3; S(6)=2"}
    Path(__file__).with_name("round21_floating_lower_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)
    assert result["status"]=="all exact checks passed"


if __name__=="__main__":
    main()
