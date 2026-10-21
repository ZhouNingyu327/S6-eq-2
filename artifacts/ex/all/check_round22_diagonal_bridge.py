"""Exact small-lemma checks for excluding the full G4 diagonal representative."""
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
    mu,c,s,K,r,u,XX,YY=z3.Reals("b22_mu b22_c b22_s b22_K b22_r b22_u b22_Xmax b22_Ymax")
    rows.append(query("a corner's positive facet gives K<1",[
        mu>1,c>0,s>0,c*c+s*s==1,K*c*s==c+s-mu,K>=1]))
    rows.append(query("corner cannot bridge both positive axes past C",[
        mu>1,K<1,XX+YY==K,r>=mu-XX,u>=mu-YY,mu+r+u<2],"QF_LRA"))
    x,d,S2,q,b,v,delta,Delta=z3.Reals("b22_x b22_d b22_S2 b22_q b22_b b22_v b22_delta b22_Delta")
    rows.append(query("C contains qU: joint bottom contradiction",[
        x>0,15*x<4,d>=0,(2-x)*d<x,
        delta*(1-x*x)==2*x*x,2*(1-x)*Delta==x*x,
        S2<delta+Delta,7*q>15*x,
        b>1+q-S2,v>1-d,b+v*v<=2]))
    rows.append(query("C contains qU: 2d upper coefficient",[
        x>0,15*x<4,(2-x)*d<x,13*(2*d)>=15*x]))
    rows.append(query("C contains qU: joint coefficient is below 15/7",[
        x>0,S2<z3.RealVal("120/209")*x+z3.RealVal("2/11")*x,
        2*d<z3.RealVal("15/13")*x,7*q>15*x,S2+2*d>=q],"QF_LRA"))
    k,J,z,L2,D,B,sqrt2=z3.Reals("b22_k b22_J b22_z b22_L2 b22_D b22_B b22_sqrt2")
    rows.append(query("qR in C plus horizontal diameter gives k<3/7",[
        mu>1,sqrt2>0,sqrt2*sqrt2==2,r+mu<=sqrt2,k<r,7*k>=3]))
    dk=z3.Real("b22_dk")
    rows.append(query("right meet and real nonempty parallel traces give J<Delta(k)",[
        mu>1,B<1,D+J<=B,D+L2>=2*mu,L2<=1+dk,J>=dk],"QF_LRA"))
    rows.append(query("k<3/7 gives Delta(k)<9/56",[
        k>0,7*k<3,2*(1-k)*dk==k*k,56*dk>=9]))
    rows.append(query("x+J<359/840<3/7",[
        x>0,15*x<4,J<z3.RealVal("9/56"),z==x+J,7*z>=3],"QF_LRA"))
    rows.append(query("vertical coverage forces u>4/7",[
        mu>1,z<z3.RealVal("3/7"),u>1-z,7*u<=4],"QF_LRA"))
    normal=[c>0,s>0,c>=s,c*c+s*s==1,mu>1]
    rows.append(query("C positive rotation excluded by u>4/7",normal+[
        7*u>4,c*mu+s*u<=1]))
    h=z3.Real("b22_h")
    rows.append(query("C negative rotation yields half angle bound from real u",normal+[
        z>0,7*z<3,u>1-z,s*mu+c*u<=1,h*(1+c)==s,(2-z)*h>=z]))
    dz=z3.Real("b22_dz")
    rows.append(query("C actual right ray is <Delta(z)",[
        z>0,7*z<3,mu>1,h>=0,(2-z)*h<z,
        2*(1-z)*dz==z*z,
        (1-h*h)*(mu+r)<=1+h*h,r>=dz]))
    t,dt=z3.Reals("b22_t b22_dt")
    rows.append(query("Delta(t)<3t/8 on 0<t<3/7",[
        t>0,7*t<3,2*(1-t)*dt==t*t,8*dt>=3*t]))
    rows.append(query("feedback lower/upper floating length contradiction",[
        x>0,3*J>x,z==x+J,8*J<3*k,k<r,8*r<3*z],"QF_LRA"))
    rows.append(query("entire qR scalar chain is inconsistent",[
        x>0,15*x<4,k>0,7*k<3,J>0,3*J>x,z==x+J,
        2*(1-k)*dk==k*k,J<dk,
        2*(1-z)*dz==z*z,k<r,r<dz,z<1]))

    C,S,M=sp.symbols("c s mu",positive=True)
    Xmax=(1-S*M)/C
    Ymax=(1-C*M)/S
    KK=(C+S-M)/(C*S)
    residual=M*(1-C*C-S*S)/(C*S)
    assert sp.cancel(Xmax+Ymax-KK-residual)==0
    T=sp.symbols("t")
    assert sp.cancel(2*(T/(2-T))**2/(1-(T/(2-T))**2)-T*T/(2*(1-T)))==0
    y,kSym=sp.symbols("y k")
    assert sp.cancel((1+(1-kSym)**2)/(2*(1-kSym))-1-kSym*kSym/(2*(1-kSym)))==0
    assert sp.expand((1-C)*(1-S)-(1-C-S+C*S))==0
    coefficient=sp.Rational(120,209)+sp.Rational(2,11)+sp.Rational(15,13)
    constants={
        "qU joint coefficient below 15/7":coefficient<sp.Rational(15,7),
        "sqrt(2)-1 <3/7":2*7**2<10**2,
        "4/7 >sqrt(2)-1":2*7**2<11**2,
        "Delta(3/7)=9/56":sp.Rational(3,7)**2/(2*(1-sp.Rational(3,7)))==sp.Rational(9,56),
        "4/15+9/56=359/840<3/7":
            sp.Rational(4,15)+sp.Rational(9,56)==sp.Rational(359,840)
            and sp.Rational(359,840)<sp.Rational(3,7),
        "9/64<1/4":sp.Rational(9,64)<sp.Rational(1,4),
    }
    assert all(constants.values())
    result={"status":"all exact checks passed" if all(row["result"]=="unsat" for row in rows) else "inspect",
        "queries":rows,"query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "symbolic_identity_checks":4,
        "constant_checks":{key:bool(value) for key,value in constants.items()},
        "qU_positive_margin":str(sp.Rational(15,7)-coefficient),
        "corner_identity_condition":"Xmax+Ymax-K has residual mu*(1-c^2-s^2)/(cs), zero on the unit circle.",
        "scope":"Full G4 diagonal top TL/right BR excluded, including empty and negative F horizontal; positive case inherited.",
        "proof_method":"actual corner bridge endpoints force qU or qR into C; bottom chord contradiction and complementary-angle feedback",
        "free_corner_standardization_needed":False,
        "new_core_round13_pair_certificate_needed":False,
        "no_search":"no poses, target points, angle samples or interval partition",
        "not_proved":"same-side G4 top TR/right BR; remaining G2/G3; S(6)=2"}
    Path(__file__).with_name("round22_diagonal_bridge_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)
    assert result["status"]=="all exact checks passed"


if __name__=="__main__":
    main()
