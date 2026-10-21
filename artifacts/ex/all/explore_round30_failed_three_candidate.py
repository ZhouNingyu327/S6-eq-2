"""WITHDRAWN candidate: assumes geometrically invalid J<delta(z).

UNSAT here certifies only the stated algebra, not a cover exclusion.
Correct pairs are TOP/H and RIGHT/V, hence J<delta(x).
The saved original result is retained only as an audit diagnostic.
"""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        solver=z3.SolverFor(theory);solver.set(timeout=20000);solver.add(*cs)
        start=time.perf_counter();ans=solver.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        if ans!=z3.unsat:
            row["detail"]=str(solver.model()) if ans==z3.sat else solver.reason_unknown()
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    mu,B,hc,u,J,H,A,D,L1,L2,L4,S1,S2,U1,U2,z,a=z3.Reals(
        "mu B hc u J H A D L1 L2 L4 S1 S2 U1 U2 z a")
    b,f=z3.Reals("b f")
    query("C bottom contact impossible with F horizontal nonempty",[
        mu>1,B<1,12*mu<=8+2*B+2*mu],"QF_LRA")
    query("joint actual W grid and F parallel budget",[
        hc+f+U1+U2+H>=2*mu,b>=2*mu-S1-S2,b+f<=B,
        A+D+H+J<=2,A+L2>=2*mu,D+L4>=2*mu,
        hc<8*mu-B-2-(L2+S2+U2)-(L4+S1+U1)+J],"QF_LRA")
    query("LEFT adjacent lemma strengthens C horizontal chord",[
        mu>1,B<1,U1<a,L2+S2+U2<2,L4+S1+a+2*z-z*z<=2,
        hc>=8*mu-B-2-(L2+S2+U2)-(L4+S1+U1)+J,
        hc<=1+2*z-z*z+J])
    query("original W TOP/V nonempty gives J<delta(z)",[
        mu>1,B<1,z>0,z<1,D+L4>=2*mu,D+J<=B,
        L4*(1-z*z)<=1+z*z,J*(1-z*z)>=2*z*z])
    query("small positive lower u",[
        z>0,6*z<=1,J>=0,J*(1-z*z)<2*z*z,1-z-J<=0])
    query("small J product decreases",[
        z>0,6*z<=1,J>=0,-3*z+z*z-2*J>=0])
    P=z**6-5*z**5+5*z**4+4*z**3-7*z*z-3*z+1
    query("small scalar P6 explicit lower bound",[
        z>=0,6*z<=1,P<z3.Q(2371,7776)])
    query("small entire scalar contradiction",[
        z>0,6*z<=1,J>=0,J*(1-z*z)<2*z*z,
        hc>1+2*z-z*z+J,u>1-z-J,hc*u<=1])
    query("large sum lower bound",[
        6*z>=1,15*z<4,hc>1+2*z-z*z+J,u>1-z-J,
        36*(hc+u)<=77])
    query("large quadratic has positive margin",[
        hc>=1,12*hc<=17,hc*(z3.Q(77,36)-hc)<z3.Q(221,216)])
    query("large entire scalar contradiction",[
        hc>1,12*hc<17,36*(hc+u)>77,hc*u<=1])
    # The triangle-area statement is affine in each square coordinate.
    # Check its determinant bound directly as an independent local theorem.
    x1,y1,x2,y2,x3,y3=z3.Reals("x1 y1 x2 y2 x3 y3")
    coords=[x1,y1,x2,y2,x3,y3]
    det=(x2-x1)*(y3-y1)-(x3-x1)*(y2-y1)
    query("triangle determinant upper bound in one unit square",
          [*[v>=0 for v in coords],*[v<=1 for v in coords],det>1])
    query("triangle determinant lower bound in one unit square",
          [*[v>=0 for v in coords],*[v<=1 for v in coords],det< -1])
    Z,JJ,HH=sp.symbols("z J h")
    delta=2*Z*Z/(1-Z*Z)
    poly=Z**6-5*Z**5+5*Z**4+4*Z**3-7*Z*Z-3*Z+1
    identities=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,name;identities.append(name)
    product=(1+2*Z-Z*Z+JJ)*(1-Z-JJ)
    ident("J derivative",sp.diff(product,JJ)-(-3*Z+Z*Z-2*JJ))
    ident("small product factor",product.subs(JJ,delta)-1-Z*poly/(1-Z*Z)**2)
    ident("sum cancels J",1+2*Z-Z*Z+JJ+1-Z-JJ-(2+Z-Z*Z))
    ident("large quadratic exact margin",
          HH*(sp.Rational(77,36)-HH)-sp.Rational(221,216)-
          (sp.Rational(17,12)-HH)*(HH-sp.Rational(13,18)))
    constants=[]
    def exact(name,expr,expected):
        value=sp.factor(expr);assert value==expected,(name,value)
        constants.append({"name":name,"value":str(value)})
    exact("P6 elementary lower",1-sp.Rational(1,2)-sp.Rational(7,36)-sp.Rational(5,7776),
          sp.Rational(2371,7776))
    exact("z-z² at 1/6",sp.Rational(1,6)-sp.Rational(1,36),sp.Rational(5,36))
    exact("large sum lower",2+sp.Rational(5,36),sp.Rational(77,36))
    exact("quadratic left endpoint",sp.Rational(77,36)-1,sp.Rational(41,36))
    exact("quadratic right endpoint",sp.Rational(17,12)*(sp.Rational(77,36)-sp.Rational(17,12)),
          sp.Rational(221,216))
    exact("rational chord cap square margin",sp.Rational(17,12)**2-2,sp.Rational(1,144))
    result={"queries":rows,"symbolic_identities":identities,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(v["theory"]=="QF_NRA" for v in rows),
                  "LRA":sum(v["theory"]=="QF_LRA" for v in rows),
                  "symbolic_identities":len(identities),"constants":len(constants)},
        "scope":"Far LEFT/TOP/RIGHT all meeting, every nonempty F horizontal trace excluded",
        "historical_input":"round13 adjacent-corner lemma and 266 exact coefficients assumed; own entry not replayed",
        "not_proved":"Far LEFT gap; far RIGHT gap; far three meetings with F H empty; S(6)=2"}
    Path(__file__).with_name("round30_far_three_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
