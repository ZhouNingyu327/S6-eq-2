"""Exact convexity certificate for far TOP positive C, without layout search."""
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
    h,E,mu,c,s,l,r,d,L,U1,S1,S4,z,t=z3.Reals(
        "h E mu c s l r d L U1 S1 S4 z t")
    norm=[mu>1,c>=s,s>0,c*c+s*s==1,h*(1+c)==s]
    q=lambda x:x/(2-x);g=lambda x:(1-x)/(1+x)
    query("TOP actual P/left gives l+E<G",norm+[
        E>=0,c*(E+l)+s*mu<=1,(l+E)*(1+h)>=1-h])
    query("TOP actual P/right gives r<h+E",norm+[
        E>=0,c*mu+s*(r-E)<=1,r>=h+E])
    query("LEFT meeting forces E<32/209",[
        mu>1,z>0,15*z<4,E==L-mu,
        L*(1-z*z)<=1+z*z,209*E>=32])
    query("long-leg short bound implies S4<1-3E",[
        E>0,6*E<=1,t>0,t*t==E*(2+E),
        S4<=(1+E)*(1-t),S4+3*E>=1])
    query("actual LEFT joint corner budget gives S1<l-3E",[
        mu>1,l>=mu-U1,L+S1+U1<2,L+S4>=2*mu,
        S4+3*E<=1,S1>=l-3*E],"QF_LRA")
    large=[h>=z3.Q(4,15),12*h<=5,E>=0,6*E<=1]
    whole=[h>=0,12*h<=5,E>=0,6*E<=1]
    G=g(h)
    query("whole G-E positive",whole+[G-E<=0])
    query("whole h+E<1",whole+[h+E>=1],"QF_LRA")
    query("whole E+q(h+E)<1",whole+[E+q(h+E)>=1])
    query("q shift at most 2E",whole+[q(h+E)-q(h)>2*E])
    query("positive bridge argument",whole+[
        h+E>0,1-G+3*E-q(h+E)<=0])
    small=[h>=0,15*h<=4,E>=0,6*E<=1]
    query("small bridge argument <1",small+[1-G+3*E-q(h+E)>=1])
    query("small K<3/5",small+[10*h>=3*(1-h*h)])
    P=3*E*E*h**4+8*E*E*h*h+E*E+3*E*h**5+18*E*h**3+3*E*h+9*h**4+4*h*h-1
    query("R h-second-derivative polynomial negative",[
        h>=0,3*h<=1,E>=0,6*E<=1,P> -z3.Q(1,9)])
    x=z3.Real("x")
    query("q derivative <2 on [0,1)",[x>=0,x<1,2/(2-x)**2>=2])
    query("q second derivative >=1/2",[
        x>=0,x<1,4/(2-x)**3<z3.Q(1,2)])
    query("g second derivative >=1/2",[
        x>=0,x<1,4/(1+x)**3<z3.Q(1,2)])
    query("minus g first derivative >=1/2",[
        x>=0,x<1,2/(1+x)**2<z3.Q(1,2)])
    # Sympy independently checks the derivative and endpoint identities.
    H,EE,X=sp.symbols("h E x")
    qs=lambda a:a/(2-a);gs=lambda a:(1-a)/(1+a)
    GG=gs(H);KK=2*H/(1-H*H);AA=1-GG
    RR=(1-KK*(H+EE))**2
    DD=qs(GG-EE)+qs(H+EE)
    UU=qs(GG-EE)+qs(EE+qs(H+EE))
    WW=qs(3*EE)+gs(AA+3*EE-qs(H+EE))
    identities=[]
    def ident(name,expr):
        print(json.dumps({"checking_identity":name}),flush=True)
        assert sp.cancel(expr)==0,name;identities.append(name)
    ident("q first",sp.diff(qs(X),X)-2/(2-X)**2)
    ident("q second",sp.diff(qs(X),X,2)-4/(2-X)**3)
    ident("g first",sp.diff(gs(X),X)+2/(1+X)**2)
    ident("g second",sp.diff(gs(X),X,2)-4/(1+X)**3)
    ident("G second",sp.diff(GG,H,2)-4/(1+H)**3)
    ident("A-q(h) positive identity",AA-qs(H)-3*H*(1-H)/((1+H)*(2-H)))
    PP=3*EE**2*H**4+8*EE**2*H**2+EE**2+3*EE*H**5+18*EE*H**3+3*EE*H+9*H**4+4*H**2-1
    ident("R hh numerator",sp.diff(RR,H,2)-8*PP/(1-H*H)**4)
    ident("R EE",sp.diff(RR,EE,2)-2*KK**2)
    ident("Phi+3E square gap",EE*(2+EE)-(4*EE/(1+EE))**2-
          EE*(EE**3+4*EE**2-11*EE+2)/(1+EE)**2)
    ident("bridge lower l endpoint WITH q(3E)",
          (qs(X)+gs(AA+X-qs(H+EE))).subs(X,3*EE)-WW)
    ident("bridge upper l endpoint (generic q argument)",
          gs(1-X)-qs(X))
    # Verify the chain with independent scalar arguments before substitution.
    V,Vp,Vpp=sp.symbols("v vp vpp")
    Fn=sp.Function("v")(EE)
    chain=sp.diff(gs(Fn),EE,2).subs({
        sp.diff(Fn,EE,2):Vpp,sp.diff(Fn,EE):Vp,Fn:V})
    ident("T EE chain",chain-4*Vp**2/(1+V)**3+2*Vpp/(1+V)**2)
    constants=[]
    def exact(name,value,expected=None,positive=False):
        value=sp.factor(value)
        if expected is not None:
            assert value==expected,(name,value,expected)
        if positive:
            assert value>0,(name,value)
        constants.append({"name":name,"value":str(value)})
    exact("R hh P coarse corner",PP.subs({H:sp.Rational(1,3),EE:sp.Rational(1,6)}),
          -sp.Rational(1,9))
    exact("K small endpoint",KK.subs(H,sp.Rational(4,15)),sp.Rational(120,209))
    exact("R EE upper",2*sp.Rational(120,209)**2,sp.Rational(28800,43681))
    exact("R EE margin below 3/4",sp.Rational(3,4)-sp.Rational(28800,43681),positive=True)
    exact("D EE lower",sp.Rational(1,2)*2,sp.Rational(1))
    exact("U EE lower",sp.Rational(1,2)+sp.Rational(1,2)*sp.Rational(3,2)**2+
          sp.Rational(1,4),sp.Rational(15,8))
    exact("32/209 below 1/6",sp.Rational(1,6)-sp.Rational(32,209),positive=True)
    small_corners=[]
    for hh in [sp.Rational(0),sp.Rational(4,15)]:
        for ee in [sp.Rational(0),sp.Rational(1,6)]:
            vals=[]
            for name,func in [("D",DD),("U",UU),("W",WW)]:
                value=sp.factor((RR-func).subs({H:hh,EE:ee}))
                exact(f"small corner {hh},{ee} gap {name}",value,
                      sp.Rational(0) if hh==ee==0 else None,
                      positive=not(hh==ee==0))
                vals.append(str(value))
            small_corners.append({"h":str(hh),"E":str(ee),"gaps":vals})
    large_corners=[]
    for hh in [sp.Rational(4,15),sp.Rational(5,12)]:
        for ee in [sp.Rational(0),sp.Rational(1,6)]:
            vals=[]
            for name,func in [("D",DD),("U",UU),("W",WW)]:
                value=sp.factor((sp.Rational(7,12)-func).subs({H:hh,EE:ee}))
                exact(f"large corner {hh},{ee} gap {name}",value,positive=True)
                vals.append(str(value))
            large_corners.append({"h":str(hh),"E":str(ee),"gaps":vals})
    result={"queries":rows,"symbolic_identities":identities,"constants":constants,
        "small_corners":small_corners,"large_corners":large_corners,
        "totals":{"UNSAT":len(rows),"NRA":sum(r["theory"]=="QF_NRA" for r in rows),
                  "LRA":sum(r["theory"]=="QF_LRA" for r in rows),
                  "symbolic_identities":len(identities),"constants":len(constants)},
        "scope":"Complete standardized far TOP real-gap exclusion, combined with round27",
        "not_proved":"Far no-TOP residuals; entire G2; S(6)=2"}
    Path(__file__).with_name("round29_far_top_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
