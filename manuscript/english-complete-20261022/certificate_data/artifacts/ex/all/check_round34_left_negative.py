"""Real-endpoint and scalar checks for LEFT-gap, negative F horizontal."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        sol=z3.SolverFor(theory);sol.set(timeout=60000);sol.add(*cs)
        start=time.perf_counter();ans=sol.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        if ans!=z3.unsat:
            row["detail"]=str(sol.model()) if ans==z3.sat else sol.reason_unknown()
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    mu,c,s,l,r,u,d,alpha,beta,eta,K,e,L1=z3.Reals(
        "mu c s l r u d alpha beta eta K e L1")
    norm=[c>=s,s>0,c*c+s*s==1]
    roots=[mu>1,l>0,r>0,u>0,d>0,l<mu,r<mu,u<mu,d<mu,l+r-d>mu]
    query("LEFT positive C first down root impossible",norm+roots+[
        s*d==-alpha,c*l<=-alpha])
    query("LEFT second down root upper cap",norm+roots+[
        c*d==-beta,c*(l+r)<=1,d>=1/c-mu])
    query("LEFT true up root first upper face active",norm+roots+[
        c*d==-beta,d<1/c-mu,z3.Or(s*u==alpha+1,c*u==beta+1),
        s*u<=alpha+1,c*u<=beta+1,s*u!=alpha+1])
    query("LEFT positive C true right root is short",norm+[
        alpha==s*u-1,c*r<=alpha+1,K*c==s,r>K*u])
    query("LEFT lower actual gap endpoint long leg",norm+[
        mu>1,eta*(1+c)==s,
        -c*mu+s*(L1-mu)>=s*u-1,L1<=1+u-eta])
    G,z=z3.Reals("G z")
    query("LEFT upper actual gap endpoint e+d<G",norm+[
        mu>1,s*mu+c*(e+d)<=1,G*c==1-s,e+d>=G])
    query("LEFT short leg and side endpoint give z<qG",[
        eta>0,eta*eta+2*eta<=1,G*(1+eta)==1-eta,z>0,z<1,
        d>0,1-(1-z)/(1+z)+d<G,z>=(1-eta)/(1+3*eta)])
    cw,sw=z3.Reals("cw sw")
    query("one original corner square cannot contain two short axis ends",[
        cw>0,sw>0,cw*cw+sw*sw==1,mu>1,
        cw*r>=mu*(cw+sw)-1,sw*u>=mu*(cw+sw)-1,r+u<=mu])
    query("LEFT C right+up roots are too short for joint W containment",[
        mu>1,u>0,2*u<1,r<=K*u,K>0,K<=1,r+u>=mu])
    x=z3.Real("x")
    query("direct Q2 contact gives bottom short leg <q(r)",[
        r>0,2*r<1,x>1-r,x<1,
        (1-x)/(1+x)>=r/(2-r)])
    query("large x gives L2-1<Delta(r)",[
        r>0,2*r<1,x>1-r,x<1,
        (1-x)*(1-x)/(2*x)>=r*r/(2*(1-r))])
    w,v,phi,S1,S2=z3.Reals("w v phi S1 S2")
    query("direct Q2 bottom budget forces positive w<2u/9",[
        u>0,2*u<1,r>0,r<=u,w>0,w==v*v,v>0,
        phi<1-v,S1<=phi,S2<r/(2-r),S1+S2>1,9*w>=2*u])
    query("direct Q2 yields u<9eta/7: positive w",[
        eta>0,u==eta+w,9*w<2*u,7*u>=9*eta],"QF_LRA")
    query("direct Q2 yields u<9eta/7: nonpositive w",[
        eta>0,u==eta+w,w<=0,7*u>=9*eta],"QF_LRA")
    query("direct Q2 and direct QU are incompatible",[
        eta>0,12*eta<5,u<9*eta/7,
        z>1-u,z<(1-eta)/(1+3*eta)])
    query("direct Q2 with actual W up bridge impossible",[
        eta>0,12*eta<5,u>0,2*u<1,7*u<9*eta,
        r>0,r<=u,z<(1-eta)/(1+3*eta),
        z+u/(2-u)+r*r/(2*(1-r))>=1])
    query("direct QU implies eta<2u/5<1/5",[
        eta>0,u>0,2*u<1,z>1-u,z<(1-eta)/(1+3*eta),
        z3.Or(5*eta>=2*u,5*eta>=1)])
    query("direct QU makes K<5u/6",[
        eta>0,5*eta<2*u,u>0,2*u<1,
        K*(1-eta*eta)==2*eta,6*K>=5*u])
    query("direct QU forces q(r)<5u²/9",[
        u>0,2*u<1,r>0,6*r<5*u*u,r/(2-r)>=5*u*u/9])
    query("direct QU implies w>u²",[
        u>0,2*u<1,eta>0,5*eta<2*u,w==u-eta,w<=u*u])
    query("bottom same legs then force x<g(u)",[
        u>0,2*u<1,w>u*u,w==v*v,v>0,phi<1-v,
        S1<=phi,S1+S2>1,S2<(1-x)/(1+x),x>0,x<1,
        x>=(1-u)/(1+u)])
    query("large z gives L4-1<Delta(u)",[
        u>0,2*u<1,z>1-u,z<1,
        (1-z)*(1-z)/(2*z)>=u*u/(2*(1-u))])
    query("actual W right bridge conflicts with TOP meeting",[
        u>0,2*u<1,r>0,6*r<5*u*u,x<(1-u)/(1+u),
        x+r/(2-r)+u*u/(2*(1-u))>=1])

    C,S,M,R,U,E,X,V=sp.symbols("c s mu r u eta x v")
    identities=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.cancel(expr));identities.append(name)
    ident("joint-axis endpoint lower difference",
        ((M*(C+S)-1)*(C+S)/(C*S)-M)-
        ((M-1)*(1+C*S)+(1-C)*(1-S))/(C*S)-
        M*(C*C+S*S-1)/(C*S))
    ident("q(G) in centre halfangle",
        ((1-E)/(1+E))/(2-(1-E)/(1+E))-(1-E)/(1+3*E))
    ident("long-leg defect exact",(1+X*X)/(2*X)-1-(1-X)**2/(2*X))
    ident("long-leg defect derivative",sp.diff((1-X)**2/(2*X),X)-(X*X-1)/(2*X*X))
    ident("short leg from direct endpoint",
        (1-(1-R))/(1+(1-R))-R/(2-R))
    ident("TOP lower angle rearrangement",
        (U-4*E/(1+3*E))*(1+3*E)-(U-E*(4-3*U)))
    ident("g deficit",1-(1-U)/(1+U)-2*U/(1+U))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,value)
        constants.append({"name":name,"value":str(expected)})
    exact("eta top gap lower factor",4/(1+3*sp.Rational(5,12)),sp.Rational(16,9))
    exact("top factor versus direct budget",sp.Rational(16,9)-sp.Rational(9,7),sp.Rational(31,63))
    exact("first direct endpoint combined budget",sp.Rational(6,7)+sp.Rational(9,14),sp.Rational(3,2))
    exact("first contradiction factor gap",sp.Rational(16,9)-sp.Rational(3,2),sp.Rational(5,18))
    exact("eta<1/5 norm denominator",1-sp.Rational(1,5)**2,sp.Rational(24,25))
    exact("K/u constant",sp.Rational(4,5)/sp.Rational(24,25),sp.Rational(5,6))
    exact("q(r)/u² constant",sp.Rational(2,3)*sp.Rational(5,6),sp.Rational(5,9))
    exact("last chord deficit coefficient",1+sp.Rational(5,9),sp.Rational(14,9))
    exact("last contradiction coefficient gap",sp.Rational(4,3)-sp.Rational(7,9),sp.Rational(5,9))
    result={"queries":rows,"symbolic_identities":identities,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(r["theory"]=="QF_NRA" for r in rows),
                  "LRA":sum(r["theory"]=="QF_LRA" for r in rows),
                  "symbolic_identities":len(identities),"constants":len(constants)},
        "scope":"Entire far LEFT real gap with negative nonempty F horizontal, including tangency",
        "also_proved":"All LEFT nonempty F: C cannot contain the actual V2 H inner endpoint",
        "not_proved":"LEFT positive F H; LEFT/RIGHT/three meetings with empty F H; S(6)=2"}
    Path(__file__).with_name("round34_left_negative_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
