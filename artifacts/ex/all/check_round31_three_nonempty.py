"""Exact local geometry checks for far three meetings, F horizontal nonempty."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        solver=z3.SolverFor(theory);solver.set(timeout=60000);solver.add(*cs)
        start=time.perf_counter();ans=solver.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        if ans!=z3.unsat:
            row["detail"]=str(solver.model()) if ans==z3.sat else solver.reason_unknown()
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    mu,z,J,hc,u,U4=z3.Reals("mu z J hc u U4")
    query("C cannot contain actual TOP axis tail endpoint",[
        mu>1,z>0,z<1,J>=0,hc>1+2*z-z*z+J,
        U4<z,u>=mu-U4,hc+u*u<=2])
    c,s,A,D,L2,t,K,H,beta=z3.Reals("c s A D L2 t K H beta")
    norm=[c>0,s>0,c*c+s*s==1]
    query("actual QU and TOP leg give right leg bridge upper",norm+[
        mu>1,s*D+c*A==1,s*(mu-D)<=c*U4,U4<z,
        A>=(1-s)/c+z])
    query("c<=s forces c/(1+s)<5/12",norm+[
        c<=s,12*c>=5*(1+s)])
    query("actual RIGHT meet and bridge force c>s",norm+[
        mu>1,L2>1,L2*L2<=2,A+L2>=2*mu,z>0,7*z<1,
        A<(1-s)/c+z,c<=s])
    query("c>s implies c>1/2",norm+[c>s,2*c<=1])
    query("TOP meeting and z<1/7 force D>23/24",[
        mu>1,z>0,7*z<1,L2*(1-z*z)<=1+z*z,
        L2+D>=2*mu,24*D<=23])
    query("nonempty W H impossible from actual K equalities",norm+[
        mu>1,c>s,z>0,7*z<1,J>0,9*J*J>z,H>=0,
        s*D+c*A==1,A+J==K,D+H==K,
        K*c*s==c+s-mu,D>1-2*z*z/(1-z*z)])
    v=z3.Real("v")
    query("2delta(z)<sqrt(z)/3",[
        z>0,7*z<1,v>0,v*v==z,
        12*z*z>=v*(1-z*z)])
    x,L=z3.Reals("x L")
    query("near-anchor pair angle amplification <=133/121",[
        t>0,t*t+2*t<=1,L>=1,L*L<=2,D>=z3.Q(23,24),D<=1,
        L+(1+t*t-2*t*D)/(1-t*t)>=2,
        121*t*(3-L)>133*(L-1)])
    query("cosine angle cap kappa<=Yc",[
        x>0,5*x<=2,L>=1,L*(1-x*x)<=1+x*x,
        (L-1)*(1-2*x*x)>x*x*(3-L)])
    query("sine angle cap kappa<=Ys",[
        5*x>=2,x<1,L>=1,2*x*L<=1+x*x,
        (L-1)*(6*x-1-x*x)>(1-x)*(1-x)*(3-L)])
    kx,ky,bx,by,objective=z3.Reals("kx ky bx by objective")
    query("extended pair affine reduction with nonnegative coefficient",[
        kx>=0,L>=2-by+ky*D,D<=1,1-kx*ky>=0,
        objective==D+bx-kx*L+x+2*t-t*t,
        objective>(1-kx*ky)+bx-2*kx+kx*by+x+2*t-t*t])
    query("V far endpoint depth is less than true W halfangle",norm+[
        mu>1,t*(1+c)==s,(1-c*mu)/s>=t])
    S1,S2,U1,U2,L4,B,a,f,b=z3.Reals("S1 S2 U1 U2 L4 B a f b")
    query("empty original W H leaves C/F/root horizontal coverage",[
        hc+f+U1+U2>=2*mu,b>=2*mu-S1-S2,b+f<=B,
        hc<4*mu-B-S1-S2-U1-U2],"QF_LRA")
    query("two valid pair budgets yield full strengthened C chord",[
        mu>1,B<1,U1<a,U2<x,
        L4+S1+a+2*z-z*z<=2,D+S2+x+2*t-t*t<=2,
        L4+D>=2*mu,hc>=4*mu-B-S1-S2-U1-U2,
        hc<=1+2*z-z*z+2*t-t*t])
    for label,m,n in [("z larger",z,t),("t larger",t,z)]:
        query("final true endpoint-envelope contradiction: "+label,[
            m>=n,n>0,m<1,u>1-m,
            hc>1+2*m-m*m+2*n-n*n,hc+u*u<=2])
    # Independent local check of the root bound used in the final contradiction.
    ll,rr,uu=z3.Reals("ll rr uu")
    query("unit square three actual endpoints imply chord+up²<=2",norm+[
        c>=s,ll>=0,rr>=0,uu>=0,c*(ll+rr)<=1,s*(ll+rr)<=1,
        c*rr+s*uu<=1,s*ll+c*uu<=1,
        c*ll-s*uu<=1,s*uu-c*ll<=1,
        s*rr-c*uu<=1,c*uu-s*rr<=1,ll+rr+uu*uu>2])
    C,S,MU,DD,AA,JJ,HH,KK,T,X=sp.symbols("c s mu D A J H K t x")
    identities=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,name;identities.append(name)
    ident("K zero-mu-defect identity",
        2-(1+C+S)*(C+S-MU)/(C*S)-
        ((C+S+1)*(MU-1)+(1-C*C-S*S))/(C*S))
    ident("K and leg weighted relation",
        C*(KK-AA)+S*(KK-DD)-((C+S)*KK-(C*AA+S*DD)))
    ident("unit halfangle identity",(1-C)/S-S/(1+C)-
          (1-C*C-S*S)/(S*(1+C)))
    ident("near-anchor meeting angle factor",
        (sp.Symbol("L")+(1+T*T-2*T*DD)/(1-T*T)-2)*(1-T*T)-
        ((1-T)*((sp.Symbol("L")-1)-(3-sp.Symbol("L"))*T)+2*T*(1-DD)))
    ident("pair affine elimination",
        DD+(1+X*X)/(1-X*X)-2*X/(1-X*X)*
        (2-(1+T*T)/(1-T*T)+2*T*DD/(1-T*T))+X+2*T-T*T-
        ((1-4*X*T/((1-X*X)*(1-T*T)))*DD+
        (1+X*X)/(1-X*X)-4*X/(1-X*X)+
        2*X*(1+T*T)/((1-X*X)*(1-T*T))+X+2*T-T*T))
    m,n=sp.symbols("m n")
    ident("final same-block root sum",
        1+2*m-m*m+2*n-n*n+(1-m)**2-(2+2*n-n*n))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,value)
        constants.append({"name":name,"value":str(expected)})
    exact("c<=s bridge maximum rational",sp.Rational(5,12)+sp.Rational(1,7),sp.Rational(47,84))
    exact("RIGHT leg lower rational",2-sp.Rational(17,12),sp.Rational(7,12))
    exact("bridge contradiction gap",sp.Rational(7,12)-sp.Rational(47,84),sp.Rational(1,42))
    exact("delta at 1/7",2*sp.Rational(1,7)**2/(1-sp.Rational(1,7)**2),sp.Rational(1,24))
    exact("K cap denominator",sp.Rational(7,12)*sp.Rational(19,12),sp.Rational(133,144))
    exact("angle amplification loss",sp.Rational(1,12)/sp.Rational(133,144),sp.Rational(12,133))
    exact("angle amplification",1/(1-sp.Rational(12,133)),sp.Rational(133,121))
    exact("amplification below 11/10",sp.Rational(11,10)-sp.Rational(133,121),sp.Rational(1,1210))
    result={"queries":rows,"symbolic_identities":identities,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(r["theory"]=="QF_NRA" for r in rows),
                  "LRA":sum(r["theory"]=="QF_LRA" for r in rows),
                  "symbolic_identities":len(identities),"constants":len(constants)},
        "scope":"Complete far three-meeting branch with nonempty F horizontal trace",
        "not_proved":"Far LEFT gap; far RIGHT gap; far three meetings with F horizontal empty; S(6)=2"}
    Path(__file__).with_name("round31_three_nonempty_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
