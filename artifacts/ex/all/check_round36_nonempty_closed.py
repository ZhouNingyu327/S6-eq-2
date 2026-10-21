"""Exact local checks for closing the final nonempty-F relay mechanism."""
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
    mu,b,f,Sigma,h0,h1,r,u,x,t,D,Up,L4=z3.Reals(
        "mu b f Sigma h0 h1 r u x t D Up L4")
    query("same original F bottom/H pair gives Sigma>1+f",[
        mu>1,b>=2*mu-Sigma,b+f<1,Sigma<=1+f],"QF_LRA")
    query("direct TOP order I actual relay budget bounds h0",[
        Sigma>1+f,f>=h0-r,Sigma<1-u+(1-x)/(1+x),
        r<5*u*u/6,t==u-5*u*u/6,x>0,x<1,
        h0>=(1-x)/(1+x)-t])
    query("direct TOP order I convex chord gap",[
        u>0,2*u<1,t==u-5*u*u/6,
        (1-t)/(1+t)+u*u/(2*(1-u))>=1])
    query("relay convex function stays below common endpoints",[
        t>0,t<1,x>=0,x<=(1-t)/(1+t),
        x+((1-x)/(1+x)-t)/(2-(1-x)/(1+x)+t)>(1-t)/(1+t)])
    query("direct TOP order II original W bridge bounds right H end",[
        mu>1,D+L4>=2*mu,D<mu-h1+r/(2-r),
        L4<1+u*u/(2*(1-u)),u>0,2*u<1,r>0,
        h1>=u*u/(2*(1-u))+r/(2-r)])
    query("direct TOP order II gives h1<7u/9",[
        u>0,2*u<1,r>0,r/(2-r)<5*u*u/9,
        h1<u*u/(2*(1-u))+r/(2-r),9*h1>=7*u])
    query("direct TOP order II same-F budget forces h1>u",[
        u>0,x>0,x<1,Sigma<1-u+(1-x)/(1+x),
        Sigma>2-x-h1,h1<=u])
    c,s,tau=z3.Reals("c s tau")
    norm=[c>0,s>0,c*c+s*s==1]
    query("original W Cup forces halfangle tau>1-u",norm+[
        mu>1,c*mu+s*(mu-u)<=1,tau*s==1-c,tau<=1-u])
    query("original W actual H point lies beyond 1-g(tau)",norm+[
        mu>1,c*(mu-h0)+s*mu<=1,tau*s==1-c,
        h0<=1-(1-tau)/(1+tau)])
    query("original W Cup and actual H left endpoint give h0>1-q(u)",norm+[
        mu>1,u>0,u<1,c*mu+s*(mu-u)<=1,
        c*(mu-h0)+s*mu<=1,h0<=1-u/(2-u)])
    query("same F actual relay yields total short-leg loss bound",[
        Sigma>1+f,f>=h0-r,h0>1-u/(2-u),u>0,u<1,
        2-Sigma>=u/(2-u)+r])
    eta,K,G,z,A,L1,L2,eps1,eps2=z3.Reals(
        "eta K G z A L1 L2 eps1 eps2")
    query("original W V bridge and RIGHT meet give actual L2 defect",[
        mu>1,u>0,u<1,A<Up+u/(2-u),Up<z,
        L2+A>=2*mu,z<(1-eta)/(1+3*eta),eta>0,
        eps2==L2-1,eps2<=4*eta/(1+3*eta)-u/(2-u)])
    E,Y,loss,v1,v2=z3.Reals("E Y loss v1 v2")
    query("two actual long-leg deficits dominate scalar E",[
        eta>0,u>0,u<1,eps1>u-eta,
        eps2>4*eta/(1+3*eta)-u/(2-u),
        E==u-eta+4*eta/(1+3*eta)-u/(2-u),eps1+eps2<=E])
    query("two explicit Phi loss bounds force total loss above Y",[
        v1>0,v2>0,eps1==v1*v1,eps2==v2*v2,
        loss>5*(v1+v2)/4,Y>=0,
        eps1+eps2>16*Y*Y/25,loss<=Y])
    query("separate u concavity implication",[
        E>=0,Y>=0,eps1>0,eps2>=0,
        -eps1-z3.Q(32,25)*(E*E+Y*eps2)>=0])
    query("separate eta concavity implication",[
        eta>=0,Y>=0,u>=0,eps1>=0,eps2>=0,
        -24/(1+3*eta)**3-z3.Q(32,25)*(eps1*eps1+Y*u*eps2)>=0])
    q=u/(2-u);kk=2*eta/(1-eta*eta)
    scalar=u-eta+4*eta/(1+3*eta)-q-z3.Q(16,25)*(q+kk*u)**2
    query("whole enlarged scalar rectangle positive for u>0",[
        eta>=0,12*eta<=5,u>0,2*u<=1,scalar<=0])
    p,e=z3.Reals("p e")
    query("F-empty side upper point excludes bottom same-side by area",[
        mu>1,e>=0,p<=0,mu*mu-e*p<=1])
    query("F-empty side upper point excludes bottom opposite-side by diameter",[
        mu>1,e>=0,p>0,(mu+p)*(mu+p)+(mu+e)*(mu+e)<=2])

    E0,U0,T0,X=sp.symbols("eta u t x")
    qsp=lambda a:a/(2-a)
    gsp=lambda a:(1-a)/(1+a)
    ksp=2*E0/(1-E0**2)
    hsp=4*E0/(1+3*E0)-E0
    yy=qsp(U0)+ksp*U0
    pp=U0-qsp(U0)+hsp-sp.Rational(16,25)*yy**2
    ids=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.cancel(expr));ids.append(name)
    ident("q first derivative",sp.diff(qsp(U0),U0)-2/(2-U0)**2)
    ident("q second derivative",sp.diff(qsp(U0),U0,2)-4/(2-U0)**3)
    ident("K first derivative",sp.diff(ksp,E0)-2*(1+E0**2)/(1-E0**2)**2)
    ident("K second derivative",sp.diff(ksp,E0,2)-4*E0*(3+E0**2)/(1-E0**2)**3)
    ident("eta drift second derivative",sp.diff(hsp,E0,2)+24/(1+3*E0)**3)
    ident("P second u derivative",sp.diff(pp,U0,2)-
        (-sp.diff(qsp(U0),U0,2)-sp.Rational(32,25)*
         ((sp.diff(qsp(U0),U0)+ksp)**2+yy*sp.diff(qsp(U0),U0,2))))
    ident("P second eta derivative",sp.diff(pp,E0,2)-
        (-24/(1+3*E0)**3-sp.Rational(32,25)*
         ((U0*sp.diff(ksp,E0))**2+yy*U0*sp.diff(ksp,E0,2))))
    ident("relay convex function rational expression",
        X+qsp(gsp(X)-T0)-(X+(1-T0-(1+T0)*X)/(1+T0+(3+T0)*X)))
    ident("relay convex function positive second derivative",
        sp.diff(X+qsp(gsp(X)-T0),X,2)-8*(3+T0)/(1+T0+(3+T0)*X)**3)
    ident("relay convex left endpoint",qsp(1-T0)-gsp(T0))
    ident("relay convex right endpoint",gsp(T0)+qsp(gsp(gsp(T0))-T0)-gsp(T0))
    C,S=sp.symbols("c s")
    ident("original W halfangle identity",
        (1-S)/C-(1-(1-C)/S)/(1+(1-C)/S)-
        (1-C*C-S*S)/(C*(1+S-C)))
    ident("loss deficit sum",U0-E0+4*E0/(1+3*E0)-qsp(U0)-
        (U0-qsp(U0)+3*E0*(1-E0)/(1+3*E0)))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,sp.factor(value))
        constants.append({"name":name,"value":str(expected)})
    exact("scalar corner 00",pp.subs({E0:0,U0:0}),sp.Rational(0))
    exact("scalar corner eta0",pp.subs({E0:sp.Rational(5,12),U0:0}),sp.Rational(35,108))
    exact("scalar corner uhalf",pp.subs({E0:0,U0:sp.Rational(1,2)}),sp.Rational(43,450))
    exact("scalar corner etahalf",pp.subs({E0:sp.Rational(5,12),U0:sp.Rational(1,2)}),
        sp.Rational(1598333,38234700))
    exact("TOP relay t/u lower factor",1-sp.Rational(5,6)*sp.Rational(1,2),sp.Rational(7,12))
    exact("TOP relay g deficit lower factor",2*sp.Rational(7,12)/sp.Rational(3,2),sp.Rational(7,9))
    exact("TOP second order handoff factor",1+sp.Rational(5,9),sp.Rational(14,9))
    result={"queries":rows,"symbolic_identities":ids,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(t["theory"]=="QF_NRA" for t in rows),
                  "LRA":sum(t["theory"]=="QF_LRA" for t in rows),
                  "symbolic_identities":len(ids),"constants":len(constants)},
        "scope":"All remaining nonempty F horizontal cases excluded via the LEFT positive relay proof",
        "also_proved":"Empty-F LEFT/RIGHT side-gap cases have C disjoint from BOTTOM",
        "not_proved":"Empty-F LEFT/RIGHT/three-meeting families; entire G2; S(6)=2"}
    Path(__file__).with_name("round36_nonempty_closed_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
