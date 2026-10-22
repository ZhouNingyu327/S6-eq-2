"""Exact checks for eliminating empty/tangent W H in the last nonempty-F type."""
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
    eta,u,k,v,K,B,x,r,phi,S1,S2,mu,b,f,U=z3.Reals(
        "eta u k v K B x r phi S1 S2 mu b f U")
    query("same original F bottom and full H bridge budget",[
        mu>1,b>=2*mu-S1-S2,f>=mu-U-r,U<x,b+f<1,
        S1+S2<=2-x-r],"QF_LRA")
    rho=z3.Real("rho")
    query("nonpositive defect: actual short legs force rho(x)<r",[
        x>0,x<1,rho*(1+x)==x*(1-x),
        S1<1,S2<(1-x)/(1+x),S1+S2>2-x-r,rho>=r])
    query("positive defect: same legs force loss<r-rho(x)",[
        x>0,x<1,rho*(1+x)==x*(1-x),
        S1<=phi,S2<(1-x)/(1+x),S1+S2>2-x-r,1-phi>=r-rho])
    query("C direct QU contradicts same-F full H bridge",[
        u>0,2*u<1,r<u,1-phi>u,rho>0,1-phi<r-rho])
    query("positive defect maps to scalar cap B(v)",[
        v>0,1-phi>5*v/4,1-phi<r-rho,r<=K*u,
        k<8*rho/5,5*k>=8*K*u-10*v])
    query("scalar cap implies v<2/5",[
        v>0,k>0,5*k<8*K*u-10*v,u>0,2*u<1,K>0,K<=1,5*v>=2])
    query("M(eta) is decreasing on C unit-circle range",[
        eta>0,eta*eta+2*eta<=1,
        -4/(1+3*eta)**2+2/(2-eta)**2>0])
    query("small eta A0 below 3/10",[
        eta>0,25*eta<=7,16*eta*eta/(5*(1-eta*eta))>=z3.Q(3,10)])
    query("small eta numerator polynomial positive",[
        eta>0,25*eta<=7,19*eta**3-83*eta**2-99*eta+35<=0])
    query("small eta numerator polynomial decreases",[
        eta>0,25*eta<=7,57*eta*eta-166*eta-99>=0])
    query("B(v) strictly decreases on feasible v range",[
        K>0,K<=1,v>=0,5*v<=2,16*K*v/5-2>=0])
    query("g(B(v))-q(u) strictly increases where 0<B<=3/10",[
        K>0,K<=1,v>=0,5*v<=2,B>0,10*B<=3,u>0,2*u<1,
        (4-32*K*v/5)/(1+B)**2-4*v/(2-u)**2<=0])
    query("middle eta K cap",[
        eta>0,8*eta<=3,K*(1-eta*eta)==2*eta,55*K>48])
    query("middle eta threshold B below Z",[
        eta>0,8*eta<=3,K>0,55*K<=48,
        8*K*(eta+z3.Q(9,256))/5-z3.Q(3,8)>=z3.Q(29,111)])
    query("high eta threshold B below Z",[
        eta>0,70*eta<29,K>0,K<=1,
        8*K*(eta+z3.Q(169,2500))/5-z3.Q(13,25)>=z3.Q(29,111)])
    query("q difference less than 8v²/9",[
        eta>0,v>0,u==eta+v*v,2*u<1,
        u/(2-u)-eta/(2-eta)>=8*v*v/9])
    L2,A,z=z3.Reals("L2 A z")
    query("actual RIGHT meeting gives A>g(kappa)",[
        mu>1,L2>1,L2<3,k*(3-L2)==L2-1,A+L2>=2*mu,
        A<=(1-k)/(1+k)])
    query("actual W bridge and scalar inequality contradict",[
        k>0,k<1,u>0,u<1,eta>0,
        A>(1-k)/(1+k),A<z+u/(2-u),
        z<(1-eta)/(1+3*eta),
        (1-k)/(1+k)>(1-eta)/(1+3*eta)+u/(2-u)])
    base=[eta>0,eta*eta+2*eta<=1,u>0,2*u<1,k>0,111*k<29,
          K*(1-eta*eta)==2*eta,K>0,K<=1]
    query("whole continuous scalar lemma nonpositive defect",base+[
        u<=eta,5*k<8*K*u,
        (1-k)/(1+k)<=(1-eta)/(1+3*eta)+u/(2-u)])
    query("whole continuous scalar lemma positive defect",base+[
        u==eta+v*v,v>0,5*k<8*K*u-10*v,
        (1-k)/(1+k)<=(1-eta)/(1+3*eta)+u/(2-u)])
    E,V,KK=sp.symbols("eta v K")
    q=lambda t:t/(2-t)
    g=lambda t:(1-t)/(1+t)
    M=(1-E)/(1+3*E)+q(E)
    A0=16*E**2/(5*(1-E**2))
    BB=sp.Rational(8,5)*KK*(E+V**2)-2*V
    ids=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.cancel(expr));ids.append(name)
    ident("M derivative",sp.diff(M,E)-(-4/(1+3*E)**2+2/(2-E)**2))
    ident("M derivative sign polynomial",
        (-4/(1+3*E)**2+2/(2-E)**2)*
        (1+3*E)**2*(2-E)**2-14*(E**2+2*E-1))
    ident("small eta base numerator",
        g(A0)-M-E*(19*E**3-83*E**2-99*E+35)/
        ((2-E)*(3*E+1)*(11*E**2+5)))
    ident("B derivative",sp.diff(BB,V)-(sp.Rational(16,5)*KK*V-2))
    ident("monotone comparison derivative",
        sp.diff(g(BB)-q(E+V**2),V)-
        ((4-sp.Rational(32,5)*KK*V)/(1+BB)**2-4*V/(2-E-V**2)**2))
    ident("q difference",q(E+V**2)-q(E)-2*V**2/((2-E-V**2)*(2-E)))
    ll,kappa=sp.symbols("L kappa")
    ident("RIGHT meeting complementary leg",2-(1+3*kappa)/(1+kappa)-g(kappa))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,value)
        constants.append({"name":name,"value":str(expected)})
    exact("monotone derivative rational gap",sp.Rational(144,169)-sp.Rational(32,45),sp.Rational(1072,7605))
    exact("small numerator endpoint",(19*E**3-83*E**2-99*E+35).subs(E,sp.Rational(7,25)),sp.Rational(18592,15625))
    exact("g(Z)",g(sp.Rational(29,111)),sp.Rational(41,70))
    exact("middle q increment",sp.Rational(8,9)*sp.Rational(3,16)**2,sp.Rational(1,32))
    exact("middle scalar gap",sp.Rational(41,70)-M.subs(E,sp.Rational(7,25))-sp.Rational(1,32),sp.Rational(409,1107680))
    exact("middle K cap",2*sp.Rational(3,8)/(1-sp.Rational(3,8)**2),sp.Rational(48,55))
    exact("middle B threshold gap",sp.Rational(29,111)-
        (sp.Rational(8,5)*sp.Rational(48,55)*(sp.Rational(3,8)+sp.Rational(9,256))-sp.Rational(3,8)),
        sp.Rational(3103,48840))
    exact("high scalar gap",sp.Rational(41,70)-M.subs(E,sp.Rational(3,8))-
        sp.Rational(8,9)*sp.Rational(13,50)**2,sp.Rational(12853,17403750))
    exact("high B threshold gap",sp.Rational(29,111)-
        (sp.Rational(8,5)*(sp.Rational(29,70)+sp.Rational(169,2500))-sp.Rational(13,25)),
        sp.Rational(24874,2428125))
    result={"queries":rows,"symbolic_identities":ids,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(t["theory"]=="QF_NRA" for t in rows),
                  "LRA":sum(t["theory"]=="QF_LRA" for t in rows),
                  "symbolic_identities":len(ids),"constants":len(constants)},
        "scope":"Last LEFT positive-F case: original W horizontal trace has positive length",
        "not_proved":"Entire LEFT positive F relay; empty-F families; S(6)=2"}
    Path(__file__).with_name("round35_positive_H_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
