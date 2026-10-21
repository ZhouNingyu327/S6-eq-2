"""Exact scalar and same-F budget checks. No square-layout optimization."""
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
    mu,a,l,p,U,b,f,S1,S2,Sigma=z3.Reals("mu a l p U b f S1 S2 Sigma")
    query("same F bottom and left-axis bridge give Sigma>2-a-l",[
        mu>1,p==mu-U,U<a,p>l,f>=p-l,
        Sigma==S1+S2,b>=2*mu-Sigma,b+f<1,Sigma<=2-a-l],"QF_LRA")
    rho,v,w,phi,u,eta,z,K=z3.Reals("rho v w phi u eta z K")
    query("same bottom legs force rho(a)<l",[
        a>0,a<1,rho*(1+a)==a*(1-a),
        S1<(1-a)/(1+a),S2<1,S1+S2>2-a-l,rho>=l])
    query("same bottom legs and Phi force loss<l-rho",[
        a>0,a<1,rho*(1+a)==a*(1-a),
        S1<(1-a)/(1+a),S2<=phi,S1+S2>2-a-l,1-phi>=l-rho])
    query("strong Phi loss positive square difference",[
        v>0,(1+v*v)*(1+v*v)*(2+v*v)<=(z3.Q(5,4)+v)*(z3.Q(5,4)+v)])
    query("small corner polynomial decreases",[
        a>0,12*a<=5,-13-42*a+48*a*a>=0])
    query("small corner polynomial is positive",[
        a>0,12*a<=5,8-13*a-21*a*a+16*a*a*a<=0])
    query("large corner Ys denominator positive",[
        12*a>=5,a<1,6*a-1-a*a<=0])
    query("large corner polynomial increases",[
        12*a>=5,a<1,-24*a*a+106*a-8<=0])
    query("large corner polynomial is positive",[
        12*a>=5,a<1,-8*a*a*a+53*a*a-8*a-5<=0])
    query("small corner cap implies z<8rho/5",[
        a>0,12*a<=5,rho*(1+a)==a*(1-a),
        z<a*a/(1-2*a*a),5*z>=8*rho])
    query("large corner cap implies z<8rho/5",[
        12*a>=5,a<1,rho*(1+a)==a*(1-a),
        z<(1-a)*(1-a)/(6*a-1-a*a),5*z>=8*rho])
    L=z3.Real("L")
    query("all meeting corner angles have z<29/111",[
        L>1,70*L<99,z<(L-1)/(3-L),111*z>=29])
    query("strong loss and same-F budget yield scalar second type",[
        v>0,1-phi>5*v/4,1-phi<l-rho,l<=K*u,
        z<8*rho/5,5*z>=8*K*u-10*v])
    query("positive scalar type forces v<2/5",[
        v>0,z>0,5*z<8*K*u-10*v,K>0,K<=1,u>0,2*u<1,5*v>=2])
    query("eta<=sqrt2-1 implies eta<29/70",[
        eta>0,eta*eta+2*eta<=1,70*eta>=29])
    query("D negative on eta<=7/25",[
        eta>0,25*eta<=7,-15+62*eta-31*eta*eta>=0])
    query("R derivative positive on (0,1/2)",[
        eta>0,2*eta<1,2/(1+eta)**2-2/(2-eta)**2<=0])
    query("R derivative below one on eta>=7/25",[
        25*eta>=7,2*eta<1,2/(1+eta)**2-2/(2-eta)**2>=1])
    query("A0 derivative greater than 224/125",[
        25*eta>=7,2*eta<1,(32*eta)/(5*(1-eta*eta)**2)<=z3.Q(224,125)])
    query("q difference below 8v²/9",[
        eta>0,u==eta+v*v,v>0,2*u<1,
        u/(2-u)-eta/(2-eta)>=8*v*v/9])
    query("f derivative strictly negative on relevant interval",[
        K>0,K<=1,v>=0,5*v<=2,u>0,2*u<1,
        (16*K/5+4/(2-u)**2)*v-2>z3.Q(-2,225)])
    query("small v affine loss coefficient 62/45",[
        v>0,4*v<=1,(z3.Q(8,5)+z3.Q(8,9))*v*v-2*v>-z3.Q(62,45)*v])
    D,DD,Dp,Rpp,Coeff=z3.Reals("D DD Dp Rpp Coeff")
    query("concavity implication with D>0 and D''>0",[
        D>0,DD>0,Rpp<0,Rpp-z3.Q(900,961)*(Dp*Dp+D*DD)>=0])
    domains=[eta>0,eta*eta+2*eta<=1,u>0,2*u<1,z>0,
             111*z<29,K*(1-eta*eta)==2*eta,K>0,K<=1]
    query("whole continuous scalar lemma nonpositive defect",domains+[
        u<=eta,5*z<8*K*u,z+u/(2-u)>=2*eta/(1+eta)])
    query("whole continuous scalar lemma positive defect",domains+[
        u==eta+v*v,v>0,5*z<8*K*u-10*v,
        z+u/(2-u)>=2*eta/(1+eta)])
    e,d,G=z3.Reals("e d G")
    query("opposite inequalities from actual RIGHT/W endpoints contradict",[
        d>0,z+u/(2-u)>1-G+d,z+u/(2-u)<1-G,u>0,u<1])

    E,V,X=sp.symbols("eta v a")
    A0=16*E**2/(5*(1-E**2))
    R=3*E*(1-E)/((1+E)*(2-E))
    Dexpr=A0-R
    q=lambda x:x/(2-x)
    rh=X*(1-X)/(1+X)
    ids=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.cancel(expr))
        ids.append(name)
    ident("strong Phi loss sum of positive squares",
        (1+V**2)**2*(2+V**2)-(sp.Rational(5,4)+V)**2-
        (4*(V-sp.Rational(5,16))**2+sp.Rational(3,64)+4*V**4+V**6))
    ident("bottom leg rho identity",1-X-(1-X)/(1+X)-rh)
    ident("small angle rho cap numerator",
        sp.Rational(8,5)*rh-X**2/(1-2*X**2)-
        X*(8-13*X-21*X**2+16*X**3)/(5*(1+X)*(1-2*X**2)))
    ident("large angle rho cap numerator",
        sp.Rational(8,5)*rh-(1-X)**2/(6*X-1-X**2)-
        (1-X)*(-8*X**3+53*X**2-8*X-5)/(5*(1+X)*(6*X-1-X**2)))
    ident("R equals target minus qeta",R-(2*E/(1+E)-q(E)))
    ident("A0 derivative",sp.diff(A0,E)-32*E/(5*(1-E**2)**2))
    ident("A0 second derivative",sp.diff(A0,E,2)-32*(1+3*E**2)/(5*(1-E**2)**3))
    ident("R first derivative",sp.diff(R,E)-(2/(1+E)**2-2/(2-E)**2))
    ident("R second derivative",sp.diff(R,E,2)-(-4/(1+E)**3-4/(2-E)**3))
    ident("D sign polynomial",
        Dexpr-E*(-15+62*E-31*E**2)/(5*(1-E**2)*(2-E)))
    ident("concavity exact second derivative",
        sp.diff(R-sp.Rational(450,961)*Dexpr**2,E,2)-
        (sp.diff(R,E,2)-sp.Rational(900,961)*(sp.diff(Dexpr,E)**2+Dexpr*sp.diff(Dexpr,E,2))))
    ident("q difference exact",q(E+V**2)-q(E)-2*V**2/((2-E-V**2)*(2-E)))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,sp.factor(value),expected)
        constants.append({"name":name,"value":str(expected)})
    b0=sp.Rational(29,70);a0=sp.Rational(7,25);Z=sp.Rational(29,111)
    exact("small corner polynomial endpoint",(8-13*X-21*X**2+16*X**3).subs(X,sp.Rational(5,12)),sp.Rational(41,432))
    exact("large corner polynomial endpoint",(-8*X**3+53*X**2-8*X-5).subs(X,sp.Rational(5,12)),sp.Rational(125,432))
    exact("D left endpoint",Dexpr.subs(E,a0),sp.Rational(-77,30960))
    exact("D right endpoint",Dexpr.subs(E,b0),sp.Rational(84709,250305))
    exact("large-v gap",sp.Rational(31,90)-Dexpr.subs(E,b0),sp.Rational(9043,1501830))
    exact("concavity left lower gap",R.subs(E,a0)-Z,sp.Rational(1027,76368))
    exact("concavity right gap",(R-sp.Rational(450,961)*Dexpr**2).subs(E,b0)-Z,
          sp.Rational(23375336726,2408365675881))
    exact("small-v coefficient",2-(sp.Rational(8,5)+sp.Rational(8,9))/4,sp.Rational(62,45))
    exact("quarter-v loss",sp.Rational(62,45)/4,sp.Rational(31,90))
    exact("concavity coefficient",sp.Rational(8,9)*sp.Rational(45,62)**2,sp.Rational(450,961))
    exact("derivative negative gap",2-sp.Rational(224,45)*sp.Rational(2,5),sp.Rational(2,225))
    result={"queries":rows,"symbolic_identities":ids,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(r["theory"]=="QF_NRA" for r in rows),
                  "LRA":sum(r["theory"]=="QF_LRA" for r in rows),
                  "symbolic_identities":len(ids),"constants":len(constants)},
        "scope":"Entire far RIGHT gap and nonempty F H, combined with round32 positive case",
        "not_proved":"LEFT with nonempty F H; LEFT/RIGHT/three meetings with empty F H; S(6)=2"}
    Path(__file__).with_name("round33_right_nonempty_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
