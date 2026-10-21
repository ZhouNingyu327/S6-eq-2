"""Exact small lemmas for the final G4 positive-horizontal two-gap residual."""
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
    a,L,eta,y,r,b,f,S2,B=z3.Reals("f23_a f23_L f23_eta f23_y f23_r f23_b f23_f f23_S2 f23_B")
    common=[a>0,a<1,L>1,L<2,eta*(1+a)==a*(1-a),eta*(3-L)<L-1]
    rows.append(query("eta<kappa and cosine cap imply a>1/3",common+[
        3*a<=1,L*(1-a*a)<=1+a*a]))
    rows.append(query("eta<kappa and sine cap imply a<1/2",common+[
        2*a>=1,2*a*L<=1+a*a]))
    rows.append(query("eta>1/6 on 1/3<a<1/2",[
        3*a>1,2*a<1,eta*(1+a)==a*(1-a),6*eta<=1]))
    rows.append(query("no bottom-midpoint corner: F trace budget forces r>eta",[
        B<1,b>1-S2,f>1-a-r,S2<1-a-eta,b+f<=B,r<=eta],"QF_LRA"))
    z,w,SL,LB,dz=z3.Reals("f23_z f23_w f23_SL f23_LB f23_dz")
    rows.append(query("bottom-midpoint corner: left trace pin gives LB-1<Delta(z)",[
        z>0,z<1,w>0,w<1,
        SL*(1+w)<1-w,SL>1-z,
        LB*(1-w*w)<=1+w*w,
        2*(1-z)*dz==z*z,LB-1>=dz]))
    rows.append(query("bottom-midpoint corner: F trace budget forces r+LB-1>eta",[
        B<1,b>1-S2-(LB-1),f>1-a-r,
        S2<1-a-eta,b+f<=B,r+LB-1<=eta],"QF_LRA"))
    rows.append(query("r+Delta(y-r)>eta implies eta<y",[
        z>0,15*z<4,z==y-r,2*(1-z)*dz==z*z,
        r+dz>eta,eta>=y]))
    dy=z3.Real("f23_dy")
    rows.append(query("qU in C, no bottom-midpoint corner: r<Delta(y) conflicts with r>eta",[
        a>0,a<1,y>0,15*y<4,y<a,y<1-a,eta*(1+a)==a*(1-a),
        2*(1-y)*dy==y*y,r<dy,r>eta]))
    rows.append(query("qU in C, bottom-midpoint corner: double Delta below eta",[
        y>0,15*y<4,r>=0,z>0,z==y-r,
        2*(1-y)*dy==y*y,2*(1-z)*dz==z*z,
        r<dy,r+dz>eta,6*eta>1]))
    T,g,eT,mu,D,ell,u=z3.Reals("f23_T f23_g f23_eT f23_mu f23_D f23_ell f23_u")
    rows.append(query("qU in W plus real left-gap C endpoint gives eta(T)<y-r",[
        mu>1,T>0,T<1,g*(1+T)==1-T,eT*(1+T)==T*(1-T),
        D<g+y,u>1-T,ell>=mu-D,mu+ell+r+u<2,
        z==y-r,eT>=z]))
    rows.append(query("bottom-midpoint case: z-Delta(z)<1/10 forces z<3/28",[
        z>0,15*z<4,2*(1-z)*dz==z*z,z-dz<z3.RealVal("1/10"),28*z>=3]))
    rows.append(query("bottom-midpoint case: r+Delta(z)>eta forces r>3/20",[
        z>0,28*z<3,2*(1-z)*dz==z*z,
        r+dz>eta,6*eta>1,20*r<=3]))
    rows.append(query("no bottom-midpoint case: r>eta gives z<3/28",[
        15*y<4,6*eta>1,r>eta,z==y-r,28*z>=3],"QF_LRA"))
    rows.append(query("eta(T)<3/28 splits into T<1/7 or T>3/4",[
        T>0,T<1,eT*(1+T)==T*(1-T),
        28*eT<3,7*T>=1,4*T<=3]))
    dT=z3.Real("f23_dT")
    rows.append(query("small free-corner angle gives r<1/84, contradicting lower bound",[
        T>0,7*T<1,2*(1-T)*dT==T*T,r<dT,20*r>3]))
    rows.append(query("large free-corner angle bounds D<43/105",[
        T>0,T<1,4*T>3,g*(1+T)==1-T,
        15*y<4,D<g+y,105*D>=43]))
    p,s,h,lam=z3.Reals("f23_Cp f23_Cs f23_Ch f23_lambda")
    normal=[p>0,s>0,p>=s,p*p+s*s==1,mu>1,r>z3.RealVal("3/20"),p*(mu+r)<=1]
    rows.append(query("long C horizontal chord forces h>5/19",normal+[
        p*(mu+r)<=1,h*(1+p)==s,19*h<=5]))
    rows.append(query("positive C rotation bounds actual left upper ray lambda<7/12",normal+[
        s*(mu+r)+p*lam<=1,12*lam>=7]))
    rows.append(query("negative C rotation bounds actual left upper ray lambda<7/12",normal+[
        p*(mu+r)+s*lam<=1,12*lam>=7]))
    rows.append(query("large T: real left-gap endpoint contradicts C left upper bound",[
        mu>1,105*D<43,lam>=mu-D,12*lam<7],"QF_LRA"))

    A,Z,T0,P,Q=sp.symbols("a z t p q")
    etaA=A*(1-A)/(1+A)
    assert sp.cancel(A*A/(1-2*A*A)-etaA
        -A*(-1+2*A+3*A*A-2*A**3)/((1-2*A*A)*(1+A)))==0
    assert sp.cancel(etaA-(1-A)**2/(6*A-1-A*A)
        -(1-A)*(7*A*A-A-A**3-1)/((6*A-1-A*A)*(1+A)))==0
    assert sp.cancel(etaA-sp.Rational(1,6)
        -(3*A-1)*(1-2*A)/(6*(1+A)))==0
    assert sp.cancel(T0*(1-T0)/(1+T0)-sp.Rational(3,28)
        -(7*T0-1)*(3-4*T0)/(28*(1+T0)))==0
    assert sp.cancel(2*(Z/(2-Z))**2/(1-(Z/(2-Z))**2)-Z*Z/(2*(1-Z)))==0
    assert sp.cancel((Q/(1+P))**2-(1-P)/(1+P)
        -(P*P+Q*Q-1)/(1+P)**2)==0
    assert sp.cancel(sp.diff(Z-Z*Z/(2*(1-Z)),Z)-(2-6*Z+3*Z*Z)/(2*(1-Z)**2))==0
    constants={
        "cosine comparison at a=1/3":(1-2*A-3*A*A+2*A**3).subs(A,sp.Rational(1,3))==sp.Rational(2,27),
        "sine comparison at a=1/2":(7*A*A-A-A**3-1).subs(A,sp.Rational(1,2))==sp.Rational(1,8),
        "Delta(3/28)=9/1400":sp.Rational(3,28)**2/(2*(1-sp.Rational(3,28)))==sp.Rational(9,1400),
        "3/28-9/1400=141/1400>1/10":
            sp.Rational(3,28)-sp.Rational(9,1400)==sp.Rational(141,1400)
            and sp.Rational(141,1400)>sp.Rational(1,10),
        "1/6-9/1400=673/4200>3/20":
            sp.Rational(1,6)-sp.Rational(9,1400)==sp.Rational(673,4200)
            and sp.Rational(673,4200)>sp.Rational(3,20),
        "Delta(1/7)=1/84<3/20":
            sp.Rational(1,7)**2/(2*(1-sp.Rational(1,7)))==sp.Rational(1,84)
            and sp.Rational(1,84)<sp.Rational(3,20),
        "g(3/4)=1/7":(1-sp.Rational(3,4))/(1+sp.Rational(3,4))==sp.Rational(1,7),
        "1/7+4/15=43/105":sp.Rational(1,7)+sp.Rational(4,15)==sp.Rational(43,105),
        "(5/19)^2<3/43":sp.Rational(5,19)**2<sp.Rational(3,43),
        "g(5/19)=7/12":(1-sp.Rational(5,19))/(1+sp.Rational(5,19))==sp.Rational(7,12),
        "62/105-7/12=1/140>0":sp.Rational(62,105)-sp.Rational(7,12)==sp.Rational(1,140),
        "1/10<3/28":sp.Rational(1,10)<sp.Rational(3,28),
        "2 Delta(4/15)=16/165<1/6":
            sp.Rational(4,15)**2/(1-sp.Rational(4,15))==sp.Rational(16,165)
            and sp.Rational(16,165)<sp.Rational(1,6),
        "sqrt(2)-1<7/12":2*12**2<19**2,
    }
    assert all(constants.values())
    result={"status":"all exact checks passed" if all(row["result"]=="unsat" for row in rows) else "inspect",
        "queries":rows,"query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "symbolic_identity_checks":7,"constant_checks":{key:bool(value) for key,value in constants.items()},
        "scope":"Last G4 same-side positive-horizontal left/bottom two-gap case excluded; entire G4 closes with prior cases.",
        "proof_method":"midpoint-host split, parallel bottom/horizontal traces, real top bridge, free-angle dichotomy and C left-upper projection",
        "round13_pair_certificate_needed":False,
        "not_proved":"remaining G2/G3; S(6)=2",
        "no_search":"no placements, fixed target points, angle samples or interval trees"}
    Path(__file__).with_name("round23_g4_residual_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({key:value for key,value in result.items() if key!="queries"},ensure_ascii=False,indent=2))
    for row in rows:
        if row["result"]!="unsat":
            print(json.dumps(row,ensure_ascii=False,indent=2))
    assert result["status"]=="all exact checks passed"


if __name__=="__main__":
    main()
