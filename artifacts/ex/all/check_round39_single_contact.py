"""Exact small checks for LEFT right-contact and three-meeting structure."""
from pathlib import Path
import json,time
import sympy as sp
import z3

def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        solver=z3.SolverFor(theory);solver.set(timeout=30000);solver.add(*cs)
        start=time.perf_counter();ans=solver.check()
        row={"name":name,"theory":theory,"result":str(ans),"seconds":time.perf_counter()-start}
        if ans!=z3.unsat:row["detail"]=str(solver.model()) if ans==z3.sat else solver.reason_unknown()
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    eta,u,d,r,K,E,t,w,L,S,z,A,mu,v,b,Sigma=z3.Reals(
        "eta u d r K E t w L S z A mu v b Sigma")
    q=lambda a:a/(2-a)
    Delta=lambda a:a*a/(2*(1-a))
    G=(1-eta)/(1+eta)
    query("LEFT direct Q2 two roots give r<1/2",[
        K>0,K<=1,u>0,d>0,u+d<1,r>0,r<=K*u,K*r<=d,2*r>=1])
    query("LEFT direct Q2 preliminary t is below one",[
        eta>0,eta<z3.Q(3,7),w>0,w<z3.Q(2,7),u==eta+w,
        r>0,2*r<1,t==q(u)+Delta(r),t>=1])
    query("actual V bridge equivalent deficit inequality",[
        E>0,E<1,t>0,t<1,(1-E)/(1+E)+t>1,E>=q(t)])
    query("small root Delta is below ud",[
        r>0,2*r<1,K>0,u>0,d>0,r<=K*u,K*r<=d,Delta(r)>=u*d])
    query("bridge implies original eta lower bound on u",[
        eta>0,u>0,u<1,d>0,E==2*eta/(1+eta)+d,
        E<q(u)+u*d,u<=4*eta/(1+3*eta)])
    query("w cap forces eta<1/4",[
        eta>=z3.Q(1,4),eta<=z3.Q(5,12),u-eta<z3.Q(2,7),
        u>4*eta/(1+3*eta)])
    query("eta and w caps force small r",[
        eta>0,eta<z3.Q(1,4),K*(1-eta*eta)==2*eta,
        u-eta<z3.Q(2,7),u>0,r<=K*u,7*r>=2])
    query("improved t is below one half",[
        u>0,u<z3.Q(15,28),r>0,7*r<2,
        t==q(u)+Delta(r),2*t>=1])
    query("q contraction and Delta coefficient",[
        t>0,2*t<1,r>0,7*r<2,
        z3.Or(q(t)>=2*t/3,Delta(r)>=7*r*r/10)])
    query("new linear deficit budget",[
        eta>0,4*eta<1,u>0,28*u<15,d>0,E==2*eta/(1+eta)+d,
        E<2*q(u)/3+7*u*d/15,
        8*eta/5+3*d/4>=56*u/123])
    query("combine explicit coefficient slack",[
        eta>0,u>0,d>0,S<16*u/45,
        8*eta/5+3*d/4<56*u/123,2*d+S>=8*(u-eta)/5],"QF_LRA")
    query("Phi and actual bottom square contradiction",[
        w>0,7*w<2,v>0,v*v==w,d>0,
        5*v/4<2*d-d*d+S,2*d+S<8*w/5])
    query("three meetings, direct QU gives upper root lower bound",[
        u>1-z,z<z3.Q(4,15),u<=z3.Q(38,79)],"QF_LRA")
    query("three meetings, actual W V bridge gives upper root lower bound",[
        u>0,u<1,z<z3.Q(4,15),A>z3.Q(7,12),
        A<z+q(u),u<=z3.Q(38,79)])
    query("C upper root excludes any BOTTOM point by diameter",[
        mu>1,u>z3.Q(38,79),(mu+u)*(mu+u)<=2])
    query("same F triangle area gives bottom budget",[
        mu>1,d>0,d<1,b>=2*mu-Sigma,v>=mu-d,b>0,v>0,b*v<=1,
        Sigma<=2-1/(1-d)])
    query("same F square budget remains legal after C avoids bottom",[
        mu>1,d>0,d<1,b>=2*mu-Sigma,v>=mu-d,b+v*v<=2,
        Sigma<=(1-d)*(1-d)])
    query("LEFT top contact root lemma r<2w/3",[
        eta>0,12*eta<=5,w>0,12*w<=5,u==eta+w,
        K*(1-eta*eta)==2*eta,r<=K*u,K*r<q(u)-2*eta/(1+eta),
        3*r>=2*w])
    P=-9*eta**3-5*eta**2*w+18*eta**2+4*eta*w*w-2*eta*w-9*eta+3*w
    R=3*eta**6+7*eta**5-41*eta**4-40*eta**3+71*eta**2-27*eta+3
    Q=324*eta**3-573*eta**2+329*eta-45
    query("root lemma P increases with w",[
        eta>=0,12*eta<=5,w>=0,3-2*eta-5*eta*eta+8*eta*w<=0])
    query("root lemma large eta cubic positive",[
        5*eta>=1,12*eta<=5,Q<=0])
    query("root lemma small eta sixth degree positive",[
        eta>=0,5*eta<=1,R<=0])
    query("global TOP meeting with H bridge gives S2<5/12",[
        r>0,r<z3.Q(5,18),t>0,t<z3.Q(5,12)+q(r),S<q(t),
        S>=z3.Q(5,12)])
    query("w<1/3 strengthens S2 to 13/35",[
        r>0,r<z3.Q(2,9),t>0,t<z3.Q(5,12)+q(r),S<q(t),
        S>=z3.Q(13,35)])
    query("w<9/28 excludes eta>=1/4",[
        eta>=z3.Q(1,4),12*eta<=5,w<z3.Q(9,28),
        w>3*eta*(1-eta)/(1+3*eta)])
    query("top contact new linear d cap",[
        eta>0,4*eta<1,u>0,7*u<4,d>0,
        2*eta/(1+eta)+d<q(u),
        d>=7*u/10-8*eta/5])
    query("actual horizontal W bridge refined deficit is small",[
        u>0,7*u<4,r>0,2*r<1,K>0,15*K<8,r<=K*u,
        t==Delta(u)+q(r),
        z3.Or(t>=46*u/45,t>=z3.Q(2,3))])
    query("refined H bridge bounds S2",[
        u>0,t>0,t<z3.Q(2,3),t<46*u/45,S<q(t),S>=23*u/30])
    query("top contact linear loss budget",[
        eta>0,u>0,d>0,d<7*u/10-8*eta/5,S<23*u/30,
        2*d+S>=13*(u-eta)/6],"QF_LRA")
    query("top contact final Phi loss contradiction",[
        w>0,28*w<9,v>0,v*v==w,d>0,
        5*v/4<2*d-d*d+S,2*d+S<13*w/6])

    U,D,H,W=sp.symbols("u d eta w")
    ids=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.cancel(expr));ids.append(name)
    ident("area vs square budget difference",
          2-1/(1-D)-(1-D)**2-D*(1-3*D+D*D)/(1-D))
    ident("bottom budget derivative in mu",
          sp.diff(2*U-1/(U-D),U)-(2+1/(U-D)**2))
    pp=-9*H**3-5*H**2*W+18*H**2+4*H*W**2-2*H*W-9*H+3*W
    rr=3*H**6+7*H**5-41*H**4-40*H**3+71*H**2-27*H+3
    qq=324*H**3-573*H**2+329*H-45
    ident("root lemma projection numerator",
          (H+W)/(2-H-W)-2*H/(1+H)-4*H*W/(3*(1-H**2))
          -pp/(3*(1-H**2)*(2-H-W)))
    ident("root lemma large w endpoint",pp.subs(W,sp.Rational(5,12))+qq/36)
    ident("root lemma small eta endpoint",
          pp.subs(W,3*H**2/(1-3*H-H**2))
          +3*H*rr/(H**2+3*H-1)**2)
    ident("eta lower-bound quadratic at w=9/28",
          28*(1+3*H)*(3*H*(1-H)/(1+3*H)-sp.Rational(9,28))
          -(57*H-84*H**2-9))
    constants=[]
    def exact(name,expr,value):
        assert sp.factor(expr)==value,(name,sp.factor(expr))
        constants.append({"name":name,"value":str(value)})
    exact("t cap",sp.Rational(15,41)+sp.Rational(2,35),sp.Rational(607,1435))
    exact("half minus t cap",sp.Rational(1,2)-sp.Rational(607,1435),sp.Rational(221,2870))
    exact("u coefficient gap",sp.Rational(8,5)-sp.Rational(448,369)-sp.Rational(16,45),
          sp.Rational(56,1845))
    exact("eta coefficient gap",sp.Rational(64,15)-sp.Rational(8,5),sp.Rational(8,3))
    exact("strong loss squared margin",sp.Rational(25,16)-sp.Rational(64,25)*sp.Rational(2,7),
          sp.Rational(2327,2800))
    exact("C bottom diameter margin",(1+sp.Rational(38,79))**2-2,sp.Rational(1207,6241))
    exact("root cubic endpoint",qq.subs(H,sp.Rational(1,5)),sp.Rational(59,125))
    exact("root cubic derivative endpoint",sp.diff(qq,H).subs(H,sp.Rational(5,12)),sp.Rational(81,4))
    exact("root sixth degree endpoint",rr.subs(H,sp.Rational(1,5)),sp.Rational(888,15625))
    exact("root sixth degree derivative cap",-27+sp.Rational(118,5)+sp.Rational(193,3125),
          -sp.Rational(10432,3125))
    exact("Phi(1/3) root comparison",7-sp.Rational(21,8)**2,sp.Rational(7,64))
    exact("Phi(9/28) rational upper gap",sp.Rational(1,5)-sp.Rational(37,196),sp.Rational(11,980))
    exact("global H bridge S2 cap",q(sp.Rational(5,12)+sp.Rational(5,31)),sp.Rational(215,529))
    exact("global H cap gap",sp.Rational(5,12)-sp.Rational(215,529),sp.Rational(65,6348))
    exact("second global H cap",q(sp.Rational(5,12)+sp.Rational(1,8)),sp.Rational(13,35))
    exact("eta quadratic left endpoint",(57*H-84*H**2-9).subs(H,sp.Rational(1,4)),sp.Integer(0))
    exact("eta quadratic right endpoint",(57*H-84*H**2-9).subs(H,sp.Rational(5,12)),sp.Rational(1,6))
    exact("top loss eta coefficient gap",sp.Rational(16,5)-sp.Rational(13,6),sp.Rational(31,30))
    exact("top final squared loss gap",sp.Rational(25,16)-sp.Rational(169,36)*sp.Rational(9,28),
          sp.Rational(3,56))
    result={"queries":rows,"symbolic_identities":ids,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(r["theory"]=="QF_NRA" for r in rows),
        "LRA":sum(r["theory"]=="QF_LRA" for r in rows),
        "symbolic_identities":len(ids),"constants":len(constants)},
        "scope":"Entire LEFT real-gap family excluded; three meetings C avoids BOTTOM",
        "not_proved":"F empty three meetings; S(6)=2"}
    Path(__file__).with_name("round39_single_contact_checks.json").write_text(
        json.dumps(result,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)

if __name__=="__main__":
    main()
