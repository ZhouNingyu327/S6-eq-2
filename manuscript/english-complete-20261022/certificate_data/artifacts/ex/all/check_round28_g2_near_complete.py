"""Exact local checks for the complete near G2 exclusion; no layout search."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name, conditions, theory="QF_NRA"):
        sol=z3.SolverFor(theory);sol.set(timeout=20000);sol.add(*conditions)
        start=time.perf_counter();answer=sol.check()
        row={"name":name,"theory":theory,"result":str(answer),
             "seconds":time.perf_counter()-start}
        if answer!=z3.unsat:
            row["detail"]=str(sol.model()) if answer==z3.sat else sol.reason_unknown()
        print(json.dumps(row),flush=True);assert answer==z3.unsat,row;rows.append(row)
    h,w,d,l,u,mu,c,s,L,E,z=z3.Reals("h w d l u mu c s L E z")
    circle=[mu>1,c>=s,s>0,c*c+s*s==1,h*(1+c)==s]
    query("actual lower RIGHT endpoint forces L2>1+w",circle+[
        w==u-h,c*mu-s*(L-mu)<=1-s*u,L<=1+w])
    query("actual upper RIGHT endpoint/down forces e+d<G",circle+[
        s*mu+c*(E+d)<=1,(E+d)*(1+h)>=1-h])
    query("long TOP leg excess <w-d-hG",[
        h>0,h<1,w==u-h,E+d<(1-h)/(1+h),L<E+u,
        L-1>=w-d-h*(1-h)/(1+h)])
    query("angle quartic concavity",[
        h>=0,12*h<=5,432*h*h-792*h-290>=0])
    P=36*h**4-132*h**3-145*h*h+82*h-11
    query("angle quartic negative",[h>=0,12*h<=5,P>=0])
    query("angle balance scalar",[h>0,h*h+2*h<=1,w>0,12*w<5,
        2*h*(1-h*h-2*h)*(w+h)*5 >= 6*h*(1-h)/(1+h)*(1-h*h)**2])
    query("derived l bound and l+d<2w",[
        h>0,h<1,d>0,w>d+h*(1-h)/(1+h),
        l<d+z3.Q(6,5)*h*(1-h)/(1+h),l+d>=2*w])
    query("derived N+l<6w/5",[
        h>0,h<1,d>0,w>d+h*(1-h)/(1+h),
        l<d+z3.Q(6,5)*h*(1-h)/(1+h),
        w-d-h*(1-h)/(1+h)+l>=z3.Q(6,5)*w])
    aa,bb=z3.Reals("aa bb")
    query("fixed long-leg short function derivative positive",[
        L>1,aa>0,bb>0,aa*aa+bb*bb==1,L-bb<=0])
    query("maximal short leg decreases in L",[
        L>1,bb>0,bb*bb==L*L-1,1-bb-L*L/bb>=0])
    query("Gamma cubic increasing",[
        w>=0,12*w<=5,90*w*w-196*w+92<z3.Q(31,3)])
    R=30*w**3-98*w*w+92*w-25
    query("Gamma cubic negative",[w>=0,12*w<=5,R>=0])
    P5=25*w**5-296*w**3+544*w*w-429*w+200
    query("W-down endpoint0 P5 lower bound",[
        w>=0,12*w<=5,P5<z3.Q(85,4)])
    P7=4*w**7-8*w**6-33*w**5+120*w**4-168*w**3+168*w*w-116*w+32
    query("W-down endpointw P7 lower bound",[
        w>=0,12*w<=5,P7<z3.Q(49,72)])
    tt=z3.Real("tt")
    phi=(1+w)*(1-tt);q=lambda x:x/(2-x)
    domain=[w>0,12*w<5,tt>0,tt*tt==w*(2+w)]
    query("full scalar Gamma",domain+[phi+q(z3.Q(6,5)*w)>=(1-w)*(1-w)])
    query("full W-down endpoint0",domain+[phi+z3.Q(6,5)*w+q(w)>=1])
    query("full W-down endpointw",domain+[phi+w+q(w)+w*w/(2*(1-w))>=1])
    query("full final-grid scalar",domain+[phi+2*w>=1])
    H,cw,sw,A,X=z3.Reals("H cw sw A X")
    query("original W down endpoint forces H>1-d",[
        mu>1,d>0,d<1,cw>0,sw>0,cw*cw+sw*sw==1,
        H*(1+cw)==sw,cw*mu+sw*(mu-d)<=1,H<=1-d])
    query("original W down bounds A",[
        d>0,d<1,H>1-d,H<1,sw*(1+H*H)==2*H,
        A>=0,sw*A<=1,A>=1+d*d/(2*(1-d))])
    query("original W down bounds every horizontal point",[
        mu>1,d>0,d<1,H>1-d,H<1,
        cw*(1+H*H)==1-H*H,sw*(1+H*H)==2*H,
        X>=0,cw*X+sw*mu<=1,X>=q(d)])
    query("q superadditivity",[
        l>=0,d>=0,l+d<1,q(l)+q(d)>q(l+d)])
    BF,FH,B,D,HW,S,U,L4,gap=z3.Reals("BF FH B D HW S U L4 gap")
    query("negative-H W-down parallel budget contradiction",[
        BF>=2*mu-A-S,FH>=mu-l-gap,mu>1,
        A<1+D,S+l+gap+D<1,BF+FH<1],"QF_LRA")
    query("final negative-H grid forces L4+S+U+l+d>5mu-3",[
        mu>1,d>0,gap>=0,gap<d,D+L4+gap>=2*mu,
        A+D+HW<=2,BF>=2*mu-A-S,FH+HW+l+U>=mu,
        BF+FH<1,L4+S+U+l+d<=5*mu-3],"QF_LRA")
    query("q+Delta divided by w <1",[
        w>0,12*w<5,1/(2-w)+w/(2*(1-w))>=1])
    # Symbolic identities verify the explicit hand proof, including convexity.
    W,Hh,V,Ls,a,b=sp.symbols("w h v L a b")
    qsp=lambda t:t/(2-t);delta=lambda t:2*t*t/(1-t*t)
    Delta=lambda t:t*t/(2*(1-t));G=(1-Hh)/(1+Hh);K=2*Hh/(1-Hh*Hh)
    identities=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,name;identities.append(name)
    ident("one minus G",1-G-Hh-Hh*G)
    PP=36*Hh**4-132*Hh**3-145*Hh*Hh+82*Hh-11
    ident("angle balance gap",sp.Rational(6,5)*Hh*G-K*(1-K)*(Hh+sp.Rational(5,12))
          +Hh*PP/(30*(1-Hh*Hh)**2))
    ident("angle P second derivative",sp.diff(PP,Hh,2)-(432*Hh*Hh-792*Hh-290))
    Vg=W*(3*W*W-14*W+18)/((1+W)*(5-3*W))
    V0=W*(27-11*W)/(5*(2-W)*(1+W))
    V1=W*(3*W*W-12*W+10)/(2*(W-2)*(W-1)*(W+1))
    Rsp=30*W**3-98*W*W+92*W-25
    P5sp=25*W**5-296*W**3+544*W*W-429*W+200
    P7sp=4*W**7-8*W**6-33*W**5+120*W**4-168*W**3+168*W*W-116*W+32
    ident("Gamma threshold",Vg-(1+W+qsp(sp.Rational(6,5)*W)-(1-W)**2)/(1+W))
    ident("Gamma square gap",W*(2+W)-Vg**2-
          W*(3*W-2)*Rsp/((1+W)**2*(3*W-5)**2))
    ident("W-down endpoint0 threshold",V0-(W+sp.Rational(6,5)*W+qsp(W))/(1+W))
    ident("W-down endpoint0 square gap",W*(2+W)-V0**2-
          W*P5sp/(25*(W-2)**2*(W+1)**2))
    ident("W-down endpointw threshold",V1-(2*W+qsp(W)+Delta(W))/(1+W))
    ident("W-down endpointw square gap",W*(2+W)-V1**2-
          W*P7sp/(4*(W-2)**2*(W-1)**2*(W+1)**2))
    ident("final-grid square gap",W*(2+W)-(3*W/(1+W))**2-
          W*(W**3+4*(W-sp.Rational(1,2))**2+1)/(1+W)**2)
    ident("delta(q)=Delta",delta(qsp(W))-Delta(W))
    ident("q convexity",sp.diff(qsp(V),V,2)-4/(2-V)**3)
    ident("Delta convexity",sp.diff(Delta(V),V,2)-1/(1-V)**3)
    ident("grid endpoint convexity",
          sp.diff(delta(qsp(W-V))+qsp(W-V)+2*V,V,2)-
          1/(1-W+V)**3-4/(2-W+V)**3)
    constants=[]
    def exact(name,expr,expected):
        assert sp.simplify(expr-expected)==0,name;constants.append(name)
    exact("P at 2/9",PP.subs(Hh,sp.Rational(2,9)),-sp.Rational(947,729))
    exact("P prime at 2/9",sp.diff(PP,Hh).subs(Hh,sp.Rational(2,9)),-sp.Rational(34,81))
    exact("P tangent intercept",
          PP.subs(Hh,sp.Rational(2,9))-sp.Rational(2,9)*sp.diff(PP,Hh).subs(Hh,sp.Rational(2,9)),
          -sp.Rational(293,243))
    exact("R3 endpoint",Rsp.subs(W,sp.Rational(5,12)),-sp.Rational(145,96))
    exact("R3 derivative lower",92-196*sp.Rational(5,12),sp.Rational(31,3))
    exact("P5 lower",200-429*sp.Rational(5,12),sp.Rational(85,4))
    exact("P7 quadratic endpoint",(98*W*W-116*W+32).subs(W,sp.Rational(5,12)),sp.Rational(49,72))
    exact("q plus Delta upper",sp.Rational(12,19)+sp.Rational(5,14),sp.Rational(263,266))
    # Rational strict bounds for sqrt2-1 and the anchored meeting root.
    assert sp.Rational(17,12)**2>2;constants.append("sqrt2-1<5/12")
    assert sp.Rational(27,19)**2>2;constants.append("kappa(sqrt2)<4/15")
    result={"queries":rows,"symbolic_identities":identities,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(r["theory"]=="QF_NRA" for r in rows),
                  "LRA":sum(r["theory"]=="QF_LRA" for r in rows),
                  "symbolic_identities":len(identities),"constants":len(constants)},
        "scope":"Complete near G2 exclusion, with actual endpoint geometry audited separately",
        "not_proved":"Remaining far G2 and S(6)=2"}
    Path(__file__).with_name("round28_g2_near_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
