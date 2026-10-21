"""Exact scalar checks: near RIGHT positive C and far TOP negative C."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        solver=z3.SolverFor(theory);solver.set(timeout=20000);solver.add(*cs)
        started=time.perf_counter();ans=solver.check()
        row={"name":name,"theory":theory,"result":str(ans),"seconds":time.perf_counter()-started}
        if ans!=z3.unsat:
            row["detail"]=str(solver.model()) if ans==z3.sat else solver.reason_unknown()
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    h,e,y,l,d,u,mu,p,s=z3.Reals("h e y l d u mu p s")
    normal=[mu>1,p>=s,s>0,p*p+s*s==1,h*(1+p)==s]
    query("near positive actual P/O forces e<h",normal+[p*mu+s*e<=1,e>=h])
    query("near positive P/down forces d<h-e",normal+[
        p*mu+s*(e+d)<=1,d>=h-e])
    query("near positive P/left forces l<k(h-e)",normal+[
        p*(mu+l)+s*e<=1,l*(1-h*h)>=2*h*(h-e)])
    query("near positive P/up forces u<e+G",normal+[
        s*mu+p*(u-e)<=1,(u-e)*(1+h)>=1-h])
    positive=[h>0,h*h+2*h<=1,e>0,e<h,y>0,y<1,
              e>2*y/(1+y),e>2*h/(1+h)-y]
    query("near positive h>4/15",positive+[15*h<=4])
    query("near positive y>3/20",positive+[20*y<=3])
    query("near positive y<4/15",positive+[15*y>=4])
    query("near positive h-e<1/12",positive+[12*(h-e)>=1])
    query("near positive e-y>1/10",positive+[10*(e-y)<=1])
    x,L,S,z,L4,U4=z3.Reals("x L S z L4 U4")
    query("near strengthened long RIGHT leg",[
        mu>1,e-y>z3.Q(1,10),u>1-y,d>0,
        mu+e-L+u+d<1,10*L<=11])
    query("long L>11/10 forces short S<2/3",[
        x>0,x<1,L>z3.Q(11,10),S<(1-x)/(1+x),
        L*(1-x*x)<=1+x*x,3*S>=2])
    query("TOP chain z<1/12",[
        y>0,15*y<4,z>0,z*(1-2*y*y)<y*y,12*z>=1])
    query("TOP corner L4<145/143",[
        z>0,12*z<1,L4*(1-z*z)<=1+z*z,143*L4>=145])
    A,H,Fh,bF,B,D,gL,Sigma=z3.Reals("A H Fh bF B D gL Sigma")
    query("near nonnegative H bottom scalar contradiction",[
        d>0,12*d<1,A<z3.Q(35,276),S<z3.Q(2,3),
        Sigma==A+S,Sigma>(1-d)*(1-d)])
    hw,cw,sw=z3.Reals("hw cw sw")
    query("W contains near C down endpoint forces hw>11/12",[
        mu>1,d>0,12*d<1,cw>0,sw>0,cw*cw+sw*sw==1,
        hw*(1+cw)==sw,cw*mu+sw*(mu-d)<=1,12*hw<=11])
    query("W down endpoint forces sin>264/265",[
        hw>z3.Q(11,12),hw<1,sw*(1+hw*hw)==2*hw,265*sw<=264])
    query("W bottom A<265/264",[
        sw>z3.Q(264,265),A>=0,sw*A<=1,264*A>=265])
    query("W down endpoint H reach <1/23",[
        hw>z3.Q(11,12),hw<1,(1-hw)/(1+hw)>=z3.Q(1,23)])
    query("F negative H W-down contradiction",[
        mu>1,A<z3.Q(265,264),S<z3.Q(2,3),Fh>z3.Q(5,6),
        bF>=2*mu-A-S,bF+Fh<1],"QF_LRA")
    query("near F negative H joint grid contradiction",[
        mu>1,B<1,d>0,gL>=0,gL<d,
        D+L4+gL>=2*mu,A+D+H<=2,
        bF>=2*mu-A-S,Fh+H+l+U4>=mu,bF+Fh<=B,
        L4+S+U4+l+d<2],"QF_LRA")
    aa,zz,E,omega,T,r,qG,Delta=z3.Reals("aa zz E omega T r qG Delta")
    query("far TOP negative C down d<rho",normal+[
        E>=0,s*E+p*(mu+d)<=1,d*(1-h*h)>=2*h*h])
    query("far TOP negative C l+E<h",normal+[
        E>=0,s*(l+E)+p*mu<=1,l+E>=h])
    query("far TOP negative C r<G+E",normal+[
        s*mu+p*(r-E)<=1,(r-E)*(1+h)>=1-h])
    query("far LEFT meeting plus C deficit forces small z",[
        h>0,h*h+2*h<=1,aa>1-h,aa<1,zz>0,
        zz*(6*aa-1-aa*aa)<(1-aa)*(1-aa),
        zz*(4-4*h-h*h)>=h*h])
    query("far uniform excess E<h/12",[
        h>0,12*h<5,zz>0,2*zz<h*h,E>0,
        E*(1-zz*zz)<=2*zz*zz,12*E>=h])
    query("far small h excess 4E<h/20",[
        h>0,3*h<=1,zz>0,23*zz<9*h*h,E>0,
        E*(1-zz*zz)<=2*zz*zz,80*E>=h])
    query("far first large h z<9/151",[
        h>=z3.Q(1,3),8*h<=3,zz>0,
        zz*(4-4*h-h*h)<h*h,151*zz>=9])
    query("far first large h E<81/11360",[
        zz>0,151*zz<9,E*(1-zz*zz)<=2*zz*zz,11360*E>=81])
    query("far last large h z<25/311",[
        h>=z3.Q(3,8),12*h<5,zz>0,
        zz*(4-4*h-h*h)<h*h,311*zz>=25])
    query("far last large h E<625/48048",[
        zz>0,311*zz<25,E*(1-zz*zz)<=2*zz*zz,48048*E>=625])
    query("far bridge shifted g argument stays positive",[
        h>0,12*h<5,E>0,12*E<h,Delta>=0,Delta<2*E,
        1-h-(1-h)/(1+3*h)-Delta<=0])
    query("far bridge convex endpoint <M",[
        h>0,h*h+2*h<=1,qG==(1-h)/(1+3*h),
        h/(2-h)+qG/(2-qG)>=h/(2-h)+qG])
    # Scalar identities are checked independently of geometric endpoint ownership.
    HH,YY,EE,WW,TT=sp.symbols("h y E w t")
    g=lambda t:(1-t)/(1+t)
    q=lambda t:t/(2-t)
    delta=lambda t:2*t*t/(1-t*t)
    G=g(HH);M=q(HH)+q(G);rho=delta(HH)
    Ab=1-HH-q(G);Av=1-G-q(HH);T0=g(Av)
    identities=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,name
        identities.append(name)
    ident("near e<h inversion",q(HH)-HH*G-
          HH*(-HH*HH+4*HH-1)/((2-HH)*(1+HH)))
    ident("near eta derivative",sp.diff(YY*(1-YY)/(1+YY),YY)-
          (1-2*YY-YY*YY)/(1+YY)**2)
    PN=144*HH**3-600*HH*HH+181*HH+37
    ident("near h-e small endpoint gap",
          2*HH/(1+HH)-(HH-sp.Rational(1,12))-q(HH-sp.Rational(1,12))-
          PN/(12*(1+HH)*(25-12*HH)))
    ident("near hG monotone",sp.diff(HH*G,HH)-
          (1-2*HH-HH*HH)/(1+HH)**2)
    ident("far Ys complement",(1-(1-HH))**2/(6*(1-HH)-1-(1-HH)**2)-
          HH*HH/(4-4*HH-HH*HH))
    ident("far Ab dominates A",Ab-Av-
          3*HH*(1-HH)*(1-2*HH-HH*HH)/((2-HH)*(1+HH)*(1+3*HH)))
    ident("far A derivative",sp.diff(Av,HH)-6*(1-2*HH)/((2-HH)**2*(1+HH)**2))
    ident("far A>h/2 gap",Av-HH/2-
          HH*(HH*HH-7*HH+4)/(2*(2-HH)*(1+HH)))
    ident("far bridge convex endpoint omega=0",
          g(Ab)-(3*HH*HH+1)/(-3*HH*HH+6*HH+1))
    ident("far negative bridge endpoint omega=h",q(HH)+g(Ab+HH)-q(HH)-q(q(G)))
    Pm=3*HH**6-625*HH**5+932*HH**4+850*HH**3-673*HH*HH-305*HH+138
    Pt=2*HH**6-382*HH**5+375*HH**4+444*HH**3-276*HH*HH-142*HH+59
    ident("far M margin h/20",(1-rho)**2-M-HH/20-
          HH*Pm/(20*(2-HH)*(1-HH*HH)**2*(1+3*HH)))
    ident("far T0 margin h/20",(1-rho)**2-T0-HH/20-
          HH*Pt/(20*(1-HH*HH)**2*(1+2*HH-2*HH*HH)))
    ident("far M derivative",sp.diff(M,HH)-
          14*(HH*HH+2*HH-1)/((2-HH)**2*(1+3*HH)**2))
    def at(poly):
        return sum(z3.RealVal(str(c))*(h**int(pw[0]) if pw[0] else 1)
                   for pw,c in sp.Poly(sp.expand(poly),HH).terms())
    query("far M margin polynomial decreases",[
        h>=0,3*h<=1,at(sp.diff(Pm,HH))>z3.Q(2,27)-305-z3.Q(736,9)*h])
    query("far T0 margin polynomial decreases",[
        h>=0,3*h<=1,at(sp.diff(Pt,HH))>=0])
    query("near small a cubic concavity",[
        12*h>=1,12*h<=5,at(sp.diff(PN,HH,2))>=0])
    query("far A>h/2",[
        h>0,12*h<5,h*h-7*h+4<=0])
    query("remaining near negative C: up cannot hit upper second face",
          normal+[p*(u-e)>=s*mu,p*mu+s*(u-e)<=1])
    query("remaining near negative C: down cannot hit upper first face",
          normal+[s*(e+d)>=p*mu,s*mu+p*(e+d)<=1])
    constants=[]
    def const(name,value):
        assert bool(value),name
        constants.append(name)
    const("near hG(4/15)",(HH*G).subs(HH,sp.Rational(4,15))==sp.Rational(44,285))
    const("near lower y>3/20",sp.Rational(44,285)>sp.Rational(3,20))
    const("near eta(3/20)>1/10",sp.Rational(51,460)>sp.Rational(1,10))
    const("near cubic first endpoint",PN.subs(HH,sp.Rational(1,12))==48)
    const("near cubic last endpoint",PN.subs(HH,sp.Rational(5,12))==sp.Rational(56,3))
    const("near Yc(4/15)<1/12",sp.Rational(16,193)<sp.Rational(1,12))
    const("near long/short constants",sp.Rational(13,12)<sp.Rational(11,10))
    const("near W A bound",sp.Rational(1,12)+sp.Rational(1,23)==sp.Rational(35,276))
    const("near Sigma bound",sp.Rational(35,276)+sp.Rational(2,3)==sp.Rational(73,92))
    const("near root scalar gap",sp.Rational(73,92)<sp.Rational(11,12)**2)
    const("near Wdown bottom gap",2-sp.Rational(265,264)-sp.Rational(2,3)==sp.Rational(29,88))
    const("near Wdown contradiction",sp.Rational(29,88)+sp.Rational(5,6)>1)
    const("near negative H final grid cap",sp.Rational(145,143)+sp.Rational(2,3)+
          sp.Rational(1,12)+sp.Rational(1,6)<2)
    const("far Pm endpoint",Pm.subs(HH,sp.Rational(1,3))==sp.Rational(160,81))
    const("far Pt endpoint",Pt.subs(HH,sp.Rational(1,3))==sp.Rational(368,729))
    const("far small error",sp.Rational(1,22)<sp.Rational(1,20))
    const("far M third",M.subs(HH,sp.Rational(1,3))==sp.Rational(8,15))
    const("far T0 third",T0.subs(HH,sp.Rational(1,3))==sp.Rational(7,13))
    const("far first large maximum",sp.Rational(8,15)<sp.Rational(7,13))
    const("far first large diameter",sp.Rational(7,13)+sp.Rational(81,2840)<sp.Rational(7,12))
    const("far M three eighths",M.subs(HH,sp.Rational(3,8))==sp.Rational(116,221))
    const("far T0 three eighths",T0.subs(HH,sp.Rational(3,8))==sp.Rational(49,94))
    const("far last large maximum",sp.Rational(49,94)<sp.Rational(116,221))
    const("far last large diameter",sp.Rational(116,221)+sp.Rational(625,12012)<sp.Rational(7,12))
    result={"scope":"Near G2 RIGHT gap / positive C entire branch; far G2 TOP gap / negative C entire branch",
            "queries":rows,"symbolic_identities":identities,"constants":constants,
            "totals":{"UNSAT":len(rows),"NRA":sum(v["theory"]=="QF_NRA" for v in rows),
                      "LRA":sum(v["theory"]=="QF_LRA" for v in rows),
                      "symbolic_identities":len(identities),"constants":len(constants)}}
    (Path(__file__).resolve().parent/"round27_g2_two_branch_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
