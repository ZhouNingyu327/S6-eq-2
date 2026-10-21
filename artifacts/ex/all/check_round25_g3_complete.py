"""Exact local checks for the complete G3 proof, without layout/point searches."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,premises,theory="QF_NRA"):
        sol=z3.SolverFor(theory)
        sol.set(timeout=20000)
        sol.add(*premises)
        start=time.perf_counter()
        answer=sol.check()
        row={"name":name,"theory":theory,"result":str(answer),
             "seconds":time.perf_counter()-start}
        if answer!=z3.unsat:
            row["detail"]=str(sol.model()) if answer==z3.sat else sol.reason_unknown()
        print(json.dumps(row),flush=True)
        assert answer==z3.unsat,row
        rows.append(row)

    mu,L,t,U,p,s,H,K,v=z3.Reals("g25_mu g25_L g25_t g25_U g25_p g25_s g25_H g25_K g25_v")
    angle=[t>0,t<1,L>1,L*L<=2,L*(1-t*t)<=1+t*t,2*t*L<=1+t*t,
           K*(3-L)==L-1]
    query("TOP exit / R excludes positive unit orientation",[
        mu>1,L>=mu,L*L<=2,p>0,s>=0,p>=s,p*p+s*s==1,
        s*(2*mu-L)+p*mu<=1])
    negative=[mu>1,L>=mu,L*L<=2,p>0,s>0,p>=s,p*p+s*s==1,
              H*(1+p)==s,p*(2*mu-L)+s*mu<=1,K*(3-L)==L-1]
    query("TOP exit / R pins negative halfangle H<kappa",negative+[H>=K])
    query("positive central vertical point is below negative H",[
        mu>1,p>0,s>0,p*p+s*s==1,H*(1+p)==s,
        p*mu+s*v<=1,v>=H])
    query("full local three-point obstruction, independent direct check",[
        mu>1,L>=mu,t>0,t<1,2*t*L<=1+t*t,U<t,
        p>0,s>0,p>=s,p*p+s*s==1,
        p*mu+s*(mu-U)<=1,p*(2*mu-L)+s*mu<=1])
    query("historical kappa<t checked from actual projection caps",angle+[K>=t])
    query("historical kappa<1-t checked from actual projection caps",angle+[K>=1-t])
    query("historical kappa<4/15 checked from diameter",[
        L>1,L*L<=2,K*(3-L)==L-1,15*K>=4])
    query("new q(kappa)<eta for entire actual angle domain",
          angle+[K>0,K<1,K/(2-K)>=t*(1-t)/(1+t)])

    a,w,x,h,u,d,r=z3.Reals("g25_a g25_w g25_x g25_h g25_u g25_d g25_r")
    query("two-step cascade x<w/3",[
        w>0,15*w<4,x>0,x*(1-2*w*w)<w*w,3*x>=w])
    query("kappa ratio w<2a/3, cosine range",[
        a>0,5*a<=2,w>0,w*(1-2*a*a)<a*a,3*w>=2*a])
    query("kappa ratio w<2a/3, global range",[
        5*a>=2,15*w<4,3*w>=2*a],"QF_LRA")
    query("cascade x<a/4 and x<(1-a)/3",[
        x>0,3*x<w,3*w<2*a,w<1-a,
        z3.Or(4*x>=a,3*x>=1-a)],"QF_LRA")
    query("C opposite vertical rays u<g(d)",[
        a>0,a<1,u>=0,d>=0,u<a,d<(1-a)/(1+a),
        u>=(1-d)/(1+d)])

    B,ell,S4,U4=z3.Reals("g25_B g25_ell g25_S4 g25_U4")
    query("LEFT true gap excludes C direct TOP inner endpoint",[
        mu>1,B<1,ell>=mu-S4,S4+U4<=B,ell+u<=B,u+U4>=mu],"QF_LRA")
    query("LEFT meeting direct TOP feedback loop impossible",[
        x>0,x<1,w<1-a,x<w,d>1-a,d<h,h*(2-x)<x])
    query("C direct TOP inner endpoint gives h<x/(2-x)",[
        x>0,x<1,h>0,h<1,u<(1-h)/(1+h),u>1-x,h*(2-x)>=x])
    query("small C lower ray gives next angle x<h/12",[
        h>0,12*h<5,w>0,w<h*h/2,8*w<1,
        x>0,x*(1-2*w*w)<w*w,12*x>=h])

    f0=(1-a)/(1+a)+a/(4-3*a)
    query("F0 decreases on 0<a<=1/2",[
        a>0,2*a<=1,-2/(1+a)**2+4/(4-3*a)**2>=0])
    query("large-a convex base bound on [1/2,3/5]",[
        2*a>=1,5*a<=3,f0>z3.RealVal("8/15")])
    query("large-a constant base bound for a>=3/5",[
        5*a>=3,a<1,(1-a)/(1+a)+z3.RealVal("5/19")>z3.RealVal("8/15")])
    query("small-a fullbridge sum bound",[
        a>0,5*a<=2,x<a/4,U<5*a/14,
        (1-a)/(1+a)+x+U>=1-23*a/28])
    query("small-a squared ray lower estimate",[
        a>0,5*a<=2,a*a/(1-a)>2*a/3])
    query("global cascade cap x<16/193",[
        w>0,15*w<4,x*(1-2*w*w)<w*w,193*x>=16])
    for threshold,capw,capx in [
        ("9/20","121/599","14641/329519"),
        ("12/25","169/1031","28561/1005839"),
        ("1/2","1/7","1/47")]:
        query("Ys supplies cascade w cap for a>="+threshold,[
            a>=z3.RealVal(threshold),a<1,w>0,
            w*(6*a-1-a*a)<(1-a)*(1-a),w>=z3.RealVal(capw)])
        query("Yc supplies x cap "+capx,[
            w>0,w<z3.RealVal(capw),
            x*(1-2*w*w)<w*w,x>=z3.RealVal(capx)])

    S2,E3,b,vF=z3.Reals("g25_S2 g25_E3 g25_b g25_vF")
    query("nonempty F right/central parallel pair requires S2+E3>1",[
        mu>1,B<1,vF>=0,b+vF<=B,b>=2*mu-S2-E3,S2+E3<=1],"QF_LRA")
    query("LEFT gap forces alpha>t4 from C parallel rays",[
        x>0,x<1,a>0,a<1,S4<(1-x)/(1+x),U<a,S4+U>1,a<=x])
    query("nonempty final LEFT-gap contradiction",[
        x>0,x<1,a>x,a<1,S2<(1-a)/(1+a),E3<2*x/(1+x),S2+E3>1])
    query("nonempty final LEFT-meeting contradiction",[
        x>0,a>4*x,S2<1-a,E3<2*x,S2+E3>1],"QF_LRA")

    A,D,uu,dd=sp.symbols("A D u d")
    T,LL,KK,HH=sp.symbols("t L K h")
    g=lambda z:(1-z)/(1+z)
    q=lambda z:z/(2-z)
    eta=lambda z:z*(1-z)/(1+z)
    yc=lambda z:z*z/(1-2*z*z)
    ys=lambda z:(1-z)**2/(6*z-1-z*z)
    identities=[]
    def identity(name,expr):
        assert sp.cancel(expr)==0,name
        identities.append(name)
    identity("q Yc",q(yc(T))-T*T/(2-5*T*T))
    identity("q Ys",q(ys(T))-(1-T)**2/(14*T-3-3*T*T))
    identity("eta-1/6",eta(T)-sp.Rational(1,6)-
             (3*T-1)*(1-2*T)/(6*(1+T)))
    identity("Ys derivative",sp.diff(ys(T),T)-4*(T*T-1)/(6*T-1-T*T)**2)
    identity("Ys(1-h)",ys(1-HH)-HH*HH/(4-4*HH-HH*HH))
    identity("q kappa endpoint relation",
             ((LL-1)/(3-LL))/(2-(LL-1)/(3-LL))-(LL-1)/(7-3*LL))
    identity("eta joins x to 1-g(x)",T+eta(T)-(1-g(T)))
    identity("convex bridge corner 0-0",
             (g(1-A+uu-q(dd))+g(1-D+dd)+q(uu)).subs({uu:0,dd:0})-
             q(A)-q(D))
    identity("convex bridge corner 0-D",
             (g(1-A+uu-q(dd))+g(1-D+dd)+q(uu)).subs({uu:0,dd:D})-
             g(1-A-q(D)))
    identity("convex bridge corner A-0",
             (g(1-A+uu-q(dd))+g(1-D+dd)+q(uu)).subs({uu:A,dd:0})-
             q(A)-q(D))
    identity("convex bridge corner A-D",
             (g(1-A+uu-q(dd))+g(1-D+dd)+q(uu)).subs({uu:A,dd:D})-
             q(q(D))-q(A))
    identity("F0 derivative",
             sp.diff(g(T)+T/(4-3*T),T)+2/(1+T)**2-4/(4-3*T)**2)
    identity("F0 positive second derivative",
             sp.diff(g(T)+T/(4-3*T),T,2)-4/(1+T)**3-24/(4-3*T)**3)

    R=sp.Rational
    constants={
        "2-sqrt2>sqrt2-1":3>2*sp.sqrt(2),
        "q(4/15)=2/13":q(R(4,15))==R(2,13),
        "2/13<1/6":R(2,13)<R(1,6),
        "3/13<1/2":R(3,13)<R(1,2),
        "2/13<1/3":R(2,13)<R(1,3),
        "60/193<1/3":R(60,193)<R(1,3),
        "2/9<1/4":R(2,9)<R(1,4),
        "125/6696<1/12":R(125,6696)<R(1,12),
        "small range slope":R(23,28)>R(2,3),
        "middle1 strict margin":R(4,7)+R(16,193)<R(359,440)**2,
        "middle2 strict margin":R(844,1537)+R(14641,329519)<R(253,325)**2,
        "middle3 strict margin":R(319,592)+R(28561,1005839)<R(4,7),
        "large range strict margin":R(8,15)+R(1,47)<R(4,7),
        "large constant base":R(1,4)+R(5,19)<R(8,15),
        "F0 at 2/5":g(R(2,5))+R(2,5)/(4-3*R(2,5))==R(4,7),
        "F0 at 9/20":g(R(9,20))+R(9,20)/(4-3*R(9,20))==R(844,1537),
        "F0 at 12/25":g(R(12,25))+R(12,25)/(4-3*R(12,25))==R(319,592),
        "F0 at 3/5":g(R(3,5))+R(3,5)/(4-3*R(3,5))==R(23,44),
    }
    assert all(bool(value) for value in constants.values())
    result={"status":"all exact new G3 checks passed","queries":rows,
            "totals":{"UNSAT":len(rows),
                      "NRA":sum(z["theory"]=="QF_NRA" for z in rows),
                      "LRA":sum(z["theory"]=="QF_LRA" for z in rows),
                      "symbolic_identities":len(identities),"constants":len(constants)},
            "symbolic_identities":identities,
            "constants":{name:bool(v) for name,v in constants.items()},
            "scope":"Complete G3 proof scalar checks; geometric endpoint/host audit separate",
            "not_proved":"Remaining G2; S(6)=2"}
    Path(__file__).with_name("round25_g3_complete_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({"status":result["status"],"totals":result["totals"]}),flush=True)


if __name__=="__main__":
    main()
