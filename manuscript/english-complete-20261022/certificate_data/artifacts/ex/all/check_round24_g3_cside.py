"""Exact small checks for C-side G3 empty F vertical and nonempty reduction."""
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
        assert answer==z3.unsat,row
        rows.append(row)

    mu,B,ell,u,d,S1,S4,U1,U4=z3.Reals(
        "c24_mu c24_B c24_ell c24_u c24_d c24_S1 c24_S4 c24_U1 c24_U4")
    query("C cannot directly join an anchored vertical ray",[
        mu>1,B<1,S1<1,S4+U4<=B,
        ell>=2*mu-S1-S4,ell+u<=B,u+U4>=mu],"QF_LRA")
    c,s,r=z3.Reals("c24_c c24_s c24_r")
    query("original right corner cannot hold C right/up endpoints together",[
        c>0,s>0,c*c+s*s==1,mu>1,r>=0,u>=0,r+u<1,
        c*(mu-r)+s*mu<=1,c*mu+s*(mu-u)<=1])
    a,x,t=z3.Reals("c24_a c24_x c24_t")
    query("inverse g bound gives anchored angle upper",[
        a>0,a<1,x>=0,x<=a,t>0,t<1,
        1-a+x<(1-t)/(1+t),t>=(a-x)/(2-a+x)])
    query("joint ray budget has nonnegative product",[
        a>0,a<1,x>=0,x<=a,
        a/(2-a)-(a-x)/(2-a+x)-x/(2-x)<0])
    vals=z3.Reals("c24_v1 c24_v2 c24_v3 c24_v4 c24_v5 c24_v6")
    query("six true nonempty vertical pairs cannot cover the three target lines",
          [mu>1,B<1,*[v<=B for v in vals],sum(vals)>=6*mu],"QF_LRA")
    vC,vF,J2,J3=z3.Reals("c24_vC c24_vF c24_J2 c24_J3")
    query("C-side joint vertical budget J2+J3+vF>=4mu-3B",[
        ell>=2*mu-S1-S4,ell+vC<=B,S1+U1<=B,S4+U4<=B,
        vC+vF+U1+U4+J2+J3>=2*mu,
        J2+J3+vF<4*mu-3*B],"QF_LRA")
    query("g(1-a+x)+x<=a for both C orientations",[
        a>0,a<1,x>=0,x<=a,(a-x)/(2-a+x)+x>a])
    Ahat,Dhat,t1,t4,qd,qD,b,E2=z3.Reals(
        "c24_Ahat c24_Dhat c24_t1 c24_t4 c24_qd c24_qD c24_b c24_E2")
    query("nonempty F and true RIGHT gap contradict joint C bridge budgets",[
        Ahat+Dhat<1,qD<Dhat,t1+u<Ahat,t4+qd<qD,
        E2<t1+qd,b<t4+u,b>1-E2],"QF_LRA")
    L=z3.Real("c24_L")
    five=z3.Reals("c24_z1 c24_z2 c24_z3 c24_z4 c24_z5")
    query("five real nonempty vertical pairs force L>=6mu-5B",[
        *[v<=B for v in five],sum(five)+L>=6*mu,L<6*mu-5*B],"QF_LRA")
    z,v=z3.Reals("c24_sqrt2 c24_root")
    query("B second branch below mu-sqrt(mu^2-1)",[
        z>0,z*z==2,4*mu>=3*z,mu<=z,v>=0,v*v==mu*mu-1,
        2*(z-mu)>mu-v])
    query("conditional mu+5sqrt(mu^2-1)<=sqrt2 gives quadratic root cap",[
        mu>1,z>0,z*z==2,v>=0,v*v==mu*mu-1,mu+5*v<=z,
        24*mu*mu+2*z*mu>27])

    A,X,C,SS,M=sp.symbols("a x c s mu")
    g=lambda z:(1-z)/(1+z)
    q=lambda z:z/(2-z)
    checks=[
        sp.cancel(g(g(A))-A),
        sp.cancel(q(A)-g(1-A+X)-q(X)-
            X*(A-X)*(4-A)/((2-A)*(2-X)*(2-A+X))),
        sp.expand(C+SS-1-C*SS+(1-C)*(1-SS)),
        sp.cancel((1-SS*M)/C+(1-C*M)/SS-
            (C+SS-M)/(C*SS)-M*(1-C*C-SS*SS)/(C*SS)),
        sp.cancel(A+g(A)-1+A*(1-A)/(1+A)),
        sp.simplify(24*((5*sp.sqrt(26)-sp.sqrt(2))/24)**2+
                    2*sp.sqrt(2)*(5*sp.sqrt(26)-sp.sqrt(2))/24-27)]
    assert checks==[0]*6
    result={"status":"all exact C-side small checks passed","queries":rows,
            "totals":{"UNSAT":len(rows),
                      "NRA":sum(row["theory"]=="QF_NRA" for row in rows),
                      "LRA":sum(row["theory"]=="QF_LRA" for row in rows),
                      "symbolic_identities":len(checks),"constants":0},
            "scope":"C-side G3 F vertical empty excluded; nonempty F necessary bridge ownership",
            "not_proved":"Entire C-side G3, diagonal G3, remaining G2, S(6)=2"}
    Path(__file__).with_name("round24_g3_cside_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
