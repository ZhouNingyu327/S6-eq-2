"""Exact local arithmetic for the no-TOP continuation; old adjacent lemma is assumed."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_LRA"):
        solver=z3.SolverFor(theory);solver.set(timeout=20000);solver.add(*cs)
        start=time.perf_counter();ans=solver.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    mu,B,v=z3.Reals("mu B v")
    query("C side+bottom and F H nonempty impossible",[
        mu>1,B<1,v<mu,12*mu<=8+3*B+v])
    query("C bottom and F H nonempty, three meetings",[
        mu>1,B<1,12*mu<=8+2*B+2*mu])
    Sigma,b,f=z3.Reals("Sigma b f")
    query("real bottom and H budget gives Sigma>1+f",[
        mu>1,B<1,b>=2*mu-Sigma,b+f<=B,Sigma<=1+f])
    a,x=z3.Reals("a x")
    query("joint bottom angles a+x+3ax<1",[
        a>0,a<1,x>0,x<1,
        Sigma<(1-a)/(1+a)+(1-x)/(1+x),Sigma>1,
        a+x+3*a*x>=1],"QF_NRA")
    hc,L3,L4,S1,S2,U1,U2,z,t=z3.Reals("hc L3 L4 S1 S2 U1 U2 z t")
    query("two adjacent corner budgets give strengthened C horizontal chord",[
        mu>1,B<1,hc>=4*mu-B-S1-S2-U1-U2,U1<a,U2<x,
        L4+S1+a+2*z-z*z<=2,L3+S2+x+2*t-t*t<=2,
        L3+L4>=2*mu,
        hc<=1+2*z-z*z+2*t-t*t],"QF_NRA")
    u=z3.Real("u")
    for label,m,n in [("z larger",z,t),("t larger",t,z)]:
        query("TOP midpoint repeated contradiction: "+label,[
            m>=n,n>0,m<1,u>1-m,
            hc>1+2*m-m*m+2*n-n*n,hc+u*u<=2],"QF_NRA")
    D,J,HH=z3.Reals("D J HH")
    query("CORRECTED actual TOP/H parallel pair gives H<delta(z)",[
        mu>1,B<1,z>0,z<1,D+L4>=2*mu,D+HH<=B,
        L4*(1-z*z)<=1+z*z,HH*(1-z*z)>=2*z*z],"QF_NRA")
    A,HH,L2=z3.Reals("A HH L2")
    query("CORRECTED actual RIGHT/V parallel pair gives J<delta(x)",[
        mu>1,B<1,x>0,x<1,A+L2>=2*mu,A+J<=B,
        L2*(1-x*x)<=1+x*x,J*(1-x*x)>=2*x*x],"QF_NRA")
    aa,xx,m,n=sp.symbols("a x m n")
    assert sp.cancel((1-aa)/(1+aa)+(1-xx)/(1+xx)-1-
                     (1-aa-xx-3*aa*xx)/((1+aa)*(1+xx)))==0
    assert sp.expand(1+2*m-m*m+2*n-n*n+(1-m)**2-(2+2*n-n*n))==0
    result={"queries":rows,"totals":{"UNSAT":len(rows),
        "NRA":sum(r["theory"]=="QF_NRA" for r in rows),
        "LRA":sum(r["theory"]=="QF_LRA" for r in rows),"identities":2},
        "scope":"No-TOP far: F H nonempty excludes all C bottom contact; "
                "three meetings excludes original W repeating TOPmid; "
                "exact three-side-status classification is proved in text",
        "old_adjacent_lemma":"round13 assumed, not replayed; includes its 266-coefficient certificate",
        "not_proved":"Any entire remaining side-gap or three-meeting family; S(6)=2",
        "not_in_frozen_round29_zip":True}
    Path(__file__).with_name("round29_no_top_structure_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
