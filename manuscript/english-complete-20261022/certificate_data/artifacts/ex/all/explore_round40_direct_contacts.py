"""Exploration of a specified local necessary-condition lemma, not layouts."""
import json, time
from pathlib import Path
import z3

a,x,u,d,c,s,L,S,T = z3.Reals("a x u d c s L S T")
base = [
    a>0,a<1,x>0,x<1,u>z3.Q(11,15),u<1,d>0,d<1,
    c>=s,s>=0,c*c+s*s==1,
    L>2-u/(2-u),
    L*(1-a*a)<=1+a*a,2*a*L<=1+a*a,
    S*(1-a*a)==1+a*a-2*a*L,S>=0,
    T*(1+x)==1-x,T>=0,
    S+T>z3.Q(7,12),S+T>(1-d)*(1-d),
    (2-S-T)*(1-d)<1,
    c*(2-a-x)<=1,c*(u+d)<=1,
]
positive = [
    c*(1-x)+s*d<=1,s*u+c*(1-a)<=1,
    s*(1-a)+c*d<=1,c*u+s*(1-x)<=1,
]
negative = [
    c*(1-a)+s*d<=1,s*u+c*(1-x)<=1,
    s*(1-x)+c*d<=1,c*u+s*(1-a)<=1,
]
rows=[]
for name, extra in [("direct both positive C",positive),
                    ("direct both negative C",negative)]:
    solver=z3.SolverFor("QF_NRA"); solver.set(timeout=20000)
    solver.add(*(base+extra))
    start=time.perf_counter(); ans=solver.check()
    row={"name":name,"result":str(ans),"seconds":time.perf_counter()-start,
         "meaning":"local necessary constraints only; SAT is not a cover"}
    if ans==z3.sat:
        row["model"]=str(solver.model())
    elif ans==z3.unknown:
        row["reason"]=solver.reason_unknown()
    rows.append(row);print(json.dumps(row),flush=True)
Path("work/round40_direct_contacts_exploration.json").write_text(json.dumps(rows,indent=2),encoding="utf-8")
