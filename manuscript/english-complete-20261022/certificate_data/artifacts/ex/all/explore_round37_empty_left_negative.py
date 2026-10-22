"""Small scalar consequence of empty-F LEFT negative-C supporting faces."""
from pathlib import Path
import json
import time
import z3


eta,d,l=z3.Reals("eta d l")
K=2*eta/(1-eta*eta)
sec=(1+eta*eta)/(1-eta*eta)
r=K*d
u=sec-K*l
q=lambda a:a/(2-a)
base=[eta>0,eta*eta+2*eta<=1,d>0,d<eta,l>0,l<1,
      u>0,u+d<1,q(l)+q(r)>(1-d)*(1-d)]
rows=[]
for name,goal in [
    ("bottom/root budget forces C not direct TOP",u+q(eta-d)>=1),
    ("W up bridge and direct right contact impossible",q(eta-d)+q(u)+r*r/(2*(1-r))>=1)]:
    s=z3.SolverFor("QF_NRA");s.set(timeout=45000);s.add(*base,goal)
    start=time.perf_counter();ans=s.check()
    row={"name":name,"result":str(ans),"seconds":time.perf_counter()-start,
         "scope":"local scalar candidate only; not a full layout"}
    if ans==z3.sat:row["model"]=str(s.model())
    if ans==z3.unknown:row["reason"]=s.reason_unknown()
    print(json.dumps(row),flush=True);rows.append(row)
Path(__file__).with_name("round37_empty_left_negative_exploration.json").write_text(
    json.dumps(rows,indent=2),encoding="utf-8")
