"""A local corner/seam projection lemma; not a layout search."""
from pathlib import Path
import json,time
import z3

a,z,L,S,w=z3.Reals("a z L S w")
ba=(1+a*a)/(1-a*a);ka=2*a/(1-a*a)
kz=2*z/(1-z*z);gz=(1-z)/(1+z)
X=(ba+S-2)/(ka-kz)
Q=S+(kz-1)*X
short=ba-ka*L
cs=[a>0,a<1,z>0,15*z<4,z<a,a+2*z<1,
    L>1,L*(1-a*a)<=1+a*a,2*a*L<=1+a*a,
    S>0,S<gz,L+S>2,
    w>0,w*w==2,Q<w-1+z,
    short>=1-w/2]
solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000);solver.add(*cs)
start=time.perf_counter();answer=solver.check()
row={"name":"one adjacent seam plus diagonal-C upper projection",
     "result":str(answer),"seconds":time.perf_counter()-start,
     "scope":"specified local necessary inequalities, not an entire covering"}
if answer==z3.sat:row["detail"]=str(solver.model())
elif answer==z3.unknown:row["detail"]=solver.reason_unknown()
Path("work/round41_diagonal_exploration.json").write_text(json.dumps(row,indent=2),encoding="utf-8")
print(json.dumps(row),flush=True)
