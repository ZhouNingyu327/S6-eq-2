"""Three-variable local support lemma with rational strict slack."""
import json,time
from pathlib import Path
import z3
a,z,S=z3.Reals("a z S")
b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
Q=S+(h-1)*(b+S-2)/(k-h)
base=[a>0,a<1,z>0,15*z<4,z<a,a+2*z<1,S>0,
      S<(1-z)/(1+z),2-S<b,2*a*(2-S)<1+a*a,
      k*(2-S)<b-z3.Q(2,7),Q<z3.Q(5,12)+z]
rows=[]
for label,extra in [
    ("Ka<=1",[2*a<=1-a*a]),
    ("Ka>=1",[2*a>=1-a*a])]:
    solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000);solver.add(*(base+extra))
    start=time.perf_counter();ans=solver.check()
    row={"name":label,"result":str(ans),"seconds":time.perf_counter()-start}
    if ans==z3.sat:row["detail"]=str(solver.model())
    elif ans==z3.unknown:row["detail"]=solver.reason_unknown()
    rows.append(row);print(json.dumps(row),flush=True)
Path("work/round41_rational_corner_exploration.json").write_text(json.dumps(rows,indent=2),encoding="utf-8")
