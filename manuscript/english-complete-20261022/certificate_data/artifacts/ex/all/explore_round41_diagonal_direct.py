"""A local single-corner lemma for direct QU/Q2 with diagonal C."""
from pathlib import Path
import json,time,z3
a,z,S=z3.Reals("a z S")
b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
Q=S+(h-1)*(b+S-2)/(k-h);q=lambda v:v/(2-v)
base=[a>0,a<1,z>0,15*z<4,z<a,a+2*z<1,S>0,
 S<(1-z)/(1+z),2-S<b,2*a*(2-S)<1+a*a,
 Q<z3.Q(5,12)+z,b-k*(2-S)+q(z3.Q(5,12)+z)>=z3.Q(7,12)]
rows=[]
for name,extra in [("Ka<=1",[2*a<=1-a*a]),("Ka>=1",[2*a>=1-a*a])]:
 sol=z3.SolverFor("QF_NRA");sol.set(timeout=20000);sol.add(*(base+extra))
 start=time.perf_counter();ans=sol.check()
 row={"name":name,"result":str(ans),"seconds":time.perf_counter()-start}
 if ans==z3.sat:row["detail"]=str(sol.model())
 elif ans==z3.unknown:row["detail"]=sol.reason_unknown()
 rows.append(row);print(json.dumps(row),flush=True)
Path("work/round41_diagonal_direct_exploration.json").write_text(json.dumps(rows,indent=2),encoding="utf-8")
