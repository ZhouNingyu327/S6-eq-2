"""A single proposed scalar root inequality for the remaining LEFT/top contact."""
from pathlib import Path
import json,time
import z3
eta,w=z3.Reals("eta w")
u=eta+w
K=2*eta/(1-eta*eta)
threshold=2*w/3
solver=z3.SolverFor("QF_NRA");solver.set(timeout=30000)
solver.add(eta>0,eta<=z3.Q(5,12),w>0,w<=z3.Q(5,12),u<1,
           K*u>=threshold,
           u/(2-u)>2*eta/(1+eta)+K*threshold)
start=time.perf_counter();ans=solver.check()
result={"name":"LEFT top direct contact forces r<2w/3",
        "result":str(ans),"seconds":time.perf_counter()-start,
        "scope":"One explicit two-variable relaxed necessary-condition lemma"}
if ans==z3.sat:result["model"]=str(solver.model())
if ans==z3.unknown:result["reason"]=solver.reason_unknown()
Path(__file__).with_name("round39_top_root_exploration.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
print(json.dumps(result),flush=True)
