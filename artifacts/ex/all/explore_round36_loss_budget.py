"""Two-variable continuous loss inequality candidate, no square layout search."""
from pathlib import Path
import json
import time
import z3


eta,u=z3.Reals("eta u")
q=u/(2-u)
K=2*eta/(1-eta*eta)
lhs=u-eta+4*eta/(1+3*eta)-q
rhs=z3.Q(16,25)*(q+K*u)**2
s=z3.SolverFor("QF_NRA");s.set(timeout=60000)
s.add(eta>0,eta*eta+2*eta<=1,u>0,2*u<1,lhs<=rhs)
start=time.perf_counter();ans=s.check()
row={"name":"global two-variable sum-of-long-leg-defects budget","result":str(ans),
     "seconds":time.perf_counter()-start,
     "scope":"local scalar relaxation only, not a covering proof"}
if ans==z3.sat:row["model"]=str(s.model())
if ans==z3.unknown:row["reason"]=s.reason_unknown()
Path(__file__).with_name("round36_loss_budget_exploration.json").write_text(
    json.dumps(row,indent=2),encoding="utf-8")
print(json.dumps(row),flush=True)
