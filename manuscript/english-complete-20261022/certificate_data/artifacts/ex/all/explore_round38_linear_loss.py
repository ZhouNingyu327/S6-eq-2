"""Probe one proposed explicit inequality, independent of a covering search."""
from pathlib import Path
import json,time,z3
e,u,d,l=z3.Reals('eta u d l')
K=2*e/(1-e*e);q=lambda t:t/(2-t)
cs=[e>0,e*e+2*e<=1,u>e,u<1,d>0,u+d<1,
    l>0,l<=K*u,K*l<=d,2*l<1,
    2*e/(1+e)+d<q(u)+4*l*l/7,
    2*(u-e)<=2*d-d*d+q(l)]
solver=z3.SolverFor('QF_NRA');solver.set(timeout=30000);solver.add(*cs)
t=time.perf_counter();ans=solver.check()
row={'name':'Does the bridge force 2w>2d-d^2+q(l)?','result':str(ans),'seconds':time.perf_counter()-t}
if ans==z3.sat:row['model']=str(solver.model())
if ans==z3.unknown:row['reason']=solver.reason_unknown()
Path(__file__).with_name('round38_linear_loss_exploration.json').write_text(json.dumps(row,indent=2),encoding='utf-8')
print(json.dumps(row),flush=True)
