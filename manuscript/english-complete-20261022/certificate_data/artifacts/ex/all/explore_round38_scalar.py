"""Explicit three-variable necessary-condition probe, not a cover search."""
from pathlib import Path
import json,time
import z3

e,u,d,l,v=z3.Reals('eta u d l v')
K=2*e/(1-e*e)
q=lambda t:t/(2-t)
cs=[e>0,e*e+2*e<=1,u>e,u<1,d>0,u+d<1,
    l>0,l<=K*u,K*l<=d,2*l<1,v>0,v*v==u-e,
    (u-e)**2+2*(u-e)<1,
    2*e/(1+e)+d<q(u)+4*l*l/7]
sol=z3.SolverFor('QF_NRA');sol.set(timeout=30000)
sol.add(*cs,5*v/4<2*d-d*d+q(l))
t=time.perf_counter();ans=sol.check()
row={'name':'RIGHT empty negative C: bridge plus bottom square and strong Phi loss',
     'result':str(ans),'seconds':time.perf_counter()-t,
     'status':'Exploratory scalar relaxation, not a covering model or a proof by itself'}
if ans==z3.sat:row['model']=str(sol.model())
if ans==z3.unknown:row['reason']=sol.reason_unknown()
Path(__file__).with_name('round38_scalar_exploration.json').write_text(json.dumps(row,indent=2),encoding='utf-8')
print(json.dumps(row),flush=True)
