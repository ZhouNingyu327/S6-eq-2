"""Exact checks for the ongoing k=1 analysis. Not a complete k=1 proof."""
from pathlib import Path
import itertools,json,time
import z3
import sympy as sp

records=[]
mu,d,e,p,q=z3.Reals('mu d e p q')
sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
sol.add(mu>1,d>=-mu,d<=mu,e>=0,p>=0,q>=0,p*p+q*q==1)
points=[(0,0),(d,-mu),(mu,e)]
for a,b in itertools.combinations(points,2):
    dx,dy=a[0]-b[0],a[1]-b[1]
    u,v=p*dx+q*dy,-q*dx+p*dy
    sol.add(u>=-1,u<=1,v>=-1,v<=1)
start=time.time();res=sol.check();assert res==z3.unsat,res
records.append({'scope':'centre tile touching bottom cannot touch upper half of right edge; reflection gives left edge',
                'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start})

mu,B,S1,S2,U1,U2,lC,lF,hC,hF,Hw,Tw,L4=z3.Reals('mu B S1 S2 U1 U2 lC lF hC hF Hw Tw L4')
sol=z3.SolverFor('QF_LRA')
sol.add(mu>1,B<1,lC+hC<=B,lF+hF<=B,lC+lF+S1+S2>=2*mu,
        hC+hF+U1+U2+Hw>=2*mu,S1+U1<=B,S2+U2<=B)
sol.push();sol.add(Hw<4*(mu-B));res=sol.check();assert res==z3.unsat
records.append({'scope':'far weak-corner orbit, both extras touch bottom: W middle-horizontal length >=4(mu-B)',
                'result':str(res),'arithmetic':'exact linear reals'})
sol.pop();sol.add(Tw+Hw<=B,Tw+L4>=2*mu,L4<6*mu-5*B)
res=sol.check();assert res==z3.unsat
records.append({'scope':'same branch: top corner long leg L4 >=6mu-5B',
                'result':str(res),'arithmetic':'exact linear reals'})
crit=(5*sp.sqrt(26)-sp.sqrt(2))/24
assert sp.simplify(24*crit**2+2*sp.sqrt(2)*crit-27)==0
records.append({'scope':'conditional threshold equation','result':'exact symbolic identity passed',
                'side_threshold':str(2*crit),'side_decimal':str((2*crit).evalf(20))})
for record in records:print('PASS',record,flush=True)
Path(__file__).with_name('g5_k1_structure_checks.json').write_text(json.dumps(records,indent=2))
