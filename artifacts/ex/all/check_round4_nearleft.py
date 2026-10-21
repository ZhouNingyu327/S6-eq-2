"""Exact checks for the near-W left-lower boundary contact exclusion.

The corner meeting assumptions must come from the geometry in the report.
These queries do not substitute sampled points for full square containment.
"""
import itertools,json,time
from pathlib import Path
import z3


def left_lower_triangle():
    mu,d,r,u,p,q=z3.Reals('mu d r u p q')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(mu>1,d>=0,r>=0,u>=0,p>=0,q>=0,p*p+q*q==1,r+u>=1)
    points=[(0,0),(-mu,-d),(r,0),(0,u)]
    for a,b in itertools.combinations(points,2):
        dx,dy=a[0]-b[0],a[1]-b[1]
        v1,v2=p*dx+q*dy,-q*dx+p*dy
        sol.add(v1>=-1,v1<=1,v2>=-1,v2<=1)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'centre tile with left-lower outer point has right+up rays <1',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def left_lower_forbids_top():
    mu,d,x,p,q=z3.Reals('mu d x p q')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(mu>1,d>0,d<=mu,x>=-mu,x<=mu,p>=0,q>=0,p*p+q*q==1)
    points=[(0,0),(-mu,-d),(x,mu)]
    for a,b in itertools.combinations(points,2):
        dx,dy=a[0]-b[0],a[1]-b[1]
        v1,v2=p*dx+q*dy,-q*dx+p*dy
        sol.add(v1>=-1,v1<=1,v2>=-1,v2<=1)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'centre tile with left-lower outer point cannot touch top edge',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


if __name__=='__main__':
    records=[left_lower_triangle(),left_lower_forbids_top()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_nearleft_checks.json').write_text(json.dumps(records,indent=2))
