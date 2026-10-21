"""Exact continuous centre-tile restrictions used in near-W top-left exclusion."""
from pathlib import Path
import json,time,itertools
import z3


def fit(sol,points,p,q):
    sol.add(p>=0,q>=0,p*p+q*q==1)
    for a,b in itertools.combinations(points,2):
        dx,dy=a[0]-b[0],a[1]-b[1]
        u,v=p*dx+q*dy,-q*dx+p*dy
        sol.add(u>=-1,u<=1,v>=-1,v<=1)


def top_left_forbids_right():
    mu,d,y,p,q=z3.Reals('mu d y p q')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(mu>1,d>0,d<=mu,y>=-mu,y<=mu)
    fit(sol,[(0,0),(-d,mu),(mu,y)],p,q)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'centre tile with top-left outer point cannot touch right edge',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def top_left_forbids_left_lower():
    mu,d,e,p,q=z3.Reals('mu d e p q')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(mu>1,d>0,d<=mu,e>=0,e<=mu)
    fit(sol,[(0,0),(-d,mu),(-mu,-e)],p,q)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'centre tile with top-left outer point cannot touch left lower half, including midpoint',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


if __name__=='__main__':
    records=[top_left_forbids_right(),top_left_forbids_left_lower()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_topcontact_checks.json').write_text(json.dumps(records,indent=2))
