"""Exact checks of centre-tile contact restrictions and useful-grid overlap.
No samples or optimizers are used in the exclusion checks.
"""
from pathlib import Path
import itertools,json,time
import z3


def square_fit(sol,points,p,q):
    sol.add(p>=0,q>=0,p*p+q*q==1)
    for a,b in itertools.combinations(points,2):
        dx,dy=a[0]-b[0],a[1]-b[1]
        u,v=p*dx+q*dy,-q*dx+p*dy
        sol.add(u>=-1,u<=1,v>=-1,v<=1)


def bottom_right_forbids_left():
    mu,d,y,p,q=z3.Reals('mu d y p q')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(mu>1,d>0,d<=mu,y>=-mu,y<=mu)
    square_fit(sol,[(0,0),(d,-mu),(-mu,y)],p,q)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'centre tile touching bottom right half cannot touch any left outer-edge point',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def useful_grid_bound():
    mu,B,corners,bottom,horizontal,vertical=z3.Reals('mu B corners bottom horizontal vertical')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,corners<=8,bottom+horizontal<=2*B,vertical<=2*mu,
            12*mu<=corners+bottom+horizontal+vertical)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'all other outer traces redundant: four corners plus two bottom-touching centre tiles cannot cover six-line grid',
            'result':str(res),'arithmetic':'exact linear reals','geometry_input':'redundancy of every nonbottom outer trace must be proved separately'}


if __name__=='__main__':
    records=[bottom_right_forbids_left(),useful_grid_bound()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_overlap_checks.json').write_text(json.dumps(records,indent=2))
