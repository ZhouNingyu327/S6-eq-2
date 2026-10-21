"""Exact universal checks for excluding the remaining near-W, F-bottom case."""
from pathlib import Path
import itertools,json,time
import z3


def reflected_triangle():
    mu,d,r,u,p,q=z3.Reals('mu d r u p q')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(mu>1,d>=0,r>=0,u>=0,p>=0,q>=0,p*p+q*q==1,r+u>=1)
    points=[(0,0),(-d,-mu),(r,0),(0,u)]
    for a,b in itertools.combinations(points,2):
        dx,dy=a[0]-b[0],a[1]-b[1]
        v1,v2=p*dx+q*dy,-q*dx+p*dy
        sol.add(v1>=-1,v1<=1,v2>=-1,v2<=1)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'unit square touching bottom left and containing right/up rays has r+u<1',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def C_cannot_right():
    mu,B,S2,U2,lC,hC=z3.Reals('mu B S2 U2 lC hC')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,S2>=0,U2>=0,S2+U2<=B,
            lC>=mu-S2,hC>=mu-U2,lC+hC<=B)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'near W and F bottom-left: C cannot contain right critical tip',
            'result':str(res),'arithmetic':'exact linear reals'}


def upper_meets():
    sol=z3.SolverFor('QF_LRA')
    mu,B,L2,L3,L4,S2,S3,S4,U2,U3,U4=z3.Reals('mu B L2 L3 L4 S2 S3 S4 U2 U3 U4')
    sol.add(mu>1,B<1)
    for L,S,U in [(L2,S2,U2),(L3,S3,U3),(L4,S4,U4)]:
        sol.add(L>=mu,S>=0,U>=0,L+S+U<=2,S+U<=B)
    sol.add(L2+S3>=2*mu,L3+S4>=2*mu)
    return sol,mu,B,L2,L3,L4,S2,S3,S4,U2,U3,U4


def F_cannot_up():
    sol,mu,B,L2,L3,L4,S2,S3,S4,U2,U3,U4=upper_meets()
    sol.add((mu-U2)+(mu-U3)<1)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'right and up critical rays cannot both fit the F bottom-left triangle restriction',
            'result':str(res),'arithmetic':'exact linear reals'}


def C_cannot_up():
    sol,mu,B,L2,L3,L4,S2,S3,S4,U2,U3,U4=upper_meets()
    D=z3.RealVal('10/7') # rigorously larger than sqrt(2)
    sol.add(L2<=D,2*mu-U3<=D)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'upper meets exclude C containing both bottom midpoint and up critical tip',
            'result':str(res),'arithmetic':'exact linear reals','diameter_upper':'10/7'}


if __name__=='__main__':
    records=[reflected_triangle(),C_cannot_right(),F_cannot_up(),C_cannot_up()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_sameedge_checks.json').write_text(json.dumps(records,indent=2))
