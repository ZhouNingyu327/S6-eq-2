"""Exact algebra behind the near-W, no useful F outer trace subcase."""
from pathlib import Path
import json,time
import z3
import sympy as sp


def C_horizontal_redundant():
    sol=z3.SolverFor('QF_LRA')
    mu,B,A,D,H,CL,CR,L2,L3,L4,S2,S3,S4,U2,U3,U4=z3.Reals(
        'mu B A D H CL CR L2 L3 L4 S2 S3 S4 U2 U3 U4')
    sol.add(mu>1,B<1,A>=0,D>=0,H>=0,A+D+H<=2,CL>=0,CR>=0,
            CL+CR+2*mu-A-S2<=B)
    for L,S,U in [(L2,S2,U2),(L3,S3,U3),(L4,S4,U4)]:
        sol.add(L>=mu,S>=0,U>=0,L+S+U<=2,S+U<=B)
    sol.add(L2+S3>=2*mu,L3+S4>=2*mu,D+L4>=2*mu,
            CL+U4+H>=mu)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'three nonbottom corner meets: C cannot dominate centre-left ray coverage',
            'result':str(res),'arithmetic':'exact linear reals'}


def C_up_excluded_by_right_meet():
    sol=z3.SolverFor('QF_LRA')
    mu,B,L2,S3,U3=z3.Reals('mu B L2 S3 U3');d=z3.RealVal('10/7')
    sol.add(mu>1,B<1,L2<=d,L2+S3>=2*mu,S3+U3<=B,2*mu-U3<=d)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'right corner meet alone excludes C containing up critical tip',
            'result':str(res),'arithmetic':'exact linear reals','diameter_upper':'10/7'}


def conditional_threshold():
    mu=sp.symbols('mu',positive=True)
    k=8+3/sp.sqrt(2)
    root=(10*k-sp.sqrt(k*k-99))/99
    assert sp.simplify((k-10*root)**2-root**2+1)==0
    assert 1<float(root)<float(3/(2*sp.sqrt(2)))
    assert float(k-10*root)>0
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    m,b,d=z3.Reals('mu B sqrt2')
    sol.add(m>1,d>0,d*d==2,m<=d,11*m<8+b+3/d,
            z3.Or(z3.And(2*d*m<=3,b<=m,b>=0,(m-b)*(m-b)==m*m-1),
                  z3.And(2*d*m>=3,b==2*(d-m))))
    # Safe rational value just above the derived root, not the final bound.
    sol.add(m>=z3.RealVal('1.004'))
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'near W, all nonbottom outer traces redundant: conditional length threshold',
            'result':str(res),'arithmetic':'exact nonlinear reals plus symbolic root identity',
            'seconds':time.time()-start,'mu_bound_exact':str(root),'a_bound_decimal':str(sp.N(2*root,35)),
            'not_global':True}


if __name__=='__main__':
    records=[C_horizontal_redundant(),C_up_excluded_by_right_meet(),conditional_threshold()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_noouter_checks.json').write_text(json.dumps(records,indent=2))
