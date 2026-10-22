"""Exact algebraic prerequisites for the near-W three-meet exclusion."""
from pathlib import Path
import json
import z3


def A_below_one():
    mu,A,D,H,L2,L3,L4,S3,S4,U2,U3,U4,l,r,u=z3.Reals(
        'mu A D H L2 L3 L4 S3 S4 U2 U3 U4 l r u')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,A>=1,D>=0,H>=0,A+D+H<=2,
            L2+S3>=2*mu,L3+S4>=2*mu,D+L4>=2*mu,
            L3+S3+U3<=2,L4+S4+U4<=2,
            L2+z3.RealVal('3/4')*U2<=z3.RealVal('7/4'),
            l>=mu-U4-H,r>=mu-U2,u>=mu-U3,
            l+u+z3.RealVal('3/4')*r<=2)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'near W, three meets: free corner bottom leg A<1',
            'result':str(res),'arithmetic':'exact linear reals'}


def H_below_S2():
    mu,B,A,H,S=z3.Reals('mu B A H S')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,A<1,H>=0,A+S>=2*mu-B,
            z3.Or(H==0,A+H<=B),H>=S)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'free-corner horizontal middle chord H_W<S2',
            'result':str(res),'arithmetic':'exact linear reals'}


if __name__=='__main__':
    records=[A_below_one(),H_below_S2()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round5_noouter_linear_checks.json').write_text(json.dumps(records,indent=2))
