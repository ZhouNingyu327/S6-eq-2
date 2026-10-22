"""Exact linear consequences of separately proved geometry; not a global cover model."""
from pathlib import Path
import json,z3


def run(sol,scope):
    result=sol.check();assert result==z3.unsat,result
    return {'scope':scope,'result':str(result),'arithmetic':'exact linear reals'}


def right_C_excluded():
    mu,B,S2,U2,g,h=z3.Reals('mu B S2 U2 g h')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,S2+U2<=B,g>=mu-S2,h>=mu-U2,g+h<=B)
    return run(sol,'right critical tip cannot belong to C')


def common(sol):
    mu,B,A,D,H,g,d,CL,CU,FU,L2,L3,L4,S2,S3,S4,U2,U3,U4=z3.Reals(
        'mu B A D H g d CL CU FU L2 L3 L4 S2 S3 S4 U2 U3 U4')
    sol.add(mu>1,B<1,A>=0,D>=0,H>=0,A+D+H<=2,
            CL>=0,CU>=0,FU>=0,g==2*mu-A-S2,g>0,d==2*mu-L2-S3,d>0,
            L3+S4>=2*mu,D+L4>=2*mu,CL+U4+H>=mu)
    for L,S,U in [(L2,S2,U2),(L3,S3,U3),(L4,S4,U4)]:
        sol.add(L>=mu,S>=0,U>=0,L+S+U<=2,S+U<=B)
    return mu,B,A,D,H,g,d,CL,CU,FU,L2,L3,L4,S2,S3,S4,U2,U3,U4


def C_left_excluded_when_F_up():
    sol=z3.SolverFor('QF_LRA')
    mu,B,A,D,H,g,d,CL,CU,FU,L2,L3,L4,S2,S3,S4,U2,U3,U4=common(sol)
    sol.add(CL+g<=B,FU>=mu-U3,FU+d<=B)
    return run(sol,'upper critical tip in F: C cannot dominate the left horizontal coverage')


def C_left_excluded_when_C_up():
    sol=z3.SolverFor('QF_LRA')
    mu,B,A,D,H,g,d,CL,CU,FU,L2,L3,L4,S2,S3,S4,U2,U3,U4=common(sol)
    sol.add(CU>=mu-U3,g+mu+CU+CL<2)
    return run(sol,'upper critical tip in C: its long-chord trace excludes left horizontal dominance')


def aggregate():
    mu,corners,c_useful,f_useful=z3.Reals('mu corners c_useful f_useful')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,corners<=8,c_useful<2,f_useful<2,12*mu<=corners+c_useful+f_useful)
    return run(sol,'both central useful traces below 2 cannot complete the six-line target grid')


if __name__=='__main__':
    records=[right_C_excluded(),C_left_excluded_when_F_up(),C_left_excluded_when_C_up(),aggregate()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round6_near_gap_checks.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
