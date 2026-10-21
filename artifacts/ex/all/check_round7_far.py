"""Linear implications of the far-W geometry and new continuous unit lemmas."""
from pathlib import Path
import json,z3

def run(sol,scope):
    res=sol.check();assert res==z3.unsat,res
    return {'scope':scope,'result':str(res),'arithmetic':'exact linear reals'}

def C_left_excluded():
    mu,B,g,h,S1,S2,U1=z3.Reals('mu B g h S1 S2 U1')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,g==2*mu-S1-S2,h>=mu-U1,S1+U1<=B,S2<=B,g+h<=B)
    return run(sol,'far W: C cannot contain the left critical tip, so that C ray is redundant in F')

def upper_aggregate():
    mu,corners,cu,fu=z3.Reals('mu corners c_useful f_useful')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,corners<=8,cu<2,fu<2,12*mu<=corners+cu+fu)
    return run(sol,'far W upper outer contact: two useful central traces below 2 exclude covering')

def lower_aggregate():
    mu,corners,cu,fu=z3.Reals('mu corners c_useful f_useful')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,corners<=8,cu<2,fu<mu+1,12*mu<=corners+cu+fu)
    return run(sol,'far W lower outer contact: triangle ray bound excludes covering')

def C_cannot_dominate(axis):
    mu,A,D,H,J,g,CR,CU,S1,S2,S4,U1,U2,U4,L1,L2,L4=z3.Reals(
        'mu A D H J g CR CU S1 S2 S4 U1 U2 U4 L1 L2 L4')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,A>=0,D>=0,H>=0,J>=0,A+D+H+J<=2,g==2*mu-S1-S2,
            CR>=0,CU>=0,g+mu+CU+CR<2,
            L1+S4>=2*mu,L2+A>=2*mu,L4+D>=2*mu)
    for L,S,U in [(L1,S1,U1),(L2,S2,U2),(L4,S4,U4)]:
        sol.add(L>=mu,S>=0,U>=0,L+S+U<=2)
    sol.add(CR+U2+H>=mu if axis=='right' else CU+U4+J>=mu)
    return run(sol,'far W, all nonbottom sides meet: C cannot dominate '+axis+' centre ray')

if __name__=='__main__':
    records=[C_left_excluded(),upper_aggregate(),lower_aggregate(),
             C_cannot_dominate('right'),C_cannot_dominate('up')]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round7_far_checks.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
