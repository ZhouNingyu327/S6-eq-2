"""Continuous far-G5 closure, retaining zero and floating W middle traces."""
from pathlib import Path
import json,time,z3

def result(sol,scope,nonlinear=False):
    sol.set(timeout=60000);start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':scope,'result':str(res),
            'arithmetic':'exact nonlinear reals' if nonlinear else 'exact linear reals',
            'seconds':time.time()-start}

def H_bound():
    mu,B,L4,D,H=z3.Reals('mu B L4 D H');sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,L4>=mu,D>=0,H>=0,D+L4>=2*mu,
            z3.Or(H==0,D+H<=B),H>L4-mu)
    return result(sol,'W horizontal middle trace H<=L4-mu, including H=0 and duplicate top midpoint')

def J_bound():
    mu,B,A,J=z3.Reals('mu B A J');sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,A>=0,A<mu,J>=0,z3.Or(J==0,A+J<=B),A+J>=mu)
    return result(sol,'W right leg plus vertical middle trace A+J<mu, including J=0')

def rays():
    mu,B,A,D,H,J,r,u,L2,L4,U2,U4=z3.Reals('mu B A D H J r u L2 L4 U2 U4')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,A>=0,A<mu,D>=0,H>=0,J>=0,L2>=mu,L4>=mu,U2>=0,U4>=0,
            A+L2>=2*mu,D+L4>=2*mu,z3.Or(H==0,D+H<=B),z3.Or(J==0,A+J<=B),
            r+U2+H>=mu,u+U4+J>=mu,
            z3.Or(r<2*mu-L4-U2,u<=2*mu-L2-U4))
    return result(sol,'forced F rays r>=2mu-L4-U2 and u>2mu-L2-U4')

def transfer():
    mu,L1,L4,S4,U4=z3.Reals('mu L1 L4 S4 U4');sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,L1+S4>=2*mu,L4+S4+U4<2,L4+U4>=L1-(2*mu-2))
    return result(sol,'left corner meet transfers L4+U4<L1-(2mu-2)')

def final_case(left):
    mu,l,r,u,L1,L2,L4,U1,U2,U4=z3.Reals('mu l r u L1 L2 L4 U1 U2 U4')
    sol=z3.SolverFor('QF_LRA');alpha=z3.RealVal('4/5')
    sol.add(mu>1,l>=0,r>=0,u>=0,L1>=mu,L2>=mu,L4>=mu,U1>=0,U2>=0,U4>=0,
            l>=mu-U1,r>=2*mu-L4-U2,u>2*mu-L2-U4,L4+U4<L1-(2*mu-2))
    if left:
        sol.add(L1+L2+U1+alpha*U2<=z3.RealVal('14/5'),l+u+alpha*r<=2)
    else:
        sol.add(L1+L2+alpha*U1+U2<=z3.RealVal('14/5'),r+u+alpha*l<=2)
    return result(sol,'final weighted contradiction, '+('t1<=t2' if left else 't2<=t1'))

def weighted():
    p,q,l,r,u=z3.Reals('p q l r u');sol=z3.SolverFor('QF_NRA')
    sol.add(p>=0,q>=0,p*p+q*q==1,l>=0,r>=0,u>=0,
            p*(l+r)<=1,q*(l+r)<=1,p*l+q*u<=1,q*r+p*u<=1,
            l+u+z3.RealVal('4/5')*r>2)
    return result(sol,'universal unit-square bound l+u+(4/5)r<=2; reflected version by symmetry',True)

if __name__=='__main__':
    records=[H_bound(),J_bound(),rays(),transfer(),final_case(True),final_case(False),weighted()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round8_far_closure_checks.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
