"""Exact checks of necessary-length consequences proved in round 13."""
from pathlib import Path
import json,time
import z3


def check(sol,scope,nonlinear=False):
    sol.set(timeout=60000);start=time.time();a=sol.check()
    assert a==z3.unsat,(scope,a)
    row={'scope':scope,'result':str(a),'arithmetic':'exact nonlinear reals' if nonlinear else 'exact linear reals','seconds':time.time()-start}
    print('PASS',row,flush=True);return row


def parabola():
    c,s,l,r,u=z3.Reals('c s l r u');p=z3.SolverFor('QF_NRA')
    p.add(c>=0,s>=0,c*c+s*s==1,l>=0,r>=0,u>=0,c*(l+r)<=1,s*(l+r)<=1,c*l+s*u<=1,s*r+c*u<=1,l+r+u*u>2)
    return check(p,'unit-square three-ray parabola, all rotations and reflections',True)


def both_bottoms():
    mu,B=z3.Reals('mu B');p=z3.SolverFor('QF_LRA')
    p.add(mu>1,B<1,12*mu<=8+2*mu+2*B)
    return check(p,'redundant other outer traces: C/F both bottom and F horizontal nonempty are impossible')


def near_three_meets():
    mu,B,L2,S2,U2,L3,S3,U3,L4,S4,U4,A,D,H,J,h,f,b,q,t=z3.Reals('mu B L2 S2 U2 L3 S3 U3 L4 S4 U4 A D H J h f b q t')
    p=z3.SolverFor('QF_LRA');p.add(mu>1,B<1,L2+S2+U2<2,L3+S3+U3<2,L4+S4+U4<2)
    p.add(L2+S3>=2*mu,L3+S4>=2*mu,L4+D>=2*mu,A+D+H+J<=2,J>=0,
          b>=2*mu-A-S2,b+f<=B,h+f+U2+U4+H>=2*mu,U2<t,
          L3+S2+t+q<=2,h+1-q<2)
    return check(p,'near representative, all three non-bottom edges meet, F horizontal nonempty')


def far_J_zero():
    mu,B,L1,S1,U1,L2,S2,U2,L4,S4,U4,A,D,H,h,f,b,q,t=z3.Reals('mu B L1 S1 U1 L2 S2 U2 L4 S4 U4 A D H h f b q t')
    p=z3.SolverFor('QF_LRA');p.add(mu>1,B<1,L2+S2+U2<2,L1+S4>=2*mu,L2+A>=2*mu,L4+D>=2*mu,A+D+H<=2,
          b>=2*mu-S1-S2,b+f<=B,h+f+U1+U2+H>=2*mu,U1<t,
          L4+S1+t+q<=2,h+1-q<2)
    return check(p,'far representative, three non-bottom edges meet, F horizontal nonempty, W upper vertical length J=0')


def opposite_contacts():
    mu,B=z3.Reals('mu B');p=z3.SolverFor('QF_LRA')
    p.add(mu>1,B<1,12*mu<=8+2*B+2*mu)
    return check(p,'only top non-bottom gap, C top and F bottom, both horizontal traces nonempty')


def far_two_gaps():
    mu,B,L1,S1,U1,L2,S2,U2,L4,S4,U4,A,D,H,J,l,r,u,d,b,f=z3.Reals('mu B L1 S1 U1 L2 S2 U2 L4 S4 U4 A D H J l r u d b f')
    p=z3.SolverFor('QF_LRA');p.add(mu>1,B<1,L1+S1+U1<2,L2+S2+U2<2,L4+S4+U4<2,A+D+H+J<=2,L1+S4>=2*mu,d>0,
          l+r+f+U1+U2+H>=2*mu,u+U4+J>=mu,b>=2*mu-S1-S2,
          l+r+2*mu-L4-D<=B,u+d+2*mu-L2-A<=B,b+f<=B)
    return check(p,'far representative, top and right gaps both assigned to C, F horizontal nonempty')


def near_small_H():
    l,r,u,t,k,S,w,phi=z3.Reals('l r u t k S w phi');p=z3.SolverFor('QF_NRA')
    p.add(l>=0,r>=0,u>=0,t>0,t<1,k>0,k<z3.RealVal('4/15'),w*(1-2*k*k)==k*k,
          l>1-S-w,r>1-t,u>1-k,phi==1-S-t-2*k+k*k-w,phi>0,l+r+u*u<=2)
    return check(p,'near representative, right/top meet and F horizontal empty: H<=S2 contradicts round-5 Phi budget',True)


def near_bottom_long():
    mu,B,A,H,S,g=z3.Reals('mu B A H S g');p=z3.SolverFor('QF_LRA')
    p.add(mu>1,B<1,H>S,S>=0,A+H<=B,g==2*mu-A-S,g<=1)
    return check(p,'near surviving empty-horizontal branch: A+S2<B<1 and entire F bottom gap g>1')


if __name__=='__main__':
    rows=[parabola(),both_bottoms(),near_three_meets(),far_J_zero(),opposite_contacts(),far_two_gaps(),near_small_H(),near_bottom_long()]
    Path(__file__).with_name('round13_closure_checks.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
