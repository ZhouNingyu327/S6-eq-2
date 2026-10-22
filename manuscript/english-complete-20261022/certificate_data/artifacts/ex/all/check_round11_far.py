"""Exact necessary-condition checks for G2 with C at bottom and far weak corner."""
from pathlib import Path
import json,time
import z3


def check(sol,scope,nonlinear=False):
    sol.set(timeout=60000)
    start=time.time();answer=sol.check()
    if answer!=z3.unsat:
        print(scope,answer,sol.model() if answer==z3.sat else sol.reason_unknown(),flush=True)
        raise AssertionError(answer)
    row={'scope':scope,'result':str(answer),
         'arithmetic':'exact nonlinear reals' if nonlinear else 'exact linear reals',
         'seconds':time.time()-start}
    print('PASS',row,flush=True)
    return row


def axis_propagation():
    c,s,mu,l,y,loU,loV=z3.Reals('c s mu l y loU loV')
    sol=z3.SolverFor('QF_NRA')
    sol.add(c>=0,s>=0,c*c+s*s==1,mu>1,l>0)
    for u,v in [(-c*l,s*l),(c*mu+s*y,-s*mu+c*y)]:
        sol.add(loU<=u,u<=loU+1,loV<=v,v<=loV+1)
    sol.add(z3.Or(loU>0,loU+1<0,loV>0,loV+1<0))
    return check(sol,'axis propagation: unit containing (-l,0) and (mu,y), mu>1,l>0, must contain origin',True)


def far_base():
    mu,B=z3.Reals('mu B')
    L1,S1,U1,L2,S2,U2,L4,S4,U4,A,D,H,J=z3.Reals('L1 S1 U1 L2 S2 U2 L4 S4 U4 A D H J')
    CL,CR,CU=z3.Reals('CL CR CU')
    sol=z3.SolverFor('QF_LRA');sol.add(mu>1,B<1)
    for L,S,U in [(L1,S1,U1),(L2,S2,U2),(L4,S4,U4)]:
        sol.add(L>=mu,L<z3.RealVal('3/2'),S>=0,U>=0,L+S+U<2,S+U<=B)
    sol.add(A>=0,D>=0,H>=0,J>=0,A+D+H+J<=2,CL>=0,CR>=0,CU>=0)
    return sol,locals()


def same_bottom_midline():
    mu,B,bC,bF,hC,hF,other,vertical=z3.Reals('mu B bC bF hC hF other vertical')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,bC+hC<=B,bF+hF<=B,other<=8,vertical<=2*mu,
            12*mu<=other+vertical+bC+bF+hC+hF)
    return check(sol,'F bottom and horizontal middle both nonempty: effective grid budget <12mu')


def bottom_right_no_midline():
    mu,B,bC,hC,S1,U1=z3.Reals('mu B bC hC S1 U1')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,bC>=mu-S1,hC>=mu-U1,S1+U1<=B,bC+hC<=B)
    return check(sol,'F bottom right, horizontal middle empty: C left half-gap and left tip violate parallel sections')


def bottom_left_no_midline():
    sol,v=far_base()
    mu,L2,S2,U2,L4,U4,A,D,H,J,CR,CU=[v[n] for n in ['mu','L2','S2','U2','L4','U4','A','D','H','J','CR','CU']]
    sol.add(L2+A>=2*mu,L4+D>=2*mu,
            (mu-S2)+mu+CU+CR<2,
            CR+U2+H>=mu,CU+U4+J>=mu)
    return check(sol,'F bottom left, horizontal middle empty: complete right/up middle coverage contradicts two meets')


def left_tip():
    sol,v=far_base()
    mu,B,S1,U1,S2,CL=[v[n] for n in ['mu','B','S1','U1','S2','CL']]
    g=2*mu-S1-S2
    sol.add(g+CL<=B,CL>=mu-U1)
    return check(sol,'F avoids bottom: full C bottom gap excludes C from left critical tip')


def weak_top_less_than_S1():
    sol,v=far_base()
    mu,B,S1,S2,U2,CR,D,H=[v[n] for n in ['mu','B','S1','S2','U2','CR','D','H']]
    g=2*mu-S1-S2
    sol.add(g+CR<=B,CR+U2+H>=mu)
    # Even before the conditional parallel bound, H cannot vanish.
    sol.add(H<=0)
    return check(sol,'C-only right middle coverage forces weak-corner H>0')


def weak_top_bound():
    sol,v=far_base()
    mu,B,S1,S2,U2,CR,D,H=[v[n] for n in ['mu','B','S1','S2','U2','CR','D','H']]
    g=2*mu-S1-S2
    sol.add(g+CR<=B,CR+U2+H>=mu,D+H<=B,D>=S1)
    return check(sol,'H>0 permits weak top/H parallel bound and implies D<S1')


def left_meet_case():
    sol,v=far_base()
    mu,L1,S1,U1,L4,S4,U4,D=[v[n] for n in ['mu','L1','S1','U1','L4','S4','U4','D']]
    sol.add(D<S1,L1+S4>=2*mu,L4+D>=2*mu)
    return check(sol,'left meet plus D<S1 forbids top meet, so F must own top far endpoint')


def top_far_diameter():
    mu,D,S1,U1=z3.Reals('mu D S1 U1')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,D<S1,S1+U1<1,2*mu-D-U1<=1)
    return check(sol,'F left tip and top far endpoint have horizontal span >1, and vertical span mu>1')


def top_meet_forces_upper_middle():
    sol,v=far_base()
    mu,L2,S2,U2,L4,S4,U4,S1,A,D,H,J,CR,CU=[v[n] for n in [
        'mu','L2','S2','U2','L4','S4','U4','S1','A','D','H','J','CR','CU']]
    g=2*mu-S1-S2
    sol.add(L2+A>=2*mu,L4+D>=2*mu,g+mu+CU+CR<2,
            CR+U2+H>=mu,CU+U4+J>=mu)
    return check(sol,'remaining left-gap branch: C and corners cannot cover all upper middle, so F touches positive vertical axis')


def right_gap_base():
    t,u,L,A,D,S=z3.Reals('t u L A D S')
    sol=z3.SolverFor('QF_NRA')
    sol.add(t>0,t<1,u>0,u<1,L>=1,A>=0,D>=z3.RealVal('7/12'),S>=0,
            L*(1-t*t)<=1+t*t,2*t*L<=1+t*t,
            S*(1-t*t)==1+t*t-2*t*L,
            (1-u*u)*D+2*u*A==1+u*u,
            A*(1-u*u)<=1+u*u,2*u*D<=1+u*u,
            L+A>=2,2*u*(1-A)<=(1-u*u)*t,
            2*S+2*u-S*u-2>=0)
    return sol,t,u,L,A,D,S


def forbidden_band():
    sol,t,u,L,A,D,S=right_gap_base()
    sol.add(u>=z3.RealVal('1/3'),u<=z3.RealVal('7/8'))
    return check(sol,'right-gap endpoint geometry excludes all weak-corner half-angles in [1/3,7/8]',True)


def high_short_leg():
    sol,t,u,L,A,D,S=right_gap_base()
    sol.add(u>=z3.RealVal('7/8'),S>=z3.RealVal('1/2'))
    return check(sol,'remaining high-angle branch has S2<1/2',True)


def central_witness_outside():
    u,v,mu=z3.Reals('u v mu')
    sol=z3.SolverFor('QF_NRA')
    sol.add(mu>1,u>0,u<z3.RealVal('1/3'),v>=0,v*(2-u)<=u,
            (1-v*v)*(mu+2*u/3)-2*v/3<=1+v*v)
    return check(sol,'small weak angle: C cannot contain (1/3,2u/3) after right-gap endpoint calibration',True)


def witness_forces_center():
    c,s,l,u,loU,loV=z3.Reals('c s l u loU loV')
    sol=z3.SolverFor('QF_NRA')
    sol.add(c>=0,s>=0,c*c+s*s==1,l>z3.RealVal('4/5'),u>0,u<z3.RealVal('1/3'))
    for a,b in [(-c*l,s*l),(c/3+2*s*u/3,-s/3+2*c*u/3)]:
        sol.add(loU<=a,a<=loU+1,loV<=b,b<=loV+1)
    sol.add(z3.Or(loU>0,loU+1<0,loV>0,loV+1<0))
    return check(sol,'left endpoint l>4/5 plus interior witness (1/3,2u/3) force center',True)


if __name__=='__main__':
    records=[axis_propagation(),same_bottom_midline(),bottom_right_no_midline(),
             bottom_left_no_midline(),left_tip(),weak_top_less_than_S1(),weak_top_bound(),
             left_meet_case(),top_far_diameter(),top_meet_forces_upper_middle(),
             forbidden_band(),high_short_leg(),central_witness_outside(),witness_forces_center()]
    Path(__file__).with_name('round11_far_checks.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
