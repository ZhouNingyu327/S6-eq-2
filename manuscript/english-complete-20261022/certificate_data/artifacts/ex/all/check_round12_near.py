"""Exact linear checks for the G2 C-bottom near-free-corner proof.

This is an algebraic audit of the geometric reductions in the report,
not a finite-point or full-square coverage solver.
"""
from pathlib import Path
import json
import z3
from check_round12_far import check


def base():
    mu,B,L2,S2,U2,L3,S3,U3,L4,S4,U4,A,D,H,J,a,b,CL,CR,CU,f = z3.Reals(
        'mu B L2 S2 U2 L3 S3 U3 L4 S4 U4 A D H J a b CL CR CU f')
    sol = z3.SolverFor('QF_LRA')
    sol.add(mu > 1, B < 1)
    for L,S,U in [(L2,S2,U2),(L3,S3,U3),(L4,S4,U4)]:
        sol.add(L >= mu, S >= 0, U >= 0, L+S+U < 2, S+U <= B)
    for value in [A,D,H,J,a,b,CL,CR,CU,f]:
        sol.add(value >= 0)
    sol.add(A+D+H+J <= 2, a+b+CL+CR <= B,
            a+b+mu+CL+CU < 2, a+b+mu+CR+CU < 2)
    eta = 2*mu-2
    g = 2*mu-A-S2
    gR = 2*mu-L2-S3
    return sol, locals()


def meets(sol, v, edges):
    for edge in edges:
        if edge == 'right':
            sol.add(v['L2']+v['S3'] >= 2*v['mu'])
        elif edge == 'top':
            sol.add(v['L3']+v['S4'] >= 2*v['mu'])
        elif edge == 'left':
            sol.add(v['L4']+v['D'] >= 2*v['mu'])


def left_gap_bottom_gap():
    sol,v = base()
    mu,S2,U2,A,b,CR = [v[n] for n in ['mu','S2','U2','A','b','CR']]
    sol.add(A+S2 < 2*mu, b >= mu-S2,
            4*mu <= b+mu+CR+mu+S2+U2)
    return check(sol, 'near left gap and bottom gap: weak SE traces redundant, C/V2 boundary budget deficient')


def left_gap_bottom_meet_chain():
    sol,v = base()
    mu,A,D,J,S2,U3 = [v[n] for n in ['mu','A','D','J','S2','U3']]
    meets(sol,v,['right','top'])
    sol.add(A+S2 >= 2*mu, A+D+J < 2, D+U3 >= 1)
    return check(sol, 'near left gap and bottom meet force D+U3<1, so F cannot contain the upper critical endpoint')


def left_gap_bottom_meet_center():
    sol,v = base()
    mu,A,D,J,S2,CR,CU,U2,U3 = [v[n] for n in ['mu','A','D','J','S2','CR','CU','U2','U3']]
    meets(sol,v,['right','top'])
    sol.add(A+S2 >= 2*mu, A+D+J < 2,
            CR >= mu-U2, CU >= mu-U3)
    return check(sol, 'near left gap and bottom meet: C forced to contain right/up endpoints, violating long-chord budget')


def top_gap_no_horizontal_forces_anchor():
    sol,v = base()
    sol.add(v['a']+v['b'] >= v['g'], v['CR'] >= v['mu']-v['U2'], v['A'] <= v['mu'])
    return check(sol, 'near top gap, F horizontal middle empty: A>mu, hence weak corner acquires bottom anchor')


def top_gap_no_horizontal():
    sol,v = base()
    meets(sol,v,['left'])
    sol.add(v['a']+v['b'] >= v['g'], v['A']+v['D']+v['J'] < 2,
            v['H'] == 0, v['CL'] >= v['mu']-v['U4'], v['CR'] >= v['mu']-v['U2'])
    return check(sol, 'near top gap, F horizontal middle empty: anchored weak corner and left meet contradict C parallel budget')


def right_gap_perimeter(has_vertical):
    sol,v = base()
    mu,S4,U4,L3,U3,H,CL,CU,f = [v[n] for n in ['mu','S4','U4','L3','U3','H','CL','CU','f']]
    meets(sol,v,['left'])
    sol.add(v['a']+v['b'] >= v['g'], v['gR'] > 0,
            4*mu <= S4+U4+L3+U3+H+CL+CU+f)
    if has_vertical:
        sol.add(f > 0, v['gR']+f <= v['B'])
        name = 'near right gap, F upper middle positive: right-gap/vertical parallel budget closes NW boundary'
    else:
        sol.add(f == 0)
        name = 'near right gap, F upper middle zero: NW boundary already deficient'
    return check(sol, name)


def all_three_meets_bottom_gap():
    sol,v = base()
    meets(sol,v,['right','top','left'])
    sol.add(v['A']+v['S2'] >= 2*v['mu'])
    return check(sol, 'near all right/top/left meets: strict corner chain forces a positive bottom gap')


def all_three_bottom_F(left):
    sol,v = base()
    meets(sol,v,['right','top','left'])
    mu = v['mu']
    if left:
        sol.add(v['b'] >= mu-v['S2'], v['CR'] >= mu-v['U2'])
        name = 'near all three meets, F bottom left and no horizontal middle: C bottom/right parallel contradiction'
    else:
        sol.add(v['a'] >= mu-v['A'], v['CL']+v['CR']+v['H']+v['U2']+v['U4'] >= 2*mu)
        name = 'near all three meets, F bottom right and no horizontal middle: full C horizontal trace contradicts chain'
    return check(sol, name)


def all_three_no_F_bottom(right_owned_by_C):
    sol,v = base()
    meets(sol,v,['right','top','left'])
    sol.add(v['a']+v['b'] >= v['g'])
    if right_owned_by_C:
        sol.add(v['CR']+v['U2'] >= v['mu'])
        name = 'near all three meets, F avoids bottom and positive horizontal axis: C long-chord/right budget deficient'
    else:
        sol.add(v['CL']+v['H']+v['U4'] >= v['mu'])
        name = 'near all three meets, F contains a positive horizontal point: C/W left-middle budget deficient'
    return check(sol, name)


if __name__ == '__main__':
    rows = [left_gap_bottom_gap(),left_gap_bottom_meet_chain(),left_gap_bottom_meet_center(),
            top_gap_no_horizontal_forces_anchor(),top_gap_no_horizontal(),
            right_gap_perimeter(False),right_gap_perimeter(True),all_three_meets_bottom_gap(),
            all_three_bottom_F(True),all_three_bottom_F(False),
            all_three_no_F_bottom(True),all_three_no_F_bottom(False)]
    Path(__file__).with_name('round12_near_checks.json').write_text(json.dumps(rows, indent=2), encoding='utf-8')
