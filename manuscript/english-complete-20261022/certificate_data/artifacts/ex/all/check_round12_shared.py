"""Shared C/F midpoint: complete extra cases, not assumed mutually exclusive."""
from pathlib import Path
import itertools
import json
import z3
from check_round12_far import check
from check_round12_near import base,meets


def left_point_bottom_mid_right_axis():
    c,s,mu,D,x = z3.Reals('c s mu D x')
    sol = z3.SolverFor('QF_NRA')
    sol.add(c >= 0,s >= 0,c*c+s*s == 1,mu > 1,D >= 0,x > 0)
    # Bottom midpoint translated to the origin.  The triangle area exceeds 1/2.
    points = [(0,0),(-mu,D),(x,mu)]
    for p,q in itertools.combinations(points,2):
        dx,dy = p[0]-q[0],p[1]-q[1]
        a,b = c*dx+s*dy,-s*dx+c*dy
        sol.add(a >= -1,a <= 1,b >= -1,b <= 1)
    return check(sol, 'unit containing shared bottom midpoint and left-lower gap point cannot touch positive horizontal axis', True)


def redundant_exterior_grid(horizontal_nonempty):
    mu,B,bC,bF,hC,hF,v = z3.Reals('mu B bC bF hC hF v')
    sol = z3.SolverFor('QF_LRA')
    sol.add(mu > 1,B < 1,bC >= 0,bF >= 0,hC >= 0,hF >= 0,v >= 0,
            bC+hC <= B,v < z3.RealVal('3/2'),bF < z3.RealVal('3/2'))
    if horizontal_nonempty:
        sol.add(bF+hF <= B)
        name = 'shared midpoint and redundant nonbottom exterior, F horizontal nonempty: total grid contribution deficient'
    else:
        sol.add(hF == 0)
        name = 'shared midpoint and redundant nonbottom exterior, F horizontal empty: B+2sqrt2<4 grid bound'
    sol.add(12*mu <= 8+bC+bF+hC+hF+v)
    return check(sol, name)


def near_left_gap():
    sol,v = base()
    meets(sol,v,['right','top'])
    # F contains the bottom midpoint and avoids the origin: positive vertical
    # points are impossible by convexity.  The triangle check excludes its
    # positive horizontal trace once it owns the left-lower gap.
    sol.add(v['CR'] >= v['mu']-v['U2'],v['CU'] >= v['mu']-v['U3'])
    return check(sol, 'shared midpoint near left gap: C forced to cover right/up middle endpoints, violating corner chain')


if __name__ == '__main__':
    rows = [left_point_bottom_mid_right_axis(),redundant_exterior_grid(False),
            redundant_exterior_grid(True),near_left_gap()]
    Path(__file__).with_name('round12_shared_checks.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
