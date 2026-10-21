"""Exact counterexample checks for the remaining G2 C-bottom far-corner orbit.

Geometric coverage and support restrictions are proved in the accompanying note.
The two perimeter checks use only linear consequences of those restrictions.
"""
from pathlib import Path
import json
import time
import z3


def check(sol, scope, nonlinear=False):
    sol.set(timeout=60000)
    start = time.time()
    answer = sol.check()
    if answer != z3.unsat:
        print(scope, answer, sol.model() if answer == z3.sat else sol.reason_unknown(), flush=True)
        raise AssertionError(answer)
    row = {'scope': scope, 'result': str(answer),
           'arithmetic': 'exact nonlinear reals' if nonlinear else 'exact linear reals',
           'seconds': time.time()-start}
    print('PASS', row, flush=True)
    return row


def left_gap_forbids_top_right():
    # Full arbitrary translations; quarter-turn/reflection symmetry puts an
    # arbitrary unit-square orientation in c,s >= 0 without restricting poses.
    c,s,mu,d,x,loU,loV = z3.Reals('c s mu d x loU loV')
    sol = z3.SolverFor('QF_NRA')
    sol.add(c >= 0, s >= 0, c*c+s*s == 1, mu > 1, d >= 0, x > 0)
    # Relative to the top midpoint: P=(-mu,-d), Q=(x,0).
    for a,b in [(-c*mu-s*d, s*mu-c*d), (c*x, -s*x)]:
        sol.add(loU <= a, a <= loU+1, loV <= b, b <= loV+1)
    # The midpoint is excluded from at least one closed projection interval.
    sol.add(z3.Or(loU > 0, loU+1 < 0, loV > 0, loV+1 < 0))
    return check(sol, 'left outer point and top-right point force the top midpoint, mu>1', True)


def perimeter_base():
    mu,B,L1,S1,U1,L2,S2,U2,L4,S4,U4,w,r,v,f = z3.Reals(
        'mu B L1 S1 U1 L2 S2 U2 L4 S4 U4 w r v f')
    sol = z3.SolverFor('QF_LRA')
    sol.add(mu > 1, B < 1)
    for L,S,U in [(L1,S1,U1), (L2,S2,U2), (L4,S4,U4)]:
        sol.add(L >= mu, S >= 0, U >= 0, L+S+U < 2, S+U <= B)
    sol.add(w >= 0, w <= 2, r >= 0, v >= 0, f >= 0)
    g = 2*mu-S1-S2
    leftgap = 2*mu-L1-S4
    sol.add(g > 0, leftgap > 0, g+mu+r+v < 2)
    # R=[0,mu]^2, no positive horizontal or top/right outer traces of F.
    sol.add(4*mu <= L2-mu+U2+L4-mu+U4+w+r+v+f)
    return sol, locals()


def missing_vertical_trace():
    sol, values = perimeter_base()
    sol.add(values['f'] == 0)
    return check(sol, 'left-gap branch, F upper middle trace has zero length: NE boundary budget is deficient')


def nonempty_vertical_trace():
    sol, values = perimeter_base()
    sol.add(values['f'] > 0, values['leftgap']+values['f'] <= values['B'])
    return check(sol, 'left-gap branch, F upper middle trace positive: left-gap/vertical parallel budget closes NE boundary')


if __name__ == '__main__':
    rows = [left_gap_forbids_top_right(), missing_vertical_trace(), nonempty_vertical_trace()]
    Path(__file__).with_name('round12_far_checks.json').write_text(json.dumps(rows, indent=2), encoding='utf-8')
