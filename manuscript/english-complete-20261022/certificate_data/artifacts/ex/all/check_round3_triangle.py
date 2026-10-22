"""Exact checks of the new triangle restriction and its adjacent-gap consequence.

The report supplies a hand proof. The first check represents fit in a unit
square by all pairwise projection widths, over the entire real parameter domain.
The second is only the resulting linear aggregation, not a geometry model.
"""
from pathlib import Path
import itertools
import json
import time
import z3


def triangle_check():
    c, s, mu, d, x, y = z3.Reals('c s mu d x y')
    points = [(0, 0), (d, -mu), (-x, 0), (0, y)]
    sol = z3.SolverFor('QF_NRA')
    sol.set(timeout=60000)
    sol.add(c >= 0, s >= 0, c*c + s*s == 1,
            mu > 1, d >= 0, x >= 0, y >= 0, x+y >= 1)
    for p, q in itertools.combinations(points, 2):
        dx, dy = p[0]-q[0], p[1]-q[1]
        u, v = c*dx+s*dy, -s*dx+c*dy
        sol.add(u >= -1, u <= 1, v >= -1, v <= 1)
    Path(__file__).with_name('round3_triangle_counterexample.smt2').write_text(sol.to_smt2())
    start = time.time()
    result = sol.check()
    assert result == z3.unsat, result
    return {'scope': 'unit square containing (d,-mu),(-x,0),(0,y), mu>1, d,x,y>=0 has x+y<1',
            'result': str(result), 'arithmetic': 'exact nonlinear reals',
            'seconds': time.time()-start}


def adjacent_check():
    mu, B, L3, S3, U3, S4, U4 = z3.Reals('mu B L3 S3 U3 S4 U4')
    sol = z3.SolverFor('QF_LRA')
    sol.add(mu > 1, B < 1, S3 >= 0, U3 >= 0, U4 >= 0,
            L3+S3+U3 <= 2, S4+U4 <= B, L3+S4 >= 2*mu,
            (mu-U3)+(mu-U4) < 1)
    result = sol.check()
    assert result == z3.unsat, result
    return {'scope': 'adjacent exceptional branch contradicts the triangle restriction',
            'result': str(result), 'arithmetic': 'exact linear reals'}


if __name__ == '__main__':
    records = [triangle_check(), adjacent_check()]
    for record in records:
        print('PASS', record, flush=True)
    Path(__file__).with_name('round3_triangle_checks.json').write_text(json.dumps(records, indent=2))
