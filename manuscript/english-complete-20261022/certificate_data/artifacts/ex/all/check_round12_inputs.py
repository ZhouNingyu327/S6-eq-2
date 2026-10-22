"""Fresh continuous input-lemma checks and midpoint-assignment enumeration."""
from pathlib import Path
import itertools
import json
import sympy as sp
import z3
from check_round12_far import check


def axis_propagation():
    c,s,mu,l,y,loU,loV = z3.Reals('c s mu l y loU loV')
    sol = z3.SolverFor('QF_NRA')
    sol.add(c >= 0, s >= 0, c*c+s*s == 1, mu > 1, l > 0)
    for a,b in [(-c*l,s*l),(c*mu+s*y,-s*mu+c*y)]:
        sol.add(loU <= a,a <= loU+1,loV <= b,b <= loV+1)
    sol.add(z3.Or(loU > 0,loU+1 < 0,loV > 0,loV+1 < 0))
    return check(sol, 'full arbitrary unit: (-l,0) and (mu,y), l>0,mu>1, force origin', True)


def parallel_trace():
    c,s,mu,l,r,d = z3.Reals('c s mu l r d')
    sol = z3.SolverFor('QF_NRA')
    sol.add(c >= 0,s >= 0,c*c+s*s == 1,mu > 1,l >= 0,r >= 0,l+r >= 1)
    points = [(0,0),(0,l),(mu,d),(mu,d+r)]
    for p,q in itertools.combinations(points,2):
        dx,dy = p[0]-q[0],p[1]-q[1]
        a,b = c*dx+s*dy,-s*dx+c*dy
        sol.add(a >= -1,a <= 1,b >= -1,b <= 1)
    return check(sol, 'two nonempty parallel sections at distance mu>1 have total length strictly below 1', True)


def long_chord():
    c,s,mu,beta,H = z3.Reals('c s mu beta H')
    sol = z3.SolverFor('QF_NRA')
    sol.add(c > 0,s > 0,c*c+s*s == 1,mu > 1,mu*c <= 1,mu*s <= 1,
            beta >= mu*s,beta <= 1,H >= mu,H*c <= 1,H*s <= beta)
    sol.add(H*c*s+s*(1-beta)+c*(1-mu*c) >= 2*c*s)
    return check(sol, 'universal long-chord/full-cross-section/terminal-ray total strictly below 2', True)


def identities_and_assignments():
    t = sp.symbols('t')
    c = (1-t*t)/(1+t*t)
    s = 2*t/(1+t*t)
    g1 = 1+(c+s-1)/(c*s)
    g2 = (2*c-s)/(c*c)+t
    assert sp.cancel(g2-g1+2*t*t*(t*t+2*t-1)/(1-t*t)**2) == 0
    assert sp.cancel(2-g2-t*((1-2*t)**2+t**3*(4-t))/(1-t*t)**2) == 0
    assignments = list(itertools.product([2,3],[3,4],[4,1]))
    valid = sorted(v for v in assignments if len(set(v)) == 3)
    assert valid == [(2,3,1),(2,3,4),(2,4,1),(3,4,1)]
    reflection = {1:2,2:1,3:4,4:3}
    def reflect(v):
        # Reflection exchanges m2 and m4 and fixes m3.
        return (reflection[v[2]],reflection[v[1]],reflection[v[0]])
    assert reflect((2,3,4)) == (3,4,1)
    assert reflect((2,4,1)) == (2,3,1)
    mu,B,L1,S1,L2,S2,U2,L3,S3,U3,L4,S4,U4,A,D,H,J,eta = sp.symbols(
        'mu B L1 S1 L2 S2 U2 L3 S3 U3 L4 S4 U4 A D H J eta')
    # Independently reconstruct the two new positive-trace perimeter sums.
    far = (L2-mu+U2)+(L4-mu+U4)+2+(2-3*mu+S1+S2)+(B-2*mu+L1+S4)
    # The actual far expression equals the report's pre-budget expression.
    assert sp.expand(far-(4-7*mu+B+L1+S1+(L2+S2+U2)+(L4+S4+U4))) == 0
    near = S4+U4+L3+U3+H+(2-3*mu+A+S2)+(B-2*mu+L2+S3)
    assert sp.expand(near-(2-5*mu+B+(A+H)+(L2+S2)+(L3+S3+U3)+(S4+U4))) == 0
    # Direct corner-chain telescoping identity (strict deficits Ti are positive).
    deficits = (2-L2-S2-U2)+(2-L3-S3-U3)+(2-L4-S4-U4)
    excesses = (L2+S3-2*mu)+(L3+S4-2*mu)+(L4+D-2*mu)
    assert sp.expand(deficits+excesses-(D-S2-U2-U3-U4-3*(2*mu-2))) == 0
    return {'corner_grid_endpoint_identities': 'passed',
            'valid_midpoint_injections': [list(v) for v in valid],
            'reflection_orbits': 2,'new_perimeter_and_chain_identities': 'passed'}


if __name__ == '__main__':
    identities = identities_and_assignments()
    rows = [axis_propagation(),parallel_trace(),long_chord()]
    Path(__file__).with_name('round12_input_checks.json').write_text(
        json.dumps({'queries':rows,'identities_and_classification':identities},indent=2),encoding='utf-8')
