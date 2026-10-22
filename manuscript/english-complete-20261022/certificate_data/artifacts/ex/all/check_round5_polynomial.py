"""Exact symbolic certificates and continuous counterexample checks for round 5."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def identities():
    t, k, x = sp.symbols('t k x')
    L = 1 + 2*k/(1+k)
    S = (1+t*t-2*t*L)/(1-t*t)
    w = k*k/(1-2*k*k)
    phi = 1-S-t-2*k+k*k-w
    compact = t*(1-t)/(1+t)+4*t*k/((1-t*t)*(1+k))-2*k-2*k**4/(1-2*k*k)
    psi = t*(1-t)/(1+t)+4*t*k/((1-t*t)*(1+k))-2*k-k*k/6
    P = 24*t**8-71*t**7-120*t**6+154*t**5+78*t**4-107*t**3+24*t-6
    Q = 6*t**4-83*t**3+309*t**2-153*t+17
    Kc = t*t/(1-2*t*t)
    Ks = (1-t)**2/(6*t-1-t*t)
    expected_c = -t*P/(6*(1-t)**2*(1+t)**2*(1-2*t*t)**2)
    expected_s = (1-t)*Q/(6*(t*t-6*t+1)**2)
    assert sp.cancel(phi-compact) == 0
    assert sp.cancel(phi-psi-k*k*(1-14*k*k)/(6*(1-2*k*k))) == 0
    assert sp.cancel(sp.diff(psi,k,2)+8*t/((1-t*t)*(1+k)**3)+sp.Rational(1,3)) == 0
    assert sp.cancel(psi.subs(k,Kc)-expected_c) == 0
    assert sp.cancel(psi.subs(k,Ks)-expected_s) == 0
    bs = [sp.Rational(6),sp.Rational(19,4),sp.Rational(7,2),
          sp.Rational(231103,96768),sp.Rational(24503,16128),
          sp.Rational(6477551,6967296),sp.Rational(1002889,1741824),
          sp.Rational(104107099,286654464),sp.Rational(7742393,35831808)]
    reconstructed = sum(bs[j]*sp.binomial(8,j)*x**j*(1-x)**(8-j) for j in range(9))
    assert sp.expand(-P.subs(t,sp.Rational(5,12)*x)-reconstructed) == 0
    assert all(b > 0 for b in bs)
    assert Q.subs(t,sp.Rational(2,5)) == sp.Rational(51,625)
    assert sp.diff(Q,t).subs(t,sp.Rational(2,5)) == sp.Rational(6987,125)
    assert sp.diff(Q,t,2).subs(t,1) == 192
    assert sp.expand(sp.diff(Q,t,3)-(144*t-498)) == 0
    return {'scope':'symbolic identities, positive Bernstein certificate, derivative certificate',
            'result':'exact identities verified', 'bernstein_coefficients':[str(b) for b in bs],
            'polynomial_P':str(P),'polynomial_Q':str(Q)}


def run(sol, scope):
    sol.set(timeout=60000)
    start = time.time()
    result = sol.check()
    assert result == z3.unsat, result
    return {'scope':scope,'result':str(result),'arithmetic':'exact nonlinear reals',
            'seconds':time.time()-start}


def polynomial_c():
    t=z3.Real('t'); sol=z3.SolverFor('QF_NRA')
    P=24*t**8-71*t**7-120*t**6+154*t**5+78*t**4-107*t**3+24*t-6
    sol.add(t>=0,t<=z3.RealVal('5/12'),P>=0)
    return run(sol,'P(t)<0 on the full interval [0,5/12]')


def polynomial_s():
    t=z3.Real('t'); sol=z3.SolverFor('QF_NRA')
    Q=6*t**4-83*t**3+309*t*t-153*t+17
    sol.add(t>=z3.RealVal('2/5'),t<=1,Q<=0)
    return run(sol,'Q(t)>0 on the full interval [2/5,1]')


def phi_gap():
    k=z3.Real('k'); sol=z3.SolverFor('QF_NRA')
    sol.add(k>0,k<z3.RealVal('4/15'),k*k*(1-14*k*k)<=0)
    return run(sol,'Phi-Psi is strictly positive for 0<k<4/15')


def final_contradiction():
    l,r,u,t,k,S,w,phi=z3.Reals('l r u t k S w phi')
    sol=z3.SolverFor('QF_NRA')
    sol.add(l>=0,r>=0,u>=0,t>0,t<1,k>0,k<z3.RealVal('4/15'),
            w*(1-2*k*k)==k*k,
            l>1-S-w,r>1-t,u>1-k,
            phi==1-S-t-2*k+k*k-w,phi>0,l+r+u*u<=2)
    return run(sol,'forced three rays contradict the universal unit-square parabola')


if __name__=='__main__':
    symbolic = identities()
    print('PASS',symbolic,flush=True)
    records=[polynomial_c(),polynomial_s(),phi_gap(),final_contradiction()]
    for record in records:
        print('PASS',record,flush=True)
    Path(__file__).with_name('round5_polynomial_checks.json').write_text(
        json.dumps({'symbolic':symbolic,'queries':records},indent=2),encoding='utf-8')
