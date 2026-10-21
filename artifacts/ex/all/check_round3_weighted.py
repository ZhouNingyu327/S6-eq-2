"""Exact checks of the weighted three-ray bound and the final one-gap argument.

No floating point optimizer is part of these checks. All counterexample queries
must return UNSAT; UNKNOWN is a failed verification.
"""
from pathlib import Path
import itertools
import json
import time
import sympy as sp
import z3
from check_round3_onegap import onegap


def weighted_rays():
    p,q,x,y,r = z3.Reals('p q x y r')
    sol = z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(p >= 0,q >= 0,p*p+q*q == 1,x >= 0,y >= 0,r >= 0,
            x+y+z3.RealVal('3/4')*r > 2)
    points = [(0,0),(-x,0),(r,0),(0,y)]
    for a,b in itertools.combinations(points,2):
        dx,dy = a[0]-b[0],a[1]-b[1]
        u,v = p*dx+q*dy,-q*dx+p*dy
        sol.add(u >= -1,u <= 1,v >= -1,v <= 1)
    Path(__file__).with_name('round3_weighted_counterexample.smt2').write_text(sol.to_smt2())
    start=time.time();result=sol.check();assert result == z3.unsat,result
    return {'scope':'unit square three-ray bound x+y+(3/4)r<=2; no x,y,r<=1 assumed',
            'result':str(result),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def corner_bound():
    c,s,L,t = z3.Reals('c s L t')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(c > 0,s > 0,c*c+s*s == 1,L >= 1,c*L <= 1,s*L <= 1,
            t*s == 1-c,t > 0,t < 1,L-1 >= z3.RealVal('3/4')*(1-t))
    Path(__file__).with_name('round3_corner_ratio_counterexample.smt2').write_text(sol.to_smt2())
    start=time.time();result=sol.check();assert result == z3.unsat,result
    return {'scope':'L-1<(3/4)(1-t), t=(1-c)/s, L<=min(1/c,1/s)',
            'result':str(result),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def right_tip():
    sol,mu,B,L,S,U=onegap()
    g=2*mu-L[0]-S[1]
    sol.add(g > 0,g+mu-U[1] <= B)
    result=sol.check();assert result == z3.unsat,result
    return {'scope':'bottom-gap block cannot contain right critical tip in three-meet case',
            'result':str(result),'arithmetic':'exact linear reals'}


def final_aggregation():
    mu,t,L,U3,U4,r=z3.Reals('mu t L U3 U4 r')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu > 1,t > 0,t < 1,U3 >= 0,U4 >= 0,
            U3+U4 < L-mu,L-1 < z3.RealVal('3/4')*(1-t),r > 1-t,
            (mu-U4)+(mu-U3)+z3.RealVal('3/4')*r <= 2)
    result=sol.check();assert result == z3.unsat,result
    return {'scope':'one-gap final contradiction from three meets, corner ratio, weighted rays',
            'result':str(result),'arithmetic':'exact linear reals'}


def dual_identities():
    t=sp.symbols('t',positive=True)
    p=(1-t*t)/(1+t*t);q=2*t/(1+t*t);w=sp.Rational(3,4)
    a=q+p/4;b=p-q/4
    gamma_A=1/p-q-p/4
    gamma_B=(1-a*p)/q
    for gamma,chord in [(gamma_A,p),(gamma_B,q)]:
        assert sp.cancel(a*p+gamma*chord-1)==0
        assert sp.cancel(a*q+b*p-1)==0
        assert sp.cancel(b*q+gamma*chord-w)==0
    assert sp.cancel(a+b+gamma_A-(p+1/p-q/4))==0
    assert sp.cancel(a+b+gamma_B-(7*q/4+p/4+3*p*p/(4*q)))==0
    v=sp.symbols('v')
    assert sp.expand((7+v+3*v*v)**2-64*(1+v*v)) == 9*v**4+6*v**3-21*v**2+14*v-15
    return {'scope':'hand-proof dual coefficients and polynomial expansion','result':'exact symbolic identities passed'}


if __name__=='__main__':
    records=[weighted_rays(),corner_bound(),right_tip(),final_aggregation(),dual_identities()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round3_weighted_checks.json').write_text(json.dumps(records,indent=2))
