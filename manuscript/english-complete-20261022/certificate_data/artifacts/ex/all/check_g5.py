"""Exact rational checks of the coupled grid bounds and the G5 k=2 proof."""
from fractions import Fraction as F
import random,json,time
from pathlib import Path
import sympy as sp
import z3


def interval(unit,axis,k,a):
    low=F(0);high=a
    for (nx,ny),off in zip(unit['normals'],unit['offsets']):
        coef=ny if axis==0 else nx
        base=(nx if axis==0 else ny)*k+off
        if not coef:
            if not 0<=base<=1:return None
            continue
        b0=-base/coef;b1=(1-base)/coef
        if b0>b1:b0,b1=b1,b0
        low=max(low,b0);high=min(high,b1)
        if low>high:return None
    return low,high


def union_length(intervals):
    intervals=sorted(z for z in intervals if z is not None)
    if not intervals:return F(0)
    total=F(0);low,high=intervals[0]
    for x,y in intervals[1:]:
        if x>high:total+=high-low;low,high=x,y
        else:high=max(high,y)
    return total+high-low


def grid_length(units,mu):
    return sum(union_length([interval(z,axis,k,2*mu) for z in units]) for axis in [0,1] for k in [F(0),mu,2*mu])


def params(rng,mu):
    while True:
        t=F(rng.randrange(1,1000),1000)
        c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
        if mu*c<=1 and mu*s<=1:break
    alpha=(1-mu*c)*F(rng.randrange(1001),1000)
    beta=mu*s+(1-mu*s)*F(rng.randrange(1001),1000)
    return c,s,alpha,beta


def check_rational():
    rng=random.Random(514927)
    for trial in range(2000):
        mu=F(rng.randrange(10001,10301),10000)
        c,s,alpha,beta=params(rng,mu)
        H=min((1-alpha)/c,beta/s)
        L=(1-beta)/c+alpha/s
        U=(1-alpha-mu*c)/s
        assert H+L+U<2
        C=dict(normals=[[c,s],[-s,c]],offsets=[alpha-s*mu,beta-c*mu])
        cf,sf,af,bf=params(rng,mu)
        Fa=dict(normals=[[sf,cf],[cf,-sf]],offsets=[af-sf*mu,bf-cf*mu])
        Fo=dict(normals=[[-cf,sf],[sf,cf]],offsets=[af+2*cf*mu-sf*mu,bf-2*sf*mu-cf*mu])
        assert grid_length([C,Fa],mu)<4
        assert grid_length([C,Fo],mu)<4
        # Independent corner grid test (does not require a midpoint anchor).
        t=F(rng.randrange(1001),1000);cc=(1-t*t)/(1+t*t);ss=2*t/(1+t*t)
        z=dict(normals=[[cc,ss],[-ss,cc]],offsets=[F(0),F(rng.randrange(1001),1000)])
        assert grid_length([z],mu)<=2
    print('PASS: 2000 rational star, corner-grid, adjacent- and opposite-G5 configurations',flush=True)


def check_symbolic():
    t=sp.symbols('t',positive=True);c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
    g1=1+(c+s-1)/(c*s);g2=(2*c-s)/(c*c)+t
    assert sp.simplify(g2-g1+2*t*t*(t*t+2*t-1)/(1-t*t)**2)==0
    assert sp.simplify(2-g2-t*((1-2*t)**2+t**3*(4-t))/(1-t*t)**2)==0
    print('PASS: exact corner-grid and star-bound polynomial identities',flush=True)


def check_nra():
    # Universal single-tile star inequality independently checked by NLSAT.
    # Searching for >=2 (not merely >2) gives a strict inequality when mu>1.
    c,s,mu,beta,H=z3.Reals('c s mu beta H')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(c>0,s>0,c*c+s*s==1,mu>1,mu*c<=1,mu*s<=1,
            beta>=mu*s,beta<=1,H>=mu,H*c<=1,H*s<=beta)
    sol.add(H*c*s+s*(1-beta)+c*(1-mu*c)>=2*c*s)
    t=time.time();result=sol.check()
    d=dict(result=str(result),seconds=round(time.time()-t,3),scope='universal single-tile star inequality',exact_real_arithmetic=True)
    if result==z3.unknown:d['reason']=sol.reason_unknown()
    if result==z3.sat:d['model']=str(sol.model())
    Path(__file__).with_name('star_nra_check.json').write_text(json.dumps(d,indent=2))
    print('NLSAT independent universal check:',d,flush=True)
    assert result==z3.unsat, 'Only unsat verifies the universal star inequality.'


if __name__=='__main__':
    check_symbolic()
    check_rational()
    check_nra()
