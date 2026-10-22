"""Exact/symbolic checks for scale margins and the parallel-section bound."""
from fractions import Fraction as F
import random
import math
import sympy as sp
from finite_open import depth


def scale_parameters(r):
    return r,4*r,(1-r*r)/(1+r*r),2*r/(1+r*r),r*r/(1+r*r)


def rho2(p):
    x,y=p
    return min((x-a)**2+(y-b)**2 for a,b in [(1,0),(2,1),(1,2),(0,1)])


def test_scale_margin():
    rng=random.Random(74931)
    for r in [F(1,16),F(1,64),F(1,256),F(1,4096),F(1,65536)]:
        par=scale_parameters(r);e=par[-1];delta=e/2
        points=[(F(i,40),F(j,40)) for i in range(81) for j in range(81)]
        points += [(F(rng.randrange(20001),10000),F(rng.randrange(20001),10000)) for _ in range(2000)]
        # Include points extremely close to midpoints and scale boundaries.
        for mx,my in [(1,0),(2,1),(1,2),(0,1)]:
            for dx in [-6*r,-3*r,-delta,0,delta,3*r,6*r]:
                for dy in [-6*r,-3*r,-delta,0,delta,3*r,6*r]:
                    x,y=mx+dx,my+dy
                    if 0<=x<=2 and 0<=y<=2:points.append((x,y))
        n=0
        for p in points:
            rr=rho2(p)
            if rr<=delta*delta or rr>=36*r*r:
                assert depth(p,par)>=delta,(r,p,depth(p,par),delta)
                n+=1
        assert 6*(r*r/16)<e/2
        print('PASS exact rational scale margin:',r,'tested guaranteed points',n,flush=True)
    for N in range(6):
        b=8*2**N-4;r=F(1,2**b)
        eps=F(1,4*(1+2**(16*2**N-8)))
        assert eps==r*r/(4*(1+r*r))
    print('PASS exact scale recurrence and explicit epsilon_N formula',flush=True)


def test_section_algebra():
    z,d=sp.symbols('z d',positive=True)
    g=2*(z-d)/(z*z-1)
    assert sp.simplify(sp.diff(g,z)-2*(-z*z+2*d*z-1)/(z*z-1)**2)==0
    h=sp.sqrt(d*d-1);zs=d+h
    assert sp.simplify(g.subs(z,zs)-(d-h))==0
    threshold=3/(2*sp.sqrt(2))
    assert sp.simplify((d+h).subs(d,threshold)-sp.sqrt(2))==0
    t=sp.symbols('t',positive=True)
    c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
    assert sp.factor(1+c*s-c-s)==2*t*t*(t-1)**2/(1+t*t)**2
    print('PASS exact section derivative, optimum and branch junction',flush=True)

    # Direct polygon slicing sanity, entirely rational with a unit frame.
    # Unit square vertices: (0,0),(c,s),(c-s,s+c),(-s,c).
    rng=random.Random(556)
    for _ in range(3000):
        t=F(rng.randrange(1,1000),1000)
        c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
        if c<s:c,s=s,c
        d=F(rng.randrange(10001,14142),10000)
        if d>c+s:continue
        offset=(c+s-d)*F(rng.randrange(1001),1000)
        # x_min=-s, and both cuts lie in the two triangular ends.
        assert 0<=offset<s and c<offset+d<=c+s
        total=offset/(s*c)+(c+s-offset-d)/(s*c)
        assert total==(c+s-d)/(s*c)<1
    print('PASS 3000 rational orientations/translations for coupled sections',flush=True)


if __name__=='__main__':
    test_scale_margin()
    test_section_algebra()
