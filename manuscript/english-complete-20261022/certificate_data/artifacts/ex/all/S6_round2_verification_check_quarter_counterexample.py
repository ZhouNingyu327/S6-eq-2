"""Exact local three-unit-square covering of the T8 critical quarter.

Valid uniformly for 1 <= mu <= 101/100. This is NOT a six-square cover of
the full target. It shows why the overlap V1 containing m4 must be retained.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sympy as sp


def polygon_tile(normals, offsets):
    # normals are orthonormal, possibly determinant -1; either is a unit square.
    n1,n2=normals
    assert n1[0]**2+n1[1]**2==1 and n2[0]**2+n2[1]**2==1
    assert n1[0]*n2[0]+n1[1]*n2[1]==0
    vertices=[]
    for u,v in [(0,0),(1,0),(1,1),(0,1)]:
        u-=offsets[0];v-=offsets[1]
        vertices.append((n1[0]*u+n2[0]*v,n1[1]*u+n2[1]*v))
    return dict(normals=[[str(x) for x in n] for n in normals],offsets=[str(x) for x in offsets],
                vertices=[[str(x) for x in p] for p in vertices])


def tiles(mu):
    c,s=F(195,197),F(28,197)
    cb,sb=F(12,13),F(5,13)
    c1,s1=F(21,29),F(20,29)
    return [polygon_tile([[-c,s],[s,c]],[(c-s)*mu,-c*mu]),
            polygon_tile([[cb,-sb],[-sb,-cb]],[2*mu*sb,2*mu*cb+mu*sb]),
            polygon_tile([[c1,s1],[-s1,c1]],[F(0),F(0)])]


def contains(z,p):
    x,y=p
    return all(0<=F(a)*x+F(b)*y+F(off)<=1 for (a,b),off in zip(z['normals'],z['offsets']))


def heights(mu,x):
    c,s=F(195,197),F(28,197);cb,sb=F(12,13),F(5,13)
    hc=min((1-mu*c+c*x)/s,(1-s*x)/c)
    ht=min((1-cb*x)/sb,(1-mu*sb+sb*x)/cb)
    return hc,ht


def check():
    # Height sums are concave in x. At the two endpoints of [1/20,mu]
    # both h_C+h_T >= mu, so the two canonical tiles cover that entire strip.
    # Every relevant endpoint inequality is affine decreasing in mu, hence
    # checking mu=1 and mu=101/100 suffices on the whole parameter interval.
    for mu in [F(1),F(101,100)]:
        z=tiles(mu)
        assert contains(z[0],(0,mu)) and contains(z[0],(mu,mu))
        assert contains(z[1],(0,2*mu)) and contains(z[1],(mu,2*mu))
        assert contains(z[2],(0,0)) and contains(z[2],(0,mu))
        assert not contains(z[2],(mu,mu))
        for x in [F(1,20),mu]:
            hc,ht=heights(mu,x)
            assert hc+ht>mu
            print('Endpoint exact surplus:',mu,x,hc+ht-mu,flush=True)
        # The top tile covers all y >= y0 on 0<=x<=1/20.
        y0=(29*mu-13)/12
        h0=2*mu-y0
        assert min(heights(mu,F(0))[1],heights(mu,F(1,20))[1])>=h0
        # V1 covers the complete remaining rectangle in that left strip.
        for x in [F(0),F(1,20)]:
            for y in [mu,y0]:assert contains(z[2],(x,y))
    # Optional dense checks supplement, but do not replace, the concavity proof.
    for mu in [F(1),F(1001,1000),F(101,100)]:
        z=tiles(mu)
        for i in range(101):
            for j in range(101):
                p=(mu*F(i,100),mu+mu*F(j,100))
                assert any(contains(q,p) for q in z)
    out=Path(__file__).resolve().parent/'quarter_counterexample.json'
    out.write_text(json.dumps(dict(a_num=101,a_den=50,mu='101/100',
        scope='critical quarter only, not the full target',tiles=tiles(F(101,100))),indent=2))
    print('PASS: exact rational quarter-cover inequalities for the entire mu interval [1,101/100]',flush=True)


if __name__=='__main__':check()
