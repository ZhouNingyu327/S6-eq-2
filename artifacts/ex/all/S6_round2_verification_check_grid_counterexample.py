"""A rational counterexample to the proposed bound |(C union F) cap grid|<=4.
Both squares contain the target centre, neither contains an edge midpoint.
This is a local trace example, not a covering of the full target.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from check_g5 import grid_length

def unit(c,s,alpha,beta,mu):
    return dict(normals=[[c,s],[-s,c]],
                offsets=[alpha-(c+s)*mu,beta+(s-c)*mu])

def inside(q,p):
    return all(0<=nx*p[0]+ny*p[1]+off<=1
               for (nx,ny),off in zip(q['normals'],q['offsets']))

if __name__=='__main__':
    mu=F(1001,1000)
    units=[unit(F(119,169),F(120,169),F(1,2),F(1,2),mu),
           unit(F(1599,1601),F(80,1601),F(0),F(1,1000),mu)]
    for q in units:
        assert inside(q,(mu,mu))
        assert all(not inside(q,p) for p in [(0,mu),(mu,0),(2*mu,mu),(mu,2*mu)])
    length=grid_length(units,mu)
    assert length>4
    data=dict(mu=str(mu),a_num=1001,a_den=500,scope='grid trace only; no full-target cover',
              k=0,grid_length=str(length),grid_length_float=float(length),
              tiles=[dict(normals=[[str(x) for x in row] for row in q['normals']],
                          offsets=[str(x) for x in q['offsets']]) for q in units])
    Path(__file__).with_name('grid_counterexample.json').write_text(json.dumps(data,indent=2))
    print('PASS: two centre tiles, k=0, exact grid length',length,'=',float(length),'>4',flush=True)
