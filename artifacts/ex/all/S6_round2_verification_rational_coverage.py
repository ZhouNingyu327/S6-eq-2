"""Exact continuous coverage check for fixed rational unit-square poses.
Uses rational linear inequalities, not grid points or polygon area tolerance.
"""
import argparse,json
from fractions import Fraction as F
from pathlib import Path
import z3

def convert_tiles(d):
    result=[]
    for q in d['tiles']:
        if 'normals' in q:
            normals=[[F(x) for x in row] for row in q['normals']]
            offsets=[F(x) for x in q['offsets']]
        else:
            A,B,H=q['A'],q['B'],q['H'];den=q['q']*H
            normals=[[F(A,H),F(B,H)],[F(-B,H),F(A,H)]]
            offsets=[F(-q['umin'],den),F(-q['vmin'],den)]
        n1,n2=normals
        assert sum(v*v for v in n1)==sum(v*v for v in n2)==1
        assert sum(a*b for a,b in zip(n1,n2))==0
        result.append((normals,offsets))
    return result

def check(d,quarter=False):
    a=F(d['a_num'],d['a_den']);tiles=convert_tiles(d)
    x,y=z3.Reals('x y');sol=z3.SolverFor('QF_LRA')
    sol.add(x>=0,x<=(a/2 if quarter else a),y>=(a/2 if quarter else 0),y<=a)
    for normals,offsets in tiles:
        u=z3.RealVal(str(normals[0][0]))*x+z3.RealVal(str(normals[0][1]))*y+z3.RealVal(str(offsets[0]))
        v=z3.RealVal(str(normals[1][0]))*x+z3.RealVal(str(normals[1][1]))*y+z3.RealVal(str(offsets[1]))
        sol.add(z3.Or(u<0,u>1,v<0,v>1))
    r=sol.check();result=dict(result=str(r),scope='critical quarter' if quarter else 'full target',arithmetic='exact rational linear')
    if r==z3.sat:
        mdl=sol.model()
        xx=F(mdl.eval(x).as_fraction());yy=F(mdl.eval(y).as_fraction())
        assert 0<=xx<=a and 0<=yy<=a
        for normals,offsets in tiles:
            u=normals[0][0]*xx+normals[0][1]*yy+offsets[0]
            v=normals[1][0]*xx+normals[1][1]*yy+offsets[1]
            assert u<0 or u>1 or v<0 or v>1
        result['verified_uncovered_point']=[str(xx),str(yy)]
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('path');ap.add_argument('--quarter',action='store_true');args=ap.parse_args()
    d=json.loads(Path(args.path).read_text());result=check(d,args.quarter)
    print(result,flush=True)
    Path(args.path+'.continuous_check.json').write_text(json.dumps(result,indent=2))
