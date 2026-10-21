"""Independently recheck exact unit poses, point coverage and whole-quarter coverage."""
from pathlib import Path
from fractions import Fraction as F
import json
from rational_coverage import convert_tiles,check

ROOT=Path(__file__).resolve().parent

def inside(tile,p):
    normals,offsets=tile
    return all(0<=nx*p[0]+ny*p[1]+off<=1
               for (nx,ny),off in zip(normals,offsets))

if __name__=='__main__':
    for a in ['2.02','2.025']:
        d=json.loads((ROOT/('actual_'+a+'.json')).read_text())
        pd=json.loads((ROOT/('trial_'+a+'.source.json')).read_text())
        tiles=convert_tiles(d)
        assert len(tiles)==6 and d['npoints']==len(pd['points_integer'])
        assert (d['a_num'],d['a_den'])==(pd['a_num'],pd['a_den'])
        for x,y in pd['points_integer']:
            assert any(inside(q,(F(x,pd['q']),F(y,pd['q']))) for q in tiles)
        for w in d['exact_uncovered_witnesses']:
            p=(F(w['X'],d['q']),F(w['Y'],d['q']))
            a_rat=F(d['a_num'],d['a_den'])
            assert 0<=p[0]<=a_rat and 0<=p[1]<=a_rat
            assert all(not inside(q,p) for q in tiles)
        full=check(d)
        assert full['result']=='sat'
        print('PASS exact six-unit cover of 201 points; full target has a verified hole:',a,full,flush=True)
    q=json.loads((ROOT/'quarter_counterexample.json').read_text())
    r=check(q,quarter=True)
    assert r['result']=='unsat'
    print('PASS exact continuous coverage of the entire critical quarter:',r,flush=True)
