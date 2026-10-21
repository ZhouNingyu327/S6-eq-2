"""Exact local k=1 counterexample to a blanket extra-grid bound <=4.
Only a two-tile grid trace example, not a covering of the entire target.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from check_g5 import grid_length


def contains(unit,p):
    return all(0 <= n[0]*p[0]+n[1]*p[1]+off <= 1
               for n,off in zip(unit['normals'],unit['offsets']))


def main():
    mu=F(1001,1000);c=F(43,925);s=F(924,925)
    C={'normals':[[s,c],[c,-s]],'offsets':[1-mu*(s+c),mu*(s-c)]}
    cf,sf=F(119,169),F(120,169)
    other={'normals':[[cf,sf],[-sf,cf]],'offsets':[F(1,2)-mu*(cf+sf),F(1,2)+mu*(sf-cf)]}
    units=[C,other]
    for unit in units:
        n,v=unit['normals']
        assert sum(a*a for a in n)==1 and sum(a*a for a in v)==1
        assert sum(a*b for a,b in zip(n,v))==0
        assert contains(unit,(mu,mu))
    mids=[(mu,0),(2*mu,mu),(mu,2*mu),(0,mu)]
    claims=[[contains(unit,p) for p in mids] for unit in units]
    assert claims==[[True,False,False,False],[False,False,False,False]],claims
    length=grid_length(units,mu)
    assert length>4,length
    data={'mu':str(mu),'units':[{'normals':[[str(a) for a in n] for n in z['normals']],
                               'offsets':[str(a) for a in z['offsets']]} for z in units],
          'midpoint_claims':claims,'grid_union_length':str(length),'grid_union_decimal':float(length),
          'both_contain_centre':True,'k':1,'verification':'exact Fraction arithmetic passed',
          'scope':'two centre tiles only; not a six-tile target covering'}
    Path(__file__).with_name('one_mid_grid_counterexample.json').write_text(json.dumps(data,indent=2))
    print('PASS exact k=1 local counterexample:',length,'>',4,flush=True)


if __name__=='__main__':main()
