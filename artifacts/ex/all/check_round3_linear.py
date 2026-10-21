"""Exact real linear checks of the aggregation arguments in round three.
Geometry input lemmas are proved in the reports. UNSAT checks their algebraic
consequences over all real values, not sampled numerical configurations.
"""
from pathlib import Path
import json
import z3

def base():
    sol=z3.SolverFor('QF_LRA');mu,B=z3.Reals('mu B')
    L=z3.Reals('L1 L2 L3 L4');S=z3.Reals('S1 S2 S3 S4');U=z3.Reals('U1 U2 U3 U4')
    sol.add(mu>1,B<1,B>=0)
    for l,s,u in zip(L,S,U):sol.add(l>=mu,s>=0,u>=0,l+s+u<=2,s+u<=B)
    return sol,mu,B,L,S,U

def check_opposite():
    sol,mu,B,L,S,U=base();g1,g3,hC,hF=z3.Reals('g1 g3 hC hF')
    sol.add(g1>0,g3>0,g1==2*mu-L[0]-S[1],g3==2*mu-L[2]-S[3],
            L[1]+S[2]>=2*mu,L[3]+S[0]>=2*mu,
            hC>=0,hF>=0,hC+g1<=B,hF+g3<=B,hC+hF+U[1]+U[3]>=2*mu)
    r=sol.check();assert r==z3.unsat
    return dict(result=str(r),scope='opposite two-gap case',input='star and coupled section inequalities')

def check_adjacent_left():
    # sqrt(2) < 10/7. This weaker rational diameter bound is sufficient.
    sol,mu,B,L,S,U=base();D=z3.RealVal('10/7')
    sol.add(L[2]<=D,L[2]+S[3]>=2*mu,U[3]>=2*mu-D)
    r=sol.check();assert r==z3.unsat
    return dict(result=str(r),scope='right-gap extra cannot cover left critical tip',diameter_upper='10/7')

def check_adjacent_right():
    sol,mu,B,L,S,U=base();D=z3.RealVal('10/7')
    g1,hC=z3.Reals('g1 hC')
    sol.add(L[0]<=D,L[2]<=D,L[2]+S[3]>=2*mu,
            g1>0,g1==2*mu-L[0]-S[1],hC>=2*mu-U[1]-U[3],hC+g1<=B)
    r=sol.check();assert r==z3.unsat
    return dict(result=str(r),scope='bottom-gap extra cannot cover both horizontal critical tips',diameter_upper='10/7')

def check_adjacent_regular():
    sol,mu,B,L,S,U=base();g1,g2,hC,vF,DC,RF=z3.Reals('g1 g2 hC vF DC RF')
    sol.add(mu+B<2,g1>0,g2>0,g1==2*mu-L[0]-S[1],g2==2*mu-L[1]-S[2],
            L[2]+S[3]>=2*mu,L[3]+S[0]>=2*mu,
            hC+g1<=B,vF+g2<=B,DC<=mu,RF<=mu,
            4*mu-sum(U)<=hC+vF+DC+RF)
    r=sol.check();assert r==z3.unsat
    return dict(result=str(r),scope='adjacent gaps with left tip in C and top tip in F')

if __name__=='__main__':
    records=[check_opposite(),check_adjacent_left(),check_adjacent_right(),check_adjacent_regular()]
    for r in records:print('PASS exact universal aggregation:',r,flush=True)
    Path(__file__).with_name('round3_linear_checks.json').write_text(json.dumps(records,indent=2))
