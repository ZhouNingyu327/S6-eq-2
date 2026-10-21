"""Universal exact real counterexample queries for strengthened corner bounds."""
from pathlib import Path
import json,time
import z3
import sympy as sp


def elimination_identities():
    mu,c,s,L,S,U=sp.symbols('mu c s L S U')
    D=mu*L-S*U
    e1=c*S+s*L-1;e2=s*U+mu*c-1
    assert sp.expand(c*D-(L-U)-L*e2+U*e1)==0
    assert sp.expand(s*D-(mu-S)-mu*e1+S*e2)==0
    return {'symbolic_identities':'corner-angle elimination passed',
            'identity':'(mu*L-S*U)^2=(L-U)^2+(mu-S)^2'}


def corner_solver():
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    mu,c,s,L,S,U=z3.Reals('mu c s L S U')
    sol.add(mu>1,c>0,s>0,c*c+s*s==1,L>=mu,c*L<=1,s*L<=1,
            S>=0,U>=0,c*S+s*L==1,s*U+mu*c==1)
    return sol,mu,c,s,L,S,U


def product():
    sol,mu,c,s,L,S,U=corner_solver();sol.add(S+U+S*U>=1)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'anchored corner S+U+S*U<1','result':str(res),
            'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def weighted():
    sol,mu,c,s,L,S,U=corner_solver();sol.add(L+z3.RealVal('3/4')*U>=z3.RealVal('7/4'))
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'anchored corner L+(3/4)*U<7/4','result':str(res),
            'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def sharp_weighted():
    sol,mu,c,s,L,S,U=corner_solver();d=z3.Real('sqrt2')
    sol.add(d>0,d*d==2,d*L+U>=d+1)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'anchored corner L+U/sqrt(2)<1+1/sqrt(2)',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


if __name__=='__main__':
    print('PASS',elimination_identities(),flush=True)
    records=[product(),weighted(),sharp_weighted()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_corner_product_checks.json').write_text(json.dumps(records,indent=2))
