"""Universal continuous geometry of a centre tile meeting the upper right edge."""
from pathlib import Path
import json,time
import sympy as sp
import z3


def run(sol,scope):
    sol.set(timeout=60000);start=time.time();result=sol.check()
    assert result==z3.unsat,result
    return {'scope':scope,'result':str(result),'arithmetic':'exact nonlinear reals',
            'seconds':time.time()-start}


def parameter_trace():
    c,s,mu,alpha,beta,l,r,u,d=z3.Reals('c s mu alpha beta l r u d')
    sol=z3.SolverFor('QF_NRA')
    sol.add(c>0,s>0,c*c+s*s==1,mu>1,alpha>=0,alpha<=1,beta>=0,beta<=1,
            beta<s*mu,d>0,d*s*c==c*(1-alpha)+s*beta-mu,
            l>=0,l*c<=alpha,l*s<=1-beta,r*s==beta,u*c==1-beta,l+r+u+d>=2)
    return run(sol,'full upper-right chord plus left/right/up centre rays is strictly below 2')


def direct_containment():
    c,s,mu,alpha,beta,l,r,u,a,b=z3.Reals('c s mu alpha beta l r u a b')
    sol=z3.SolverFor('QF_NRA')
    sol.add(c>0,s>0,c*c+s*s==1,mu>1,alpha>=0,alpha<=1,beta>=0,beta<=1,
            l>=0,r>=0,u>=0,a>0,b>a,beta<s*mu)
    for x,y in [(0,0),(-l,0),(r,0),(0,u),(mu,a),(mu,b)]:
        pa=c*x+s*y;pb=-s*x+c*y
        sol.add(pa>=-alpha,pa<=1-alpha,pb>=-beta,pb<=1-beta)
    sol.add(l+r+u+b-a>=2)
    return run(sol,'independent direct point containment and right-midpoint exclusion imply the same trace bound')


def symbolic():
    c,s,mu,alpha,beta,l,r=sp.symbols('c s mu alpha beta l r')
    d=(c*(1-alpha)+s*beta-mu)/(s*c)
    u=(1-beta)/c
    total=l+beta/s+u+d
    assert sp.cancel(total-(beta/s+1/s+1/c-mu/(s*c)+l-alpha/s))==0
    extra=(1-s*r)*(s-c)/s**2
    expression=sp.expand(r+1/s+1/c-mu/(s*c)+extra)
    expected=c*r/s+2/s+1/c-c/s**2-mu/(s*c)
    assert sp.cancel(expression-expected)==0
    N=c*c*s+2*c*s+s*s-c*c-s-2*c*s*s
    assert sp.expand(N-(1-s)*(-c*c+2*c*s-s))==0
    assert sp.expand((-c*c+2*c*s-s)-(-(s-c)**2-s*(1-s)))==0
    return {'scope':'rational trace reductions and strict final sign identity','result':'exact identities verified'}


if __name__=='__main__':
    records=[parameter_trace(),direct_containment()]
    identities=symbolic()
    for record in records:print('PASS',record,flush=True)
    print('PASS',identities,flush=True)
    Path(__file__).with_name('round6_right_trace_checks.json').write_text(
        json.dumps({'queries':records,'symbolic':identities},indent=2),encoding='utf-8')
