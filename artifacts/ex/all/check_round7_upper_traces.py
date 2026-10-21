"""Exact unit containment, including tangent external contacts."""
from pathlib import Path
import json,time
import sympy as sp
import z3

def run(sol,scope):
    sol.set(timeout=60000);start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':scope,'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}

def upper(kind):
    c,s,mu,alpha,beta,l,r,u,a,b,h,k=z3.Reals('c s mu alpha beta l r u a b h k')
    sol=z3.SolverFor('QF_NRA')
    sol.add(c>0,s>0,c*c+s*s==1,mu>1,alpha>=0,alpha<=1,beta>=0,beta<=1,
            l>=0,r>=0,u>=0)
    points=[(0,0),(-l,0),(r,0),(0,u)]
    trace=l+r+u
    if kind in ['top','both']:
        sol.add(a>0,b>=a,beta>1-c*mu)
        points += [(a,mu),(b,mu)];trace += b-a
    if kind in ['right','both']:
        sol.add(h>0,k>=h,beta<s*mu)
        points += [(mu,h),(mu,k)];trace += k-h
    for x,y in points:
        p=c*x+s*y;q=-s*x+c*y
        sol.add(p>=-alpha,p<=1-alpha,q>=-beta,q<=1-beta)
    sol.add(trace>=2)
    return run(sol,kind+' upper external contact: H+up+external trace(s)<2, tangencies included')

def lower_triangle():
    c,s,mu,d,r,u=z3.Reals('c s mu d r u')
    sol=z3.SolverFor('QF_NRA')
    sol.add(c>=0,s>=0,c*c+s*s==1,mu>1,d>0,r>=0,u>=0,r+u>=1)
    points=[(-mu,-d),(r,0),(0,u)]
    for i in range(len(points)):
        for j in range(i):
            x=points[i][0]-points[j][0];y=points[i][1]-points[j][1]
            p=c*x+s*y;q=-s*x+c*y
            sol.add(p>=-1,p<=1,q>=-1,q<=1)
    return run(sol,'lower-left external point forces right+up rays below 1; reflection covers lower-right')

def symbolic():
    c,s,mu,alpha,beta,l=sp.symbols('c s mu alpha beta l')
    r=beta/s;u=(1-beta)/c
    right=(c*(1-alpha)+s*beta-mu)/(s*c)
    top=(s*(1-alpha)+c*(1-beta)-mu)/(s*c)
    top_expected=u+1/s+1/c-mu/(s*c)+l-alpha/c
    both_expected=l+(2-alpha)*(1/s+1/c)-2*mu/(s*c)
    assert sp.cancel(l+r+u+top-top_expected)==0
    assert sp.cancel(l+r+u+right+top-both_expected)==0
    bound=2*(c+s-mu)/(s*c)-alpha/s
    assert sp.cancel(both_expected+alpha/c-l-bound)==0
    return {'scope':'top and adjacent-upper-side trace identities','result':'exact identities verified'}

if __name__=='__main__':
    records=[upper('right'),upper('top'),upper('both'),lower_triangle()]
    for record in records:print('PASS',record,flush=True)
    identities=symbolic();print('PASS',identities,flush=True)
    Path(__file__).with_name('round7_upper_trace_checks.json').write_text(
        json.dumps({'queries':records,'symbolic':identities},indent=2),encoding='utf-8')
