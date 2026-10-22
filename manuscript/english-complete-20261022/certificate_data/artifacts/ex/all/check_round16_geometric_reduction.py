"""Exact checks for geometric reduction and majorant monotonicity."""
from pathlib import Path
import itertools,json,time
import sympy as sp
import z3

def zqueries():
    rows=[]
    c,s,l,r,u,d,X,Y=z3.Reals('c s l r u d X Y')
    points=[(0,0),(-l,0),(r,0),(0,u),(0,-d),(X,Y)]
    for sign in [1,-1]:
        q=z3.SolverFor('QF_NRA');q.set(timeout=15000)
        q.add(c>=s,s>0,c*c+s*s==1,l>0,l<1,r>0,u>0,d>=0,
            X>r,X<=1,Y>0,Y<u)
        for (a,b),(A,B) in itertools.combinations(points,2):
            U=c*(a-A)+sign*s*(b-B)
            V=-sign*s*(a-A)+c*(b-B)
            q.add(U<=1,U>=-1,V<=1,V>=-1)
        if sign==1:
            necessary=[
                s*u<=1,c*X+s*Y<=1,c*u+s*r<=1,c*u+s*X-c*Y<=1,
                c*l+s*u<=1,c*(l+X)+s*Y<=1,
                s*(l+r)<=1,s*l+s*X-c*Y<=1,
                s*(d+u)<=1,s*d+c*X+s*Y<=1,c*(d+u)<=1]
        else:
            necessary=[
                c*r+s*u<=1,c*X+s*(u-Y)<=1,c*u<=1,s*X+c*Y<=1,
                c*(l+r)<=1,c*(l+X)-s*Y<=1,
                s*l+c*u<=1,s*(l+X)+c*Y<=1,
                s*(d+u)<=1,c*(d+u)<=1,c*d+s*X+c*Y<=1]
        q.add(z3.Or([z3.Not(p) for p in necessary]))
        start=time.time();ans=q.check();assert ans==z3.unsat,ans
        rows.append({'name':'C support implications sign %d'%sign,
            'result':str(ans),'seconds':time.time()-start,
            'inequality_count':len(necessary)})
    q=z3.SolverFor('QF_NRA');q.set(timeout=15000)
    q.add(u>=z3.RealVal('11/15'),d>=0,(u+d)*(u+d)<=2,d>1)
    ans=q.check();assert ans==z3.unsat
    rows.append({'name':'C downward extent d<=1','result':str(ans)})
    # The whole enlarged y domain has b<1/101; no rounded endpoint assumption.
    y=z3.Real('y');q=z3.SolverFor('QF_NRA');q.set(timeout=15000)
    q.add(y>=0,y<=z3.RealVal('4/15'),101*y**4>=(1-y*y)*(1-3*y*y))
    ans=q.check();assert ans==z3.unsat
    rows.append({'name':'b(y)<1/101','result':str(ans)})
    # Increasing scalar A majorant for z>=1/10.
    b,z=z3.Reals('b z');q=z3.SolverFor('QF_NRA');q.set(timeout=15000)
    q.add(b>=0,b<=z3.RealVal('256/36993'),z>=z3.RealVal('1/10'),z<=1,
        (1-b)*z*z-b<=0)
    ans=q.check();assert ans==z3.unsat
    rows.append({'name':'H derivative positive on [1/10,1]','result':str(ans)})
    return rows

def identities():
    x,y,z,k=sp.symbols('x y z k',positive=True)
    S=(1+x*x-2*x*(1+3*y)/(1+y))/(1-x*x)
    L=(1+3*y)/(1+y)
    assert sp.cancel(sp.diff(S,x)+2*(L*(1+x*x)-2*x)/(1-x*x)**2)==0
    assert sp.cancel(sp.diff(S,y)+4*x/((1-x*x)*(1+y)**2))==0
    K=y*y/(1-2*y*y);b=y**4/((1-y*y)*(1-3*y*y))
    assert sp.cancel(K*K/(1-K*K)-b)==0
    c=(1-z*z)/(1+z*z);s=2*z/(1+z*z)
    assert sp.cancel((1-c*(1-2*k*k/(1-k*k)))/s-z-
        (1-z*z)*k*k/(z*(1-k*k)))==0
    assert sp.cancel(sp.diff(b,y)-4*y**3*(1-2*y*y)/((1-y*y)**2*(1-3*y*y)**2))==0
    assert b.subs(y,sp.Rational(4,15))==sp.Rational(256,36993)
    assert sp.Rational(256,36993)<sp.Rational(1,101)
    H=z+b*(1/z-z)
    assert sp.cancel(sp.diff(H,z)-(1-b-b/z**2))==0
    return {'rational_identities':6,'exact_endpoint':'256/36993 < 1/101',
        'S_derivatives_negative':'L>=1, 0<x<1, y>=0',
        'b_derivative_positive':'0<y<=4/15'}

if __name__=='__main__':
    results={'classification':'exact geometric-reduction checks',
        'symbolic':identities(),'queries':zqueries()}
    print(json.dumps(results,indent=2))
    Path(__file__).with_name('round16_geometric_reduction_checks.json').write_text(
        json.dumps(results,indent=2),encoding='utf-8')
