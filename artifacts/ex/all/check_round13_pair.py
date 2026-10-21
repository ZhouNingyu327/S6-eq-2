"""Independent exact verification of the new adjacent-corner budget.

The certificate stores rational Bernstein coefficients. This checker derives
the polynomials from the geometric formulas and reconstructs the whole
polynomial from those coefficients; it does not call the generator.
"""
from pathlib import Path
import json,time
import sympy as sp
import z3


def certificate():
    x,y,u,v=sp.symbols('x y u v')
    ax=2*x/(1-x*x);ay=2*y/(1-y*y)
    bx=(1+x*x)/(1-x*x);by=(1+y*y)/(1-y*y)
    upper=(1-ax*ay)*by+bx-2*ax+ax*by+x+2*y-y*y
    P=sp.Poly(sp.cancel((2-upper)*(1-x*x)*(1-y*y)**2),x,y)
    Q=sp.Poly((1-x*x)*(1-y*y)-4*x*y,x,y)
    saved=json.loads(Path(__file__).with_name('round13_pair_certificate.json').read_text(encoding='utf-8'))
    expected=[('c',sp.Rational(2,5)*u,x*x/(1-2*x*x)),
              ('s',sp.Rational(2,5)+sp.Rational(3,5)*u,(1-x)**2/(6*x-1-x*x))]
    assert [r['branch'] for r in saved]==['c','s']
    records=[]
    for row,(name,xx,Y) in zip(saved,expected):
        assert row['original_polynomials']==[str(p.as_expr()) for p in [P,Q]]
        denominator=sp.denom(Y)
        for j,p in enumerate([P,Q]):
            transformed=sp.Poly(sp.expand(sp.cancel(p.as_expr().subs(y,Y*v)*denominator**p.degree(y)).subs(x,xx)),u,v)
            b=[[sp.Rational(z) for z in r] for r in row['coefficients'][j]]
            nx,ny=transformed.degree_list()
            assert len(b)==nx+1 and all(len(r)==ny+1 for r in b)
            assert all(z>=0 for r in b for z in r)
            reconstructed=sum(z*sp.binomial(nx,i)*u**i*(1-u)**(nx-i)
                                *sp.binomial(ny,k)*v**k*(1-v)**(ny-k)
                              for i,r in enumerate(b) for k,z in enumerate(r))
            assert sp.Poly(sp.expand(transformed.as_expr()-reconstructed),u,v).is_zero
            records.append({'branch':name,'polynomial':['objective','nonnegative LP coefficient'][j],
                            'degrees':[nx,ny],'minimum':str(min(z for r in b for z in r)),
                            'coefficients':sum(len(r) for r in b),'whole_rectangle_verified':True})
    return {'parameter_rectangles':2,'polynomial_identities':4,'records':records}


def query():
    x,y,Lx,Ly,Sx,Sy=z3.Reals('x y Lx Ly Sx Sy')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(x>0,x<1,y>0,y<1,Lx>=1,Ly>=1)
    for t,L,S in [(x,Lx,Sx),(y,Ly,Sy)]:
        sol.add(L*(1-t*t)<=1+t*t,2*t*L<=1+t*t,
                S*(1-t*t)==1+t*t-2*t*L,S>=0)
    sol.add(Lx+Sy>=2,Ly+Sx+x+2*y-y*y>2)
    start=time.time();answer=sol.check();assert answer==z3.unsat,answer
    return {'scope':'adjacent anchored corners: Lx+Sy>=2 implies Ly+Sx+x+2y-y^2<=2',
            'result':str(answer),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


if __name__=='__main__':
    cert=certificate();print('PASS',cert,flush=True)
    records=[query()]
    for row in records:print('PASS',row,flush=True)
    Path(__file__).with_name('round13_pair_checks.json').write_text(json.dumps({'certificate':cert,'queries':records},indent=2),encoding='utf-8')
