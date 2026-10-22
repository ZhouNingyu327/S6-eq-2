"""Universal two-corner inequality, independently certified with rational arithmetic."""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import json,time
import sympy as sp
import z3


def source_polynomials():
    x,y,u,v=sp.symbols('x y u v')
    T=sp.Rational(14,5)-x-sp.Rational(4,5)*y
    C1=(1+x*x)/(1-x*x);C2=(1+y*y)/(1-y*y);C2s=(1+y*y)/(2*y)
    ax=2*x/(1-x*x);ay=2*y/(1-y*y)
    bx=(1+x*x)/(1-x*x);by=(1+y*y)/(1-y*y)
    S1=(1+x*x-2*x*C1)/(1-x*x)
    budget=C1+(1+y*y-(1-S1)*(1-y*y))/(2*y)
    assert sp.cancel(budget-((1-ax/ay)*C1+(bx+by-1)/ay))==0
    raw=[5*(1-x*x)*(1-y*y)*(T-C1-C2),
         10*y*(1-x*x)*(T-C1-C2s),
         10*y*(1-x*x)**2*(T-budget)]
    originals=[sp.Poly(sp.cancel(p),x,y) for p in raw]
    yy=(u*(1+u)+(1-u)*(3+u)*v)/(3*(1+u))
    assert sp.cancel(yy-(u/3+(((1-u/3)/(1+u))-u/3)*v))==0
    transformed=[]
    for p in originals:
        dx=p.degree(x);dy=p.degree(y)
        transformed.append(sp.Poly(sp.cancel(p.as_expr().subs({x:u/3,y:yy})
                                             *3**(dx+dy)*(1+u)**dy),u,v))
    return originals,transformed


def powers(poly):return {ij:F(int(a.p),int(a.q)) for ij,a in poly.terms()}


def power_to_bernstein(coeff,nx,ny):
    return [[sum(a*F(comb(i,p),comb(nx,p))*F(comb(j,q),comb(ny,q))
                 for (p,q),a in coeff.items() if p<=i and q<=j)
             for j in range(ny+1)] for i in range(nx+1)]


def affine_coefficients(coeff,box):
    ua,ub,va,vb=box;out={}
    for (p,q),a in coeff.items():
        for i in range(p+1):
            fu=F(comb(p,i))*ua**(p-i)*(ub-ua)**i
            for j in range(q+1):
                term=a*fu*F(comb(q,j))*va**(q-j)*(vb-va)**j
                out[i,j]=out.get((i,j),F(0))+term
    return out


def path_box(path):
    ua,ub,va,vb=F(0),F(1),F(0),F(1)
    for depth,bit in enumerate(path):
        assert bit in '01'
        if depth%2==0:
            mid=(ua+ub)/2
            if bit=='0':ub=mid
            else:ua=mid
        else:
            mid=(va+vb)/2
            if bit=='0':vb=mid
            else:va=mid
    return ua,ub,va,vb


def certificate():
    originals,transformed=source_polynomials()
    saved=json.loads(Path(__file__).with_name('round8_pair_bernstein_certificate.json').read_text(encoding='utf-8'))
    assert saved['original_polynomials']==[str(p.as_expr()) for p in originals]
    assert saved['transformed_polynomials']==[str(p.as_expr()) for p in transformed]
    paths={leaf['path']:leaf['polynomial'] for leaf in saved['leaves']}
    assert len(paths)==len(saved['leaves'])==45
    visited=set()
    def cover(prefix):
        if prefix in paths:visited.add(prefix);return
        assert len(prefix)<11,'uncovered or invalid binary tree'
        assert any(path.startswith(prefix+'0') for path in paths)
        assert any(path.startswith(prefix+'1') for path in paths)
        cover(prefix+'0');cover(prefix+'1')
    cover('');assert visited==set(paths),'overlapping or unused certificate leaf'
    # Check the Bernstein coefficient formula by an exact expanded identity.
    for poly in transformed:
        U,V=poly.gens;nx,ny=poly.degree_list();b=power_to_bernstein(powers(poly),nx,ny)
        reconstructed=sum(sp.Rational(a.numerator,a.denominator)*sp.binomial(nx,i)*U**i*(1-U)**(nx-i)
                          *sp.binomial(ny,j)*V**j*(1-V)**(ny-j)
                          for i,row in enumerate(b) for j,a in enumerate(row))
        assert sp.expand(poly.as_expr()-reconstructed)==0
    records=[]
    # Independently reconstruct each box by affine power expansion, NOT the generator's de Casteljau splits.
    for path,j in sorted(paths.items()):
        assert j in [0,1,2]
        poly=transformed[j];nx,ny=poly.degree_list();box=path_box(path)
        coeff=affine_coefficients(powers(poly),box)
        bern=power_to_bernstein(coeff,nx,ny)
        minimum=min(a for row in bern for a in row)
        assert minimum>=0,(path,j,minimum)
        records.append({'path':path,'polynomial':j,'box':[str(z) for z in box],
                        'minimum_exact_bernstein_coefficient':str(minimum)})
    return {'status':'45 rational boxes independently verified; full domain covered',
            'box_count':45,'max_depth':max(map(len,paths)),'records':records}


def exact_query():
    x,y,L1,L2=z3.Reals('x y L1 L2')
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(x>0,x<1,y>=x,y<1,L1>=1,L2>=1)
    for t,L in [(x,L1),(y,L2)]:sol.add(L*(1-t*t)<=1+t*t,2*t*L<=1+t*t)
    budget=(1+x*x-2*x*L1)*(1-y*y)+(1+y*y-2*y*L2)*(1-x*x)-(1-x*x)*(1-y*y)
    sol.add(budget>=0,L1+L2+x+z3.RealVal('4/5')*y>z3.RealVal('14/5'))
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'two physical anchored corners, S1+S2>=1: L1+L2+min(t1,t2)+(4/5)max(t1,t2)<=14/5',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


if __name__=='__main__':
    cert=certificate();print('PASS',cert['status'],flush=True)
    records=[exact_query()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round8_two_corner_checks.json').write_text(
        json.dumps({'queries':records,'rational_certificate':cert},indent=2),encoding='utf-8')
