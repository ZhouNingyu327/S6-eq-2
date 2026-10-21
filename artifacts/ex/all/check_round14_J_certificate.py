"""Independent reconstruction of all rational rectangles in the J=0 proof."""
from pathlib import Path
from fractions import Fraction
from math import comb
import json
import sympy as sp

def bernstein_coefficients(poly):
    nx,ny=poly.degree_list();out=[]
    terms=poly.terms()
    for i in range(nx+1):
        for j in range(ny+1):
            b=sum(a*sp.Rational(comb(i,p),comb(nx,p))*sp.Rational(comb(j,q),comb(ny,q))
                  for (p,q),a in terms if p<=i and q<=j)
            out.append(b)
    return out

def interval(path):
    lo=[sp.Rational(0),sp.Rational(0)];hi=[sp.Rational(1),sp.Rational(1)]
    for i,b in enumerate(path):
        axis=i%2;mid=(lo[axis]+hi[axis])/2
        if b=='0':hi[axis]=mid
        elif b=='1':lo[axis]=mid
        else:raise ValueError(path)
    return lo,hi

def whole_tree(paths,prefix=''):
    if prefix in paths:
        assert not any(p!=prefix and p.startswith(prefix) for p in paths)
        return
    assert any(p.startswith(prefix+'0') for p in paths),prefix
    assert any(p.startswith(prefix+'1') for p in paths),prefix
    whole_tree(paths,prefix+'0');whole_tree(paths,prefix+'1')

def check():
    payload=json.loads(Path(__file__).with_name('round14_J_certificate.json').read_text(encoding='utf-8'))
    x,y,B,v,u=sp.symbols('x y B v u')
    h=2-x-3*y+x*y;n=x+y-x*y;R=1-x-2*y+x*y
    Pb=(h-n)**2*(2-4*y*y)-4*y*y*h*h
    yy=B*v
    Pm=(h.subs(y,yy)-n.subs(y,yy))**2*(2*v*(1+B)-(1-v)*(1-B*v))
    Pm-=2*(1-v)*(1-B*v)*h.subs(y,yy)**2
    originals=[R.subs(y,yy),Pb.subs(y,yy),Pm]
    branches={'c':(sp.Rational(2,5)*u,x*x/(1-2*x*x)),
              'm':(sp.Rational(2,5)+sp.Rational(1,40)*u,sp.Rational(4,15)),
              's':(sp.Rational(17,40)+sp.Rational(23,40)*u,(1-x)**2/(6*x-1-x*x))}
    assert set(r['branch'] for r in payload['records'])==set(branches)
    total=0;coeff_count=0;branch_results=[]
    for record in payload['records']:
        name=record['branch'];xx,Y=branches[name];den=sp.denom(Y)
        polys=[]
        for source,reported in zip(originals,record['transformed_polynomials']):
            power=sp.Poly(source,B).degree()
            expr=sp.cancel(source.subs(B,Y)*den**power).subs(x,xx)
            expr=sp.expand(expr)
            assert sp.cancel(expr-sp.sympify(reported))==0
            polys.append(sp.Poly(expr,u,v))
        paths={r['path'] for r in record['leaves']}
        assert len(paths)==len(record['leaves']);whole_tree(paths)
        area=Fraction(0)
        for leaf in record['leaves']:
            lo,hi=interval(leaf['path'])
            area+=Fraction(hi[0]-lo[0])*Fraction(hi[1]-lo[1])
            chosen=leaf['chosen'];assert chosen in [1,2]
            for index,key in [(0,'min_R'),(chosen,'min_P')]:
                expr=polys[index].as_expr().subs(
                    {u:lo[0]+(hi[0]-lo[0])*u,v:lo[1]+(hi[1]-lo[1])*v},simultaneous=True)
                pp=sp.Poly(sp.expand(expr),u,v)
                coefficients=bernstein_coefficients(pp)
                assert min(coefficients)>=0
                assert min(coefficients)==sp.Rational(leaf[key])
                coeff_count+=len(coefficients)
            total+=1
        assert area==1
        branch_results.append({'branch':name,'rectangles':len(paths),'area':str(area)})
    # Linear-in-N endpoint identities behind the choice of the two caps.
    N=sp.symbols('N');Z=n/h
    G=(1-Z)**2*(3-N)-2*(N-1)
    by=(1+y*y)/(1-y*y)
    assert sp.cancel(G.subs(N,by)*h*h*(1-y*y)-Pb)==0
    e=(B-y)*(1-y);f=y*(1+B)
    cap=1+e/f
    reduced=sp.cancel((G.subs(N,cap)*h*h*f).subs(y,B*v)/B)
    assert sp.cancel(reduced-Pm)==0
    # For z<=Z<1, (1-z)^2 >= (1-Z)^2.
    z=sp.symbols('z')
    assert sp.factor((1-z)**2-(1-Z)**2-(Z-z)*(2-z-Z))==0
    result={'result':'passed','rectangles':total,'rational_coefficients':coeff_count,
            'branches':branch_results,'identities':'both N caps and z monotonicity verified'}
    Path(__file__).with_name('round14_J_certificate_checks.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result),flush=True)
    return result

if __name__=='__main__':check()
