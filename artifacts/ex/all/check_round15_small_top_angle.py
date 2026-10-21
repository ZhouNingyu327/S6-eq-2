"""Exact audit: near three-meet F-horizontal-empty implies t3>1/32."""
from pathlib import Path
from math import comb
import json,time
import sympy as s
import z3

ROOT=Path(__file__).resolve().parent
h,u=s.symbols('h u')
U=s.Rational(31,32);K=s.Rational(1,1022)
M=(1-U+(1+U)*h*h)/(2*h)
R=(1+h*h-2*h*U)/(1-h*h)
g=2-R/(2-R)-M/(2-M)-K
vf=U-2*h*h/(1-h*h)

certificates=[]
for name,expression,a,b in [
    ('either_C_small_h_area',g*vf-1,s.Rational(1,8),s.Rational(17,50)),
    ('either_C_large_h_chord',g-s.Rational(99,70),s.Rational(17,50),s.Rational(5,12)),
]:
    numerator,denominator=s.together(expression).as_numer_denom()
    numerator=s.expand(numerator)
    transformed=s.Poly(numerator.subs(h,a+(b-a)*u),u)
    degree=transformed.degree()
    bs=[sum(transformed.nth(j)*s.Rational(comb(i,j),comb(degree,j))
            for j in range(i+1)) for i in range(degree+1)]
    assert all(value>0 for value in bs)
    rebuilt=sum(value*comb(degree,i)*u**i*(1-u)**(degree-i)
                for i,value in enumerate(bs))
    assert s.expand(rebuilt-transformed.as_expr())==0
    certificates.append({'name':name,'interval':[str(a),str(b)],
                         'numerator':str(numerator),'denominator':str(denominator),
                         'coefficients':list(map(str,bs)),'strictly_positive':True})

# The two quadratic factors are strictly negative throughout [1/8,5/12].
factors=[48*h*h-31*h-16,63*h*h-128*h+1]
for factor in factors:
    assert s.diff(factor,h,2)>0
    assert all(factor.subs(h,a)<0 for a in [s.Rational(1,8),s.Rational(5,12)])
assert s.factor(s.diff(M,h,2))==1/(32*h**3)
assert all(M.subs(h,a)<s.Rational(9,20)
           for a in [s.Rational(1,8),s.Rational(5,12)])
assert 1-s.Rational(9,31)-K>0
assert U-s.Rational(50,119)>0
assert s.Rational(99,70)**2>2
assert s.Rational(33,1993)>s.Rational(1,64)
assert s.Rational(5,12)+1>s.sqrt(2)
x=s.symbols('x')
Ys=(1-x)**2/(6*x-1-x*x)
assert s.cancel(s.diff(Ys,x)-4*(x-1)*(x+1)/(6*x-1-x*x)**2)==0
assert Ys.subs(x,s.Rational(5,7))==s.Rational(1,34)<s.Rational(1,32)

queries=[]
for sign in [1,-1]:
    hh,rr,zz,gg,vv=z3.Reals('h r z g v')
    p=z3.SolverFor('QF_NRA');p.set(timeout=45000)
    UU=z3.RealVal('31/32');KK=z3.RealVal('1/1022')
    mm=(1-UU+(1+UU)*hh*hh)/(2*hh)
    rr_cap=(1+hh*hh-2*hh*UU)/(1-hh*hh)
    rcap=mm if sign==1 else rr_cap
    lcap=rr_cap if sign==1 else mm
    p.add(hh>=z3.RealVal('1/8'),hh<=z3.RealVal('5/12'),
          rr>=0,rr<1,rr<=rcap,zz>0,zz<1,2*zz<=lcap*(1+zz),
          gg>2-zz-KK-rr/(2-rr),vv>UU-2*hh*hh/(1-hh*hh),
          gg*gg<=2,gg*vv<=1)
    start=time.time();ans=p.check()
    row={'C_sign':sign,'result':str(ans),'seconds':time.time()-start}
    if ans==z3.unknown:row['reason']=p.reason_unknown()
    if ans==z3.sat:row['model']=str(p.model())
    queries.append(row);print(row,flush=True)
    assert ans==z3.unsat,row

data={'classification':'exact rational coefficient and NRA audit',
      'proved_scope':'near three-meet F horizontal empty: t3>1/32',
      'certificates':certificates,'coefficient_count':12,
      'angle_corollary':'t2<5/7, by decreasing sine cap Ys(5/7)=1/34<1/32',
      'queries':queries,'unsat_count':2,'passed':True}
(ROOT/'round15_small_top_checks.json').write_text(json.dumps(data,indent=2),encoding='utf-8')
