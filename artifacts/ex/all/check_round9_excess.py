"""Two central-excess bounds: rational polynomial certificates plus independent NLSAT."""
from pathlib import Path
from math import comb
import json,time
import sympy as sp
import z3

def certificates():
    t,L,z=sp.symbols('t L z')
    S=(1+t*t-2*t*L)/(1-t*t)
    D=2-L-S-t;k=(L-1)/(3-L);b=1-k
    P=b*b*D*(D+4)-(D+2*t)**2
    Lc=(1+t*t)/(1-t*t);Ls=(5+19*t*t)/(24*t)
    definitions=[
        ('left_D_ge_t/2',D.subs(L,Lc)-t/2,sp.Rational(0),sp.Rational(16,193),2*(1-t*t)**2),
        ('top_cos_D_positive',D.subs(L,Lc),sp.Rational(0),sp.Rational(9,40),(1-t*t)**2),
        ('top_cos_P_nonnegative',P.subs(L,Lc),sp.Rational(0),sp.Rational(9,40),(1-t*t)**4*(1-2*t*t)**2),
        ('top_short_D_positive',D.subs(L,Ls),sp.Rational(9,40),sp.Rational(5,19),24*t),
        ('top_short_P_nonnegative',P.subs(L,Ls),sp.Rational(9,40),sp.Rational(5,19),192*t*t*(19*t*t-72*t+5)**2),
    ]
    records=[]
    for name,expr,a,end,den in definitions:
        num=sp.cancel(expr*den)
        assert sp.cancel(expr-num/den)==0
        poly=sp.Poly(num,t);n=poly.degree()
        shifted=sp.Poly(poly.as_expr().subs(t,a+(end-a)*z),z)
        coeff=[sum(shifted.nth(j)*sp.binomial(i,j)/sp.binomial(n,j) for j in range(i+1))
               for i in range(n+1)]
        assert all(v>=0 for v in coeff),(name,coeff)
        reconstructed=sum(coeff[i]*sp.binomial(n,i)*z**i*(1-z)**(n-i) for i in range(n+1))
        assert sp.expand(reconstructed-shifted.as_expr())==0
        if a==0:assert coeff[0]==0 and all(v>0 for v in coeff[1:])
        else:assert all(v>0 for v in coeff)
        records.append({'scope':name,'interval':[str(a),str(end)],'numerator':str(poly.as_expr()),
                        'positive_denominator':str(den),'degree':n,
                        'exact_bernstein_coefficients':[str(v) for v in coeff],
                        'status':'exact rational certificate and reconstruction identity passed'})
    # Rational constants used in the calibration/monotonicity proof.
    assert sp.Rational(242,225)>sp.Rational(144,193)
    assert sp.Rational(26,15)-sp.Rational(16,193)>sp.Rational(17,12)
    assert sp.Rational(17,12)**2>2
    assert sp.Rational(11,15)+sp.Rational(11,12)>sp.Rational(17,12)
    assert sp.Rational(16,193)<sp.Rational(1,12)
    assert 4*sp.Rational(121,144)-4*sp.Rational(4,15)-2*sp.Rational(23,144)*sp.Rational(4,15)>0
    assert sp.Rational(9,40)<sp.Rational(5,19)<sp.Rational(4,15)
    assert sp.simplify(D.subs(L,1)-t*(1-t)/(1+t))==0
    assert sp.simplify(sp.diff(D,L)-(-1+2*t/(1-t*t)))==0
    assert sp.simplify(sp.diff(b,L)+2/(3-L)**2)==0
    return records

def query(case):
    t,L,S,k,p,q=z3.Reals('t L S k p q');sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    sol.add(t>0,L>=1,p>=q,q>=0,p*p+q*q==1,L*(1-t*t)<=1+t*t,2*t*L<=1+t*t,
            S>=0,S*(1-t*t)==1+t*t-2*t*L)
    if case=='top_anchor':
        sol.add(t<z3.RealVal('4/15'),S>=z3.RealVal('7/12'),k>=0,k*(3-L)==L-1,
                p*(1-t)+q*(1-k)<=1)
    else:
        sol.add(t<=z3.RealVal('16/193'),p*(1-t)+q*z3.RealVal('11/15')<=1)
    sol.add(2-2*p>p*(2-L-S-t))
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':case+': 2/p-2 <= 2-L-S-t','result':str(res),
            'arithmetic':'exact nonlinear reals','seconds':time.time()-start}

if __name__=='__main__':
    certs=certificates();print('PASS 5 exact rational Bernstein certificates',flush=True)
    queries=[query('left_anchor'),query('top_anchor')]
    for row in queries:print('PASS',row,flush=True)
    Path(__file__).with_name('round9_excess_checks.json').write_text(
        json.dumps({'queries':queries,'rational_certificates':certs},indent=2),encoding='utf-8')
