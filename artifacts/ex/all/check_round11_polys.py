"""Rational certificates and identities for the G2 far-corner angle reduction."""
from pathlib import Path
import json
import sympy as sp


def certificates():
    u,t,z,h=sp.symbols('u t z h')
    T=u/(4-3*u)
    r=(19*u-5)/(12*(1+u))
    m=(-19*u*u+48*u-5)/(24*u)
    cap=(u+(4-3*u)*t*t)/(2*t*(2-u))
    definitions=[
        ('small_end_band',m-(1+T*T)/(1-T*T),sp.Rational(1,3),sp.Rational(2,5),
         24*u*(2-u)*(1-u)),
        ('large_end_band',m-cap.subs(t,r),sp.Rational(3,4),sp.Rational(7,8),
         24*u*(2-u)*(1+u)*(19*u-5)),
    ]
    records=[]
    for name,expr,a,b,den in definitions:
        numerator=sp.cancel(expr*den)
        poly=sp.Poly(numerator,u)
        assert sp.cancel(expr-poly.as_expr()/den)==0
        n=poly.degree();shifted=sp.Poly(poly.as_expr().subs(u,a+(b-a)*z),z)
        coeff=[sum(shifted.nth(j)*sp.binomial(i,j)/sp.binomial(n,j) for j in range(i+1))
               for i in range(n+1)]
        assert all(v>0 for v in coeff)
        rebuilt=sum(coeff[i]*sp.binomial(n,i)*z**i*(1-z)**(n-i) for i in range(n+1))
        assert sp.expand(rebuilt-shifted.as_expr())==0
        records.append({'scope':name,'interval':[str(a),str(b)],'numerator':str(poly.as_expr()),
                        'positive_denominator':str(den),'degree':n,
                        'exact_bernstein_coefficients':[str(v) for v in coeff],
                        'status':'exact rational coefficients strictly positive; reconstruction passed'})

    R=-69*u*u+79*u-20
    assert sp.cancel(r-T-R/(12*(1+u)*(4-3*u)))==0
    assert R.subs(u,sp.Rational(2,5))==sp.Rational(14,25)>0
    assert R.subs(u,sp.Rational(3,4))==sp.Rational(7,16)>0
    assert sp.diff(R,u,2)==-138
    assert sp.cancel(sp.diff(cap,t)-((4-3*u)-u/t**2)/(2*(2-u)))==0

    # Weak-corner parameterization and the endpoint-to-short-leg calibration.
    c=(1-u*u)/(1+u*u);s=2*u/(1+u*u)
    q=(1-u)/(1+u)
    assert sp.cancel(c*c+s*s-1)==0
    assert sp.cancel((1-c)/s-u)==0
    assert sp.cancel((1-s)/c-q)==0
    Sreq=2*(1-u)/(2-u)
    assert sp.cancel((1+t*t-Sreq*(1-t*t))/(2*t)-cap)==0
    assert sp.cancel(((1-t)/(1+t)-Sreq)*(1+t)*(2-u)-(u-(4-3*u)*t))==0

    # Both-leg normalization of a general weak corner.
    b=sp.symbols('b')
    A=b/s;D=(1-b)/c
    assert sp.cancel(s*A+c*D-1)==0

    # Unit through a vertical chord: positive short legs satisfy a+b+a*b<1.
    v=sp.symbols('v')
    cv=(1-v*v)/(1+v*v);sv=2*v/(1+v*v)
    tv=(1-cv)/sv;qv=(1-sv)/cv
    assert sp.cancel(tv+qv+tv*qv-1)==0
    # Central point exclusion and weak corner point exclusion.
    upper=2*v*v/(1-v*v)+2*v/(1-v*v)/3
    assert sp.cancel(upper.subs(v,u/(2-u))-u*(1+u)/(3*(1-u)))==0
    norm=c*(1-2*u/3)+s*sp.Rational(2,3)-1
    assert sp.cancel(norm-2*u*(1-3*u+u*u)/(3*(1+u*u)))==0
    assert (1-3*u+u*u).subs(u,sp.Rational(1,3))==sp.Rational(1,9)>0
    assert sp.Rational(193,81)>2

    # The general interior-point-to-center lemma, concavity endpoint constants.
    endpoint_square=(sp.Rational(17,15)+4*u*u/3)**2-(1+4*u*u)
    assert sp.expand(endpoint_square-(sp.Rational(64,225)-sp.Rational(44,45)*u*u+sp.Rational(16,9)*u**4))==0
    assert sp.Rational(64,225)-sp.Rational(44,405)>0
    assert sp.Rational(4,5)+sp.Rational(1,3)>1
    assert sp.Rational(2,5)<sp.Rational(7,12)
    assert 2-sp.sqrt(2)>sp.Rational(7,12)
    assert sp.Rational(1,3)/(2-sp.Rational(1,3))==sp.Rational(1,5)
    assert c.subs(u,sp.Rational(7,8))==sp.Rational(15,113)
    assert s.subs(u,sp.Rational(7,8))==sp.Rational(112,113)
    return records


if __name__=='__main__':
    rows=certificates()
    for row in rows:
        print('PASS',row['scope'],'degree',row['degree'],flush=True)
    Path(__file__).with_name('round11_polynomial_checks.json').write_text(
        json.dumps({'rational_certificates':rows,
                    'symbolic_identities':'angle-band reduction, concavity, monotonicity, weak-corner normalization, central witness, forced-center endpoints passed'},
                   indent=2),encoding='utf-8')
