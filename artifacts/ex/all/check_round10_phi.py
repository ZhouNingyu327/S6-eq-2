"""Independent rational certificates for the calibrated adjacent-meet envelope."""
from pathlib import Path
import json
import sympy as sp


def certificates():
    t,k,h,z,v=sp.symbols('t k h z v')
    L=(1+3*k)/(1+k)
    S=(1+t*t-2*t*L)/(1-t*t)
    B=k/(2-k)+k*k/(2*(1-k))
    w=k*k/(1-2*k*k)
    phi=t*(1-t)/(1+t)+4*t*k/((1-t*t)*(1+k))-k-B-w
    assert sp.cancel(1+B+S+t+k+w-(2-phi))==0
    curvature=-8*t/((1-t*t)*(1+k)**3)-4/(2-k)**3-1/(1-k)**3-2*(1+6*k*k)/(1-2*k*k)**3
    assert sp.cancel(sp.diff(phi,k,2)-curvature)==0

    Kc=t*t/(1-2*t*t)
    Ds=-t*t+6*t-1
    Ks=(1-t)**2/Ds
    den_c=2*(1-t*t)**2*(1-2*t*t)*(1-3*t*t)*(2-5*t*t)*(1-4*t*t+2*t**4)
    den_s=4*Ds*(-t*t+4*t-1)*(-3*t*t+14*t-3)*(Ds**2-2*(1-t)**4)
    rows=[]
    for name,K,a,b,den in [
        ('cosine_cap',Kc,sp.Rational(0),sp.Rational(5,12),den_c),
        ('sine_cap',Ks,sp.Rational(5,12),sp.Rational(1),den_s),
    ]:
        expr=sp.cancel(phi.subs(k,K))
        num=sp.cancel(expr*den)
        poly=sp.Poly(num,t)
        assert sp.cancel(expr-poly.as_expr()/den)==0
        n=poly.degree()
        shifted=sp.Poly(poly.as_expr().subs(t,a+(b-a)*v),v)
        coeff=[sum(shifted.nth(j)*sp.binomial(i,j)/sp.binomial(n,j) for j in range(i+1))
               for i in range(n+1)]
        reconstructed=sum(coeff[i]*sp.binomial(n,i)*v**i*(1-v)**(n-i) for i in range(n+1))
        assert sp.expand(reconstructed-shifted.as_expr())==0
        assert all(x>=0 for x in coeff)
        if name=='cosine_cap':
            assert coeff[0]==0 and all(x>0 for x in coeff[1:])
        else:
            assert coeff[-1]==0 and all(x>0 for x in coeff[:-1])
        rows.append({'scope':name+': Phi(t,K(t)) > 0 in the open physical interval',
                     'interval':[str(a),str(b)],'numerator':str(poly.as_expr()),
                     'positive_denominator':str(sp.expand(den)),
                     'degree':n,'exact_bernstein_coefficients':[str(x) for x in coeff],
                     'status':'exact rational certificate and reconstruction identity passed'})

    # Positive denominators and cap bounds, checked with exact constants.
    a=sp.Rational(5,12)
    assert Kc.subs(t,a)==sp.Rational(25,94)<sp.Rational(4,15)
    assert Ks.subs(t,a)==sp.Rational(49,191)<sp.Rational(4,15)
    for factor in [1-t*t,1-2*t*t,1-3*t*t,2-5*t*t,1-4*t*t]:
        assert factor.subs(t,a)>0
    for factor in [Ds,-t*t+4*t-1,-3*t*t+14*t-3]:
        assert factor.subs(t,a)>0
        assert sp.diff(factor,t).subs(t,1)>0
    assert 1-2*sp.Rational(4,15)**2>0
    assert sp.cancel(sp.diff(Ks,t)+4*(1-t*t)/Ds**2)==0

    # Half-angle calibration: convexity proof, independent of the NRA query.
    H=(k-(2-k)*z)/(2-k+(4-k)*z)
    f=(1+h*h)/(1-h*h)+h
    E=4*z*z/(1-z*z)
    denH=2-k+(4-k)*z
    assert sp.cancel(sp.diff(H,z)+4/denH**2)==0
    assert sp.cancel(sp.diff(H,z,2)-8*(4-k)/denH**3)==0
    assert sp.cancel(sp.diff(f,h)-(1+4*h/(1-h*h)**2))==0
    assert sp.cancel(sp.diff(f,h,2)-4*(1+3*h*h)/(1-h*h)**3)==0
    assert sp.cancel(sp.diff(E,z,2)-8*(1+3*z*z)/(1-z*z)**3)==0
    zmax=k/(2-k)
    J=f.subs(h,H)+E
    assert sp.cancel(J.subs(z,0)-(1+B))==0
    assert sp.cancel(J.subs(z,zmax)-(1+k*k/(1-k)))==0
    endpoint_difference=k*(2-4*k+k*k)/(2*(1-k)*(2-k))
    assert sp.cancel((1+B)-(1+k*k/(1-k))-endpoint_difference)==0
    assert (2-4*k+k*k).subs(k,sp.Rational(4,15))>0
    # The orientation substitution and the solved projection inequality.
    p=(1-z*z)/(1+z*z);q=2*z/(1+z*z)
    assert sp.cancel(p*p+q*q-1)==0
    assert sp.cancel((1-q)/p-(1-z)/(1+z))==0
    delta=k-2*z/(1+z)
    assert sp.cancel(delta/(2-delta)-H)==0
    assert sp.Rational(26,15)**2>2
    assert sp.Rational(22,15)**2>2
    return rows


if __name__=='__main__':
    rows=certificates()
    for row in rows:
        print('PASS',row['scope'],'degree',row['degree'],flush=True)
    Path(__file__).with_name('round10_phi_checks.json').write_text(
        json.dumps({'rational_certificates':rows,
                    'symbolic_identities':'Phi curvature, calibration convexity, substitutions, endpoints, positive denominators passed'},
                   indent=2),encoding='utf-8')
