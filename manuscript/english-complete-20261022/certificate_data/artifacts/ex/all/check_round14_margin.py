"""Rational proof certificate: Phi>kappa^2/3 and the near left-gap closure."""
from pathlib import Path
from math import comb
import json,time
import sympy as sp
import z3

def solve(name,p):
    p.set(timeout=30000);start=time.time();answer=p.check()
    row={'scope':name,'result':str(answer),'seconds':time.time()-start}
    assert answer==z3.unsat,row
    return row

def symbolic():
    t,k=sp.symbols('t k');u=sp.symbols('u')
    psi=t*(1-t)/(1+t)+4*t*k/((1-t*t)*(1+k))-2*k-k*k/2
    phi=t*(1-t)/(1+t)+4*t*k/((1-t*t)*(1+k))-2*k-2*k**4/(1-2*k*k)
    delta=k*k*(1-14*k*k)/(6*(1-2*k*k))
    assert sp.cancel(phi-k*k/3-psi-delta)==0
    assert sp.cancel(sp.diff(psi,k,2)+8*t/((1-t*t)*(1+k)**3)+1)==0
    P=8*t**8-23*t**7-40*t**6+50*t**5+26*t**4-35*t**3+8*t-2
    Q=2*t**4-27*t**3+101*t*t-49*t+5
    assert sp.cancel(psi.subs(k,t*t/(1-2*t*t))+t*P/(2*(1-t*t)**2*(1-2*t*t)**2))==0
    assert sp.cancel(psi.subs(k,(1-t)**2/(6*t-1-t*t))-(1-t)*Q/(2*(t*t-6*t+1)**2))==0
    poly=sp.Poly(-P.subs(t,sp.Rational(5,12)*u),u)
    coeff=[sum(poly.nth(j)*sp.Rational(comb(i,j),comb(8,j)) for j in range(i+1)) for i in range(9)]
    assert all(b>0 for b in coeff)
    assert sp.expand(sum(b*comb(8,i)*u**i*(1-u)**(8-i) for i,b in enumerate(coeff))-poly.as_expr())==0
    assert sp.expand(sp.diff(Q,t,3)-(48*t-162))==0
    assert sp.diff(Q,t,2).subs(t,1)==64
    assert Q.subs(t,sp.Rational(5,12))==sp.Rational(2335,10368)
    assert sp.diff(Q,t).subs(t,sp.Rational(5,12))==sp.Rational(9367,432)
    w=k*k/(1-2*k*k)
    theta=2*w*w/(1-3*w*w)
    assert sp.cancel(k*k/3-theta-k*k*(1-10*k*k+k**4)/(3*(1-4*k*k+k**4)))==0
    assert (1-10*k*k+k**4).subs(k,sp.Rational(4,15))==sp.Rational(14881,50625)
    return {'scope':'strengthened Phi proof identities and complete positive polynomial certificates',
            'result':'exact identities passed','Bernstein_coefficients':[str(b) for b in coeff],
            'P':str(P),'Q':str(Q)}

def P_check():
    t=z3.Real('t');P=8*t**8-23*t**7-40*t**6+50*t**5+26*t**4-35*t**3+8*t-2
    p=z3.SolverFor('QF_NRA');p.add(t>=0,t<=z3.RealVal('5/12'),P>=0)
    return solve('new P(t)<0 on entire [0,5/12]',p)

def Q_check():
    t=z3.Real('t');Q=2*t**4-27*t**3+101*t*t-49*t+5
    p=z3.SolverFor('QF_NRA');p.add(t>=z3.RealVal('5/12'),t<=1,Q<=0)
    return solve('new Q(t)>0 on entire [5/12,1]',p)

def margin_check():
    k,w=z3.Reals('k w')
    p=z3.SolverFor('QF_NRA');p.add(k>0,k<z3.RealVal('4/15'),
        w*(1-2*k*k)==k*k,z3.Or(1-3*w*w<=0,
        k*k*(1-3*w*w)<=6*w*w))
    return solve('kappa^2/3 > 2w^2/(1-3w^2)',p)

def H_margin():
    mu,x,k,w,S,H,l,r,u=z3.Reals('mu x k w S H l r u')
    p=z3.SolverFor('QF_NRA')
    phi=1-S-x-2*k+k*k-w
    p.add(mu>1,x>0,x<1,k>0,k<z3.RealVal('4/15'),w>=0,S>=0,
          l>1-w-H,r>1-x,u>1-k,l+r+u*u<=2,H-S<=phi)
    return solve('C three-axis parabola forces H-S2>Phi',p)

def triangle_closure():
    phi,w,delta,g,height=z3.Reals('phi w delta g height')
    p=z3.SolverFor('QF_NRA')
    p.add(w>=0,3*w*w<1,delta*(1-w*w)==2*w*w,
          phi*(1-3*w*w)>2*w*w,g>1+phi,height>1-delta,g*height<=1)
    return solve('F triangle violates unit-square maximum area in left-gap branch',p)

if __name__=='__main__':
    rows=[]
    for f in [symbolic,P_check,Q_check,margin_check,H_margin,triangle_closure]:
        row=f();rows.append(row);print('PASS',row,flush=True)
    Path(__file__).with_name('round14_margin_checks.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
