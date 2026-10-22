"""Independent inverse reconstruction of five explicit rational axis-area targets."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 src=Path(__file__).resolve().parent;recs=json.loads((src/'round59_certificate.json').read_text(encoding='utf-8'))
 x,t,d,h,a,mu,D,Sigma,u=s.symbols('x t d h a mu D Sigma u')
 b=lambda z:(1+z*z)/(1-z*z);k=lambda z:2*z/(1-z*z)
 g=lambda z:(1-z)/(1+z);q=lambda z:z/(2-z);j=lambda z:2*z/(1+z)
 Bt=(3*t**4-6*t**3-4*t*t+2*t+1)/(1-t*t)**2
 # Use b(x)-k(x)Bt instead of the generator's g(x)-k(x)(Bt-1).
 residual=2-1/(1-d-t)-q(x+d)-b(x)+k(x)*Bt
 tc=2*x*x/(1-x*x)
 targets=[
  ('small_zero',residual.subs({d:81*x*x/70,t:0})/x,R(0),R(1,6),
   (x+1)*(81*x*x-70)*(81*x*x+70*x-140)),
  ('small_cos_cap',residual.subs({d:81*x*x/70,t:tc})/x,R(0),R(1,6),
   (x-1)*(x+1)*(x*x+1)**2*(3*x*x-10)*(3*x*x-1)**2*(27*x*x-7)*(81*x*x+70*x-140)),
  ('middle_zero',residual.subs({d:R(2,35),t:0}),R(1,6),R(3,4),
   -33*(x+1)*(35*x-68)),
  ('middle_cos_cap',residual.subs({d:R(2,35),t:tc}),R(1,6),R(1,4),
   -(x-1)*(x+1)*(35*x-68)*(x*x+1)**2*(3*x*x-1)**2*(103*x*x-33)),
  ('middle_tau_cap',residual.subs({d:R(2,35),t:R(1,6)}),R(1,4),R(3,4),
   199675*(x-1)*(x+1)*(35*x-68))]
 total=0
 for rec,(name,expr,lo,hi,den) in zip(recs,targets):
  assert rec['name']==name and rec['interval']==[str(lo),str(hi)]
  assert s.expand(s.sympify(rec['positive_denominator'],locals={'x':x})-den)==0,name
  num=s.cancel(expr*den);assert s.denom(num)==1,name
  pp=s.Poly(s.expand(num.subs(x,lo+(hi-lo)*u)),u);n=rec['degree'];assert pp.degree()==n
  cc=[R(v) for v in rec['coefficients']];assert len(cc)==n+1 and all(v>0 for v in cc)
  rebuilt=s.expand(sum((cc[i]*comb(n,i)*u**i*(1-u)**(n-i) for i in range(n+1)),s.Integer(0)))
  assert s.Poly(rebuilt,u)==pp,name;total+=len(cc)
 assert len(recs)==len(targets)==5 and total==42
 delta=b(h)-1;f=h+(1-h*h)/(48*h)
 G=2-1/(1-d-t)-q(x+d)-g(x)+k(x)*(Bt-1)
 C=(1-h*h)/(1+h*h);ss=2*h/(1+h*h)
 identities={
  'B explicit':Bt-(1+k(t)*(1-(b(t)-1)-t)),
  'B second derivative':s.diff(Bt,t,2)+4*(3*t**5-3*t**4+18*t**3+2*t*t+3*t+1)/(1-t*t)**4,
  'G delta derivative':s.diff(G,d)+1/(1-d-t)**2+2/(2-x-d)**2,
  'G tau concavity':s.diff(G,t,2)+2/(1-d-t)**3-k(x)*s.diff(Bt,t,2),
  'F area rearrangement':(2*mu-Sigma)*(mu-D)-1-(mu-D)*(2*mu-1/(mu-D)-Sigma),
  'F mu monotonicity':s.diff(2*mu-1/(mu-D),mu)-2-1/(mu-D)**2,
  'horizontal inverse':g(1-d-x)-q(x+d),
  'long leg reform':b(x)-k(x)*Bt-g(x)+k(x)*(Bt-1),
  'delta ratio':delta-h*k(h),
  'small x quadratic':2*(3*x/4)**2*R(36,35)-R(81,70)*x*x,
  'left endpoint inverse':j(g(a))-(1-a),
  'far x f convexity':s.diff(f,h,2)-1/(24*h**3),
  'sin cap decreasing':s.diff((1-x)**2/(2*x),x)-(R(1,2)-1/(2*x*x)),
  'normal unit circle':C*C+ss*ss-1}
 for name,expr in identities.items():assert s.cancel(expr)==0,name
 constants={
  'vertical_height_margin':1-R(2,35)-R(1,6),
  'small_height_margin':1-R(81,70)*R(1,6)**2-R(2,35),
  'middle_cos_height_margin':1-R(2,35)-R(2,15),
  'q_domain_margin':2-R(3,4)-R(2,35),
  'B_second_sign':1-3*R(1,6)**4,
  'far_height_margin':1-R(2,35)-R(1,24),
  'far_short_leg_requirement':R(674,757)-R(1,7),
  'far_left_gap':R(3961,4630)-R(623,1152),
  'far_endpoint_order':f.subs(h,R(1,24))-f.subs(h,R(1,6)),
  'small_q_factor_margin':140-81*R(1,6)**2-70*R(1,6),
  'small_factor_27':7-27*R(1,6)**2,
  'middle_factor_103':33-103*R(1,4)**2}
 assert all(val>0 for val in constants.values())
 assert f.subs(h,R(1,24))==R(623,1152) and f.subs(h,R(1,6))==R(83,288)
 assert j(R(674,757)-R(1,7))==R(3961,4630)
 result={'result':'passed','new_polynomial_reconstructions':5,'new_positive_coefficients':42,
  'algebraic_identities':len(identities),'positive_exact_constants':len(constants),'UNSAT':0,
  'new_theorem':'All remaining negative W-contains-QU cases excluded; with round55 the entire upper-W mechanism is closed',
  'remaining_mechanisms':'general double direct with W not containing QU; right-W bridge I/II',
  'not_proved':'entire G2 or S(6)=2','global_bound':'2 <= S(6) < 2.03'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
