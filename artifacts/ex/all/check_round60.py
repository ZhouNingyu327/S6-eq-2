"""Independent reconstruction from explicit LEFT coordinates and side lengths."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 src=Path(__file__).resolve().parent
 records=json.loads((src/'round60_certificate.json').read_text(encoding='utf-8'))
 a,z,h,u,v,S,E,H,mu,d,Sigma=s.symbols('a z h u v S E H mu d Sigma')
 b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t)
 g=lambda t:(1-t)/(1+t);q=lambda t:t/(2-t)
 # Closed coordinate formulas, independent of the generator's support-line solver.
 X=(1-z)*(a*a*(1+2*z)-z)/((a-z)*(1+a*z))
 e=2*a*z*(1-a-z)/((a-z)*(1+a*z))
 F=lambda t:(1+t*t-2*t*(1+3*z)/(1+z))/(1-t*t)
 Dz=2*z*z/(1-z*z)
 ML=R(50,119)+X-R(120,119)*e+Dz
 MM=R(18,91)+X-R(16,63)*e+Dz
 A=1-h-z*(1-h*h)/(2*h)
 MA=(1-h)/(1+h)+2*h*z/(1-h*h)+Dz
 HF=2-1/(1-2*h*h/(1-h*h)-z)
 targets=[
  ('large_z',R(7,12)-F(a)-q(ML),a,R(1,3),R(1,2),z,R(3,20),R(4,15)),
  ('high_h_small_z',R(7,12)-F(A)-q(MA),h,R(3,10),R(5,12),z,R(0),R(3,20)),
  ('middle_z',R(7,12)-F(a)-q(MM),a,R(2,7),R(3,5),z,R(1,10),R(3,20)),
  ('low_h_small_z',HF-F(A)-q(MA),h,R(1,8),R(3,10),z,R(0),R(1,10))]
 denominators={};count=0
 for j,(label,target,pvar,lo,hi,qvar,bot,top) in enumerate(targets):
  polys=[]
  for offset,kind in enumerate(['numerator','denominator']):
   rec=records[2*j+offset]
   assert rec['name']==label and rec['kind']==kind
   assert rec['variables']==[str(pvar),str(qvar)]
   assert rec['box']==[[str(lo),str(hi)],[str(bot),str(top)]]
   poly=s.sympify(rec['polynomial'],locals={'a':a,'z':z,'h':h})
   p=s.Poly(s.expand(poly.subs({pvar:lo+(hi-lo)*u,qvar:bot+(top-bot)*v})),u,v)
   n,m=rec['degree'];assert (p.degree(u),p.degree(v))==(n,m)
   cc=[[R(c) for c in row] for row in rec['coefficients']]
   assert len(cc)==n+1 and all(len(row)==m+1 for row in cc)
   assert all(c>0 for row in cc for c in row)
   rebuilt=s.expand(sum((cc[ii][jj]*comb(n,ii)*comb(m,jj)*u**ii*(1-u)**(n-ii)*v**jj*(1-v)**(m-jj)
    for ii in range(n+1) for jj in range(m+1)),s.Integer(0)))
   assert s.Poly(rebuilt,u,v)==p,(label,kind)
   polys.append(poly);count+=(n+1)*(m+1)
  assert s.cancel(target*polys[1]-polys[0])==0,label
  denominators[label]=polys[1]
 assert len(records)==8 and count==362
 XS=(b(a)+S-2)/(k(a)-k(z));eS=1-S-k(z)*XS
 Fsupport=b(a)-k(a)*(2-g(z))
 C=(1-h*h)/(1+h*h);ss=2*h/(1+h*h);delta=b(h)-1
 positive_factor=(a-z)*(1-a*a)*(1-z)*(1+z)**2*(1+a*z)
 identities={
  'X_G coordinate':XS.subs(S,g(z))-X,
  'e_G coordinate':eS.subs(S,g(z))-e,
  'support short-leg formula':Fsupport-F(a),
  'S4 derivative of right-root bound':s.diff(XS-k(h)*eS,S)-k(h)-(1+k(h)*k(z))/(k(a)-k(z)),
  'e derivative':s.diff(eS,S)+k(a)/(k(a)-k(z)),
  'F a derivative':s.diff(Fsupport,a)-(4*a-2*(2-g(z))*(1+a*a))/(1-a*a)**2,
  'F z derivative':s.diff(Fsupport,z)+2*k(a)/(1+z)**2,
  'negative LT alpha':(1-z+k(h)*(1-A))-b(h),
  'negative RT upper':b(h)-k(h)*(1-z)-(g(h)+k(h)*z),
  'normal unit circle':C*C+ss*ss-1,
  'delta ratio':delta-h*k(h),
  'comparison factor':(b(H)-1-k(H)*E)-(b(h)-1-k(h)*E)
   -2*(H-h)*(H+h-E*(1+H*h))/((1-H*H)*(1-h*h)),
  'comparison bracket positivity':H+h-H*(1+H*h)-h*(1-H*H),
  'large denominator branch':denominators['large_z']-1428*positive_factor*(2-ML),
  'middle denominator branch':denominators['middle_z']-9828*positive_factor*(2-MM),
  'q threshold':q(R(14,19))-R(7,12),
  'area rearrangement':(2*mu-Sigma)*(mu-d)-1-(mu-d)*(2*mu-1/(mu-d)-Sigma),
  'area mu derivative':s.diff(2*mu-1/(mu-d),mu)-2-1/(mu-d)**2,
  'area depth derivative':s.diff(2-1/(1-d),d)+1/(1-d)**2,
  'large a upper endpoint':Fsupport.subs({a:R(1,2),z:R(3,20)})+R(1,69),
  'middle a upper endpoint':Fsupport.subs({a:R(3,5),z:R(1,10)})+R(1,11)}
 for name,expr in identities.items():assert s.cancel(expr)==0,name
 constants={
  'corner chord diameter':R(17,12)**2-2,
  'angle cap':R(17,12)**2-2,
  'large a lower gap':R(29,23)-R(5,4),
  'middle a lower gap':R(13,11)-R(53,45),
  'large negative F':R(1,69),
  'middle negative F':R(1,11),
  'high alpha lower':1-R(5,12)-R(3,20)/k(R(3,10)),
  'low alpha lower':1-R(3,10)-R(1,10)/k(R(1,8)),
  'axis right parameter margin':1-g(R(1,8))-k(R(5,12))*R(3,20)-(b(R(3,20))-1),
  'low area height margin':1-(b(R(3,10))-1)-R(1,10),
  'q threshold margin':1-R(14,19),
  'large a-z margin':R(1,3)-R(4,15),
  'middle a-z margin':R(2,7)-R(3,20),
  'large 1-a2 margin':1-R(1,2)**2,
  'middle 1-a2 margin':1-R(3,5)**2,
  'h unit denominator margin':1-R(5,12)**2}
 assert all(val>0 for val in constants.values())
 assert constants['high alpha lower']==R(427,1200)
 assert constants['low alpha lower']==R(49,160)
 assert b(R(5,12))-1==R(50,119) and k(R(5,12))==R(120,119)
 assert b(R(3,10))-1==R(18,91) and k(R(1,8))==R(16,63)
 # Two logically different uses of the same rational comparison are counted once.
 assert constants.pop('angle cap')==constants['corner chord diameter']
 result={'result':'passed','new_rational_inequalities':4,'new_polynomial_reconstructions':8,
  'new_positive_coefficients':count,'algebraic_identities':len(identities),
  'positive_exact_constants':len(constants),'UNSAT':0,
  'new_theorem':'All negative-C rotations excluded in both remaining mechanisms',
  'remaining_mechanisms':'positive-C general double-direct with W not containing QU; positive-C right-W bridge I/II',
  'not_proved':'entire G2 or S(6)=2','global_bound':'2 <= S(6) < 2.03'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
