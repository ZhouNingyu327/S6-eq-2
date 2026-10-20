"""Independent complete reconstruction of two angle-eliminated budgets."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 a,z,h,u,v,E,rr,dd,xx,ee=s.symbols('a z h u v E rr dd xx ee')
 b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t)
 g=lambda t:(1-t)/(1+t);q=lambda t:t/(2-t)
 X=(1-z)*(a*a*(1+2*z)-z)/((a-z)*(1+a*z))
 e=2*a*z*(1-a-z)/((a-z)*(1+a*z))
 F=(1+a*a-2*a*(1+3*z)/(1+z))/(1-a*a)
 H=R(91)*a/(140-200*z);delta=2*h*h/(1-h*h);Dz=2*z*z/(1-z*z)
 HF=2-1/(1-delta-z);RT=h+z*(1-h*h)/(2*h)
 RP=delta+X+2*h*e/(1-h*h)
 targets=[('small_a_P1R',(HF-F-q(RP+Dz)).subs(h,H),R(62,315),R(7,20)),
          ('middle_a_RT',(HF-F-q(RT+Dz)).subs(h,H),R(7,20),R(79,200))]
 records=json.loads((Path(__file__).resolve().parent/'round62_certificate.json').read_text(encoding='utf-8'))
 count=0
 for j,(label,target,lo,hi) in enumerate(targets):
  polys=[]
  for off,kind in enumerate(['numerator','denominator']):
   rec=records[2*j+off]
   assert rec['name']==label and rec['kind']==kind and rec['variables']==['a','z']
   assert rec['box']==[[str(lo),str(hi)],['0','1/10']]
   poly=s.sympify(rec['polynomial'],locals={'a':a,'z':z})
   p=s.Poly(s.expand(poly.subs({a:lo+(hi-lo)*u,z:v/10})),u,v)
   n,m=rec['degree'];assert (n,m)==(p.degree(u),p.degree(v))
   cc=[[R(c) for c in row] for row in rec['coefficients']]
   assert len(cc)==n+1 and all(len(row)==m+1 for row in cc)
   assert all(c>0 for row in cc for c in row)
   t=[[comb(n,i)*sum(((-1)**(i-jj)*comb(i,jj)*cc[jj][l] for jj in range(i+1)),R(0)) for l in range(m+1)] for i in range(n+1)]
   coeff=[[comb(m,l)*sum(((-1)**(l-jj)*comb(l,jj)*t[i][jj] for jj in range(l+1)),R(0)) for l in range(m+1)] for i in range(n+1)]
   rebuilt=s.Poly.from_dict({(i,l):coeff[i][l] for i in range(n+1) for l in range(m+1)},(u,v))
   assert rebuilt==p
   polys.append(poly);count+=(n+1)*(m+1)
  assert s.cancel(target*polys[1]-polys[0])==0,label
 assert len(records)==4 and count==338
 A=k(h)*(1-h-z);f=A/h
 c=(1-h*h)/(1+h*h);ss=2*h/(1+h*h);K=k(h)
 ER=c*(1-xx+rr)-ss*ee-1;EB=ss*(1-xx)+c*(ee+dd)-1
 ids={
  'angle lower derivative':s.diff(A,h)-2*((1-h)**2-z*(1+h*h))/(1-h*h)**2,
  'angle ratio derivative':s.diff(f,h)+2*((1-h)**2+2*h*z)/(1-h*h)**2,
  'angle ratio at 3/10':f.subs(h,R(3,10))-(140-200*z)/91,
  'angle eliminated H':H*f.subs(h,R(3,10))-a,
  'delta derivative':s.diff(delta,h)-4*h/(1-h*h)**2,
  'K derivative':s.diff(K,h)-2*(1+h*h)/(1-h*h)**2,
  'RP derivative':s.diff(RP,h)-s.diff(delta,h)-s.diff(K,h)*e,
  'RT convex h':s.diff(RT,h,2)-z/h**3,
  'HF concave h':s.diff(HF,h,2)+s.diff(delta,h,2)/(1-delta-z)**2+2*s.diff(delta,h)**2/(1-delta-z)**3,
  'HF concave z':s.diff(HF,z,2)+2/(1-delta-z)**3,
  'F convex z':s.diff(F,z,2)-4*k(a)/(1+z)**3,
  'M convex z':s.diff(RT+Dz,z,2)-4*(1+3*z*z)/(1-z*z)**3,
  'q first derivative':s.diff(q(E),E)-2/(2-E)**2,
  'q second derivative':s.diff(q(E),E,2)-4/(2-E)**3,
  'coupled P1R P1B':ER+K*EB-c*(rr+K*dd+(1+K*K)*(1-xx)-b(h)*(1+K)),
  'endpoint e relation':e-k(a)*(a-X),
 }
 for name,ex in ids.items():assert s.cancel(ex)==0,name
 Hsmall=R(637,2400);Hmid=R(7189,24000)
 constants={
  'A derivative bracket':R(7,10)**2-R(1,10)*(1+R(3,10)**2),
  'angle lower a':A.subs({h:R(1,8),z:R(1,10)}),
  'small box a-z':R(62,315)-R(1,10),
  'small box 1-a-z':1-R(7,20)-R(1,10),
  'small a slope branch':g(R(3,10))-R(7,20),
  'H minimum above low endpoint':H.subs({a:R(62,315),z:0})-R(1,8),
  'H middle below 3/10':R(3,10)-Hmid,
  'area denominator':1-(b(R(3,10))-1)-R(1,10),
  'small RP M below one':1-(b(Hsmall)-1)-R(7,20)-k(Hsmall)*R(5,12)-(b(R(1,10))-1),
  'all RT M below one':1-R(3,10)-R(1,10)/k(R(1,8))-(b(R(1,10))-1),
 }
 assert H.subs({a:R(7,20),z:R(1,10)})==Hsmall
 assert H.subs({a:R(79,200),z:R(1,10)})==Hmid
 assert constants['angle lower a']==R(62,315)
 assert all(t>0 for t in constants.values())
 # Four corners for a >= 79/200, plus two low-h corners for the middle a branch.
 margins={}
 budget=HF-F-q(RT+Dz)
 for hh in [R(1,8),R(3,10)]:
  for zz in [R(0),R(1,10)]:
   margins['large '+str(hh)+' '+str(zz)]=budget.subs({a:R(79,200),h:hh,z:zz})
 for zz in [R(0),R(1,10)]:
  margins['middle low '+str(zz)]=budget.subs({a:R(7,20),h:R(1,8),z:zz})
 assert all(t>0 for t in margins.values()),margins
 result={'result':'passed','new_rational_inequalities':2,'new_polynomial_reconstructions':4,
  'new_positive_coefficients':count,'algebraic_identities':len(ids),
  'positive_exact_constants':len(constants),'positive_corner_margins':len(margins),'corner_margins':{k:str(v) for k,v in margins.items()},
  'UNSAT':0,'new_theorem':'All z <= 1/10 excluded in both positive-C mechanisms, with round61 high-h case',
  'remaining_common_strip':'1/10 < z < 1/5',
  'not_proved':'entire double-direct, right-W bridge, G2 or S(6)=2','global_bound':'2 <= S(6) < 2.03'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
