"""Independent exact inverse Bernstein reconstruction and algebraic checks."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 records=json.loads((Path(__file__).resolve().parent/'round61_certificate.json').read_text(encoding='utf-8'))
 a,z,h,u,v,S,Y,XX=s.symbols('a z h u v S Y XX')
 b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t)
 g=lambda t:(1-t)/(1+t);q=lambda t:t/(2-t)
 X=(1-z)*(a*a*(1+2*z)-z)/((a-z)*(1+a*z))
 e=2*a*z*(1-a-z)/((a-z)*(1+a*z))
 F=lambda t:(1+t*t-2*t*(1+3*z)/(1+z))/(1-t*t)
 Dz=2*z*z/(1-z*z)
 A=2*h*(1-h-z)/(1-h*h);RT=h+z*(1-h*h)/(2*h)
 avg=(4*h*h/(1-h*h)+2*X+4*h*e/(1-h*h)+RT)/3+Dz
 targets=[('high_h_small_z',R(7,12)-F(A)-q(RT+Dz),h,R(3,10),R(5,12),z,R(0),R(1,10))]
 targets += [('large_z_low_'+tag,R(7,12)-F(a)-q(avg.subs(h,hh)),a,R(3,8),R(5,11),z,R(1,5),R(4,15))
             for tag,hh in [('left',R(1,8)),('right',R(3,10))]]
 def reconstruct(rec,pvar,lo,hi,qvar,bot,top):
  assert rec['variables']==[str(pvar),str(qvar)] and rec['box']==[[str(lo),str(hi)],[str(bot),str(top)]]
  poly=s.sympify(rec['polynomial'],locals={'a':a,'z':z,'h':h})
  n,m=rec['degree'];cc=[[R(c) for c in row] for row in rec['coefficients']]
  assert len(cc)==n+1 and all(len(row)==m+1 for row in cc)
  assert all(c>0 for row in cc for c in row)
  # Full inverse transform: Bernstein -> monomial, first u then v.
  t=[[comb(n,i)*sum(((-1)**(i-j)*comb(i,j)*cc[j][l] for j in range(i+1)),R(0)) for l in range(m+1)] for i in range(n+1)]
  coeff=[[comb(m,l)*sum(((-1)**(l-j)*comb(l,j)*t[i][j] for j in range(l+1)),R(0)) for l in range(m+1)] for i in range(n+1)]
  rebuilt=s.Poly.from_dict({(i,j):coeff[i][j] for i in range(n+1) for j in range(m+1)},(u,v))
  p=s.Poly(s.expand(poly.subs({pvar:lo+(hi-lo)*u,qvar:bot+(top-bot)*v})),u,v)
  assert (p.degree(u),p.degree(v))==(n,m) and p==rebuilt
  return poly,(n+1)*(m+1)
 count=0
 for j,(label,target,pvar,lo,hi,qvar,bot,top) in enumerate(targets):
  polys=[]
  for off,kind in enumerate(['numerator','denominator']):
   rec=records[2*j+off];assert (rec['name'],rec['kind'])==(label,kind)
   poly,num=reconstruct(rec,pvar,lo,hi,qvar,bot,top);polys.append(poly);count+=num
  assert s.cancel(target*polys[1]-polys[0])==0,label
 D0=R(7,13)+R(60,91)*X-e
 tn,td=s.cancel(2-F(a)-D0).as_numer_denom()
 square_denominators=[]
 for j,(tag,hh) in enumerate([('left',R(3,10)),('right',R(5,12))]):
  rec=records[6+j];assert rec['name']=='large_z_F_'+tag and rec['kind']=='square_denominator_numerator'
  poly,num=reconstruct(rec,a,R(3,8),R(5,11),z,R(1,5),R(4,15));count+=num
  M=hh+z/k(hh)+Dz;ln,ld=s.cancel(2-F(a)-q(M)).as_numer_denom()
  TN,TD,LN,LD=[s.Poly(t,a,z) for t in [tn,td,ln,ld]]
  assert s.Poly(poly,a,z)==TN**2*(LN**2-LD**2)-LN**2*TD**2
  square_denominators.append((ld,M,60 if j==0 else 120))
 assert count==628 and len(records)==8
 XS=(b(a)+S-2)/(k(a)-k(z));eS=1-S-k(z)*XS
 D=g(h)+k(h)*X-e
 Fsupport=b(a)-k(a)*(2-g(z))
 Yh=h*h/(1-2*h*h)
 identities={
  'XG coordinate':XS.subs(S,g(z))-X,
  'eG coordinate':eS.subs(S,g(z))-e,
  'F coordinate':Fsupport-F(a),
  'positive LT lower':b(h)-k(h)*(1-z)-(1-A),
  'positive RT upper':(b(h)-(1-z))/k(h)-RT,
  'positive P1R slope':s.diff(XS+k(h)*eS,S)-(1-k(h)*k(a))/(k(a)-k(z)),
  'positive depth slope':s.diff(b(h)-k(h)*(1-XS)-eS,S)-(k(a)+k(h))/(k(a)-k(z)),
  'depth endpoint':(b(h)-k(h)*(1-XS)-eS).subs(S,g(z))-D,
  'a minus XG':a-X-z*(1-a*a)*(1-a-z)/((a-z)*(1+a*z)),
  'X a derivative':s.diff(X,a)-(s.diff(b(a),a)-s.diff(k(a),a)*X)/(k(a)-k(z)),
  'X z derivative':s.diff(X,z)-(s.diff(g(z),z)+s.diff(k(z),z)*X)/(k(a)-k(z)),
  'X a comparison':s.diff(b(a),a)/s.diff(k(a),a)-2*a/(1+a*a),
  'X z comparison':-s.diff(g(z),z)/s.diff(k(z),z)-(1-z)**2/(1+z*z),
  'e a derivative':s.diff(e,a)+k(z)*s.diff(X,a),
  'e z derivative':s.diff(e,z)+s.diff(g(z),z)+s.diff(k(z),z)*X+k(z)*s.diff(X,z),
  'depth convexity':s.diff(D,h,2)-4*(1+3*h*h-(1-X)*h*(3+h*h))/(1-h*h)**3,
  'depth positive remainder':1+3*h*h-h*(3+h*h)-(1-h)**3,
  'right convexity':s.diff(RT,h,2)-z/h**3,
  'delta convexity':s.diff(b(h)-1,h,2)-4*(1+3*h*h)/(1-h*h)**3,
  'K convexity':s.diff(k(h),h,2)-4*h*(3+h*h)/(1-h*h)**3,
  'F at g':F(g(h))-(h-2*z/(k(h)*(1+z))),
  'F zero z':F(g(h)).subs(z,Yh),
  'F at g convex z':s.diff(F(g(h)),z,2)-4/(k(h)*(1+z)**3),
  'Y divided K derivative':s.diff(Yh/k(h),h)-(2*h**4-h*h+1)/(2*(1-2*h*h)**2),
  'D0 denominator':td-91*(a-z)*(1-a*a)*(1+z)*(1+a*z),
 }
 for i,(ld,M,mult) in enumerate(square_denominators):
  identities['L denominator branch '+str(i)]=ld+mult*(1-a*a)*(1-z)*(1+z)**2*(2-M)
 for name,expr in identities.items():assert s.cancel(expr)==0,name
 Xmax=R(9,35)
 const={
  'angle outer cap':R(17,12)**2-2,
  'a lower gap':R(4,3)-b(R(3,8)),
  'F a upper gap':-F(a).subs({a:R(5,11),z:R(1,5)}),
  'F maximum':F(a).subs({a:R(3,8),z:R(1,5)}),
  'X z threshold':(1-R(4,15))**2/(1+R(4,15)**2)-R(5,11),
  'high depth endpoint gap':g(R(3,10))-g(R(5,12))+(k(R(3,10))-k(R(5,12)))*Xmax,
  'depth positive height':1-D0.subs({a:R(5,11),z:R(1,5)}),
  'large triangle base':1-R(9,55)-R(7,9),
  'large lower branch':g(R(3,10))-R(5,11),
  'small A positive':k(R(3,10))*(1-R(5,12)-R(1,10)),
  'small A below one':1-k(R(5,12))*(1-R(3,10)),
  'small M below one':1-R(5,12)-R(1,10)/k(R(3,10))-(b(R(1,10))-1),
  'large a minus z':R(3,8)-R(4,15),
  'large a plus z':1-R(5,11)-R(4,15),
  'g branch endpoint zero margin':R(7,12)-R(8,15),
  'g branch endpoint Y margin':R(7,12)-q(R(95,168)),
  'g branch M below one':1-R(95,168),
 }
 for tag,hh in [('left',R(3,10)),('right',R(5,12))]:
  const['large M cap '+tag]=R(7,8)-hh-R(4,15)/k(hh)-(b(R(4,15))-1)
 for tag,hh in [('left',R(1,8)),('right',R(3,10))]:
  RP=b(hh)-1+Xmax+k(hh)*R(5,12);RTcap=hh+R(4,15)/k(hh)
  const['averaged M below one '+tag]=1-(2*RP+RTcap)/3-(b(R(4,15))-1)
 assert all(val>0 for val in const.values()),const
 assert X.subs({a:R(5,11),z:R(1,5)})==Xmax
 assert D0.subs({a:R(5,11),z:R(1,5)})==R(3683,7644)
 assert F(a).subs({a:R(3,8),z:R(1,5)})==R(9,55)
 result={'result':'passed','new_rational_inequalities':5,'new_polynomial_reconstructions':8,
  'new_positive_coefficients':count,'algebraic_identities':len(identities),
  'positive_exact_constants':len(const),'UNSAT':0,
  'new_theorems':['positive C: all z >= 1/5 excluded in both mechanisms',
    'positive C: h >= 3/10 and z <= 1/10 excluded in both mechanisms',
    'positive C: h <= 1/3 and a >= g(h) excluded in both mechanisms'],
  'not_proved':'entire double-direct, right-W bridge, G2 or S(6)=2',
  'global_bound':'2 <= S(6) < 2.03'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
