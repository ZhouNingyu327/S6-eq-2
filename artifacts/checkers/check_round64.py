"""Independent formulas, full inverse Bernstein reconstruction and scope guard."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 a,z,h,S,u,v=s.symbols('a z h S u v')
 b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t)
 g=lambda t:(1-t)/(1+t);q=lambda t:t/(2-t)
 X=(1-z)*(a*a*(1+2*z)-z)/((a-z)*(1+a*z))
 e=2*a*z*(1-a-z)/((a-z)*(1+a*z))
 F=lambda aa:(1+aa*aa-2*aa*(1+3*z)/(1+z))/(1-aa*aa)
 RP=R(2,15)+X+R(8,15)*e
 targets=[('low_budget',R(7,12)-F(a)-q(RP),2)]
 def polynomial(hh):
  # Explicit quadratic from support coordinates, not the generator's line solver.
  return s.cancel((g(z)-hh-z)*(a-z)*(1+a*z)
     +(2*z/(1-z*z)-(1-hh*hh)/(2*hh))*(1-z)*(a*a*(1+2*z)-z))
 for tag,hh in [('quarter',R(1,4)),('third',R(1,3))]:
  P=polynomial(hh);pp=s.Poly(P,a);assert pp.degree()==2
  targets += [(tag+'_concavity',-pp.nth(2),1),(tag+'_zero',P.subs(a,0),1),(tag+'_two_fifths',P.subs(a,R(2,5)),1)]
 B=(2-3*z+4*z*z)/4;H=R(29,70);RT=R(29,70)+R(4059,4060)*z
 for tag,hh in [('third',R(1,3)),('upper',H)]:
  P=polynomial(hh);pp=s.Poly(P,a);assert pp.degree()==2
  if tag=='upper':targets += [(tag+'_concavity',-pp.nth(2),1),(tag+'_zero',P.subs(a,0),1)]
  targets.append((tag+'_B',P.subs(a,B),1))
 targets += [('high_budget_B',R(7,12)-F(B)-q(RT),1),('high_budget_gH',R(7,12)-F(R(41,99))-q(RT),1),('B_above_z',B-z,1)]
 records=json.loads((Path(__file__).resolve().parent/'round64_certificate.json').read_text(encoding='utf-8'))
 count=0
 for j,(label,expr,dim) in enumerate(targets):
  polys=[]
  for off,kind in enumerate(['numerator','denominator']):
   rec=records[2*j+off];assert (rec['name'],rec['kind'])==(label,kind)
   poly=s.sympify(rec['polynomial'],locals={'a':a,'z':z})
   if dim==1:
    assert rec['variables']==['z'] and rec['box']==[['1/10','1/5']]
    p=s.Poly(s.expand(poly.subs(z,R(1,10)+v/10)),v);n=rec['degree'][0];assert p.degree()==n
    cc=[R(c) for c in rec['coefficients']];assert len(cc)==n+1 and all(c>0 for c in cc)
    rebuilt=s.Poly.from_dict({(i,):comb(n,i)*sum(((-1)**(i-jj)*comb(i,jj)*cc[jj] for jj in range(i+1)),R(0)) for i in range(n+1)},(v,))
    assert rebuilt==p;count+=n+1
   else:
    assert rec['variables']==['a','z'] and rec['box']==[['2/7','3/5'],['1/10','1/5']]
    p=s.Poly(s.expand(poly.subs({a:R(2,7)+R(11,35)*u,z:R(1,10)+v/10})),u,v)
    n,m=rec['degree'];assert (p.degree(u),p.degree(v))==(n,m)
    cc=[[R(c) for c in row] for row in rec['coefficients']]
    assert len(cc)==n+1 and all(len(row)==m+1 for row in cc) and all(c>0 for row in cc for c in row)
    coeff={(i,l):comb(n,i)*comb(m,l)*sum(((-1)**(i-ii+l-jj)*comb(i,ii)*comb(l,jj)*cc[ii][jj]
       for ii in range(i+1) for jj in range(l+1)),R(0)) for i in range(n+1) for l in range(m+1)}
    assert s.Poly.from_dict(coeff,(u,v))==p;count+=(n+1)*(m+1)
   polys.append(poly)
  assert s.cancel(expr*polys[1]-polys[0])==0,label
 assert len(records)==28 and count==114
 XS=(b(a)+S-2)/(k(a)-k(z));eS=1-S-k(z)*XS
 DH=g(z)+(k(z)-1/k(h))*X-h-z
 ids={
  'explicit XG':XS.subs(S,g(z))-X,
  'explicit eG':eS.subs(S,g(z))-e,
  'P1R S4 slope':s.diff(XS+k(h)*eS,S)-(1-k(h)*k(a))/(k(a)-k(z)),
  'P1T S4 slope':s.diff(S+(k(z)-1/k(h))*XS,S)-(k(a)-1/k(h))/(k(a)-k(z)),
  'P1T h concavity':s.diff(DH,h,2)+X/h**3,
  'polynomial support relation':polynomial(h)-DH*(a-z)*(1+a*z),
  'RT h convexity':s.diff(h+z/k(h),h,2)-z/h**3,
  'RT high derivative':s.diff(h+z/k(h),h)-(1-z*(1+h*h)/(2*h*h)),
  'F z convexity':s.diff(F(a),z,2)-4*k(a)/(1+z)**3,
  'RP endpoint':b(R(1,4))-1+X+k(R(1,4))*e-RP,
  'high R formula':H+z/k(H)-RT,
  'high g formula':g(H)-R(41,99),
 }
 for name,ex in ids.items():assert s.cancel(ex)==0,name
 constants={
  'a lower gap':R(13,11)-b(R(2,7)),
  'a upper gap':-F(a).subs({a:R(3,5),z:R(1,10)}),
  'a-z in low box':R(2,7)-R(1,5),
  'one-a-z':1-R(3,5)-R(1,5),
  'RP q-domain':1-R(2,15)-R(3,5)-R(8,15)*R(5,12),
  'middle slope branch':g(R(1,3))-R(2,5),
  'middle q-domain':1-R(1,3)-R(1,5)/k(R(1,4)),
  'high half-angle cap':(1+H)**2-2,
  'high q-domain':1-RT.subs(z,R(1,5)),
  'B upper below one':1-B.subs(z,R(1,10)),
  'B derivative negative':R(3,4)-2*R(1,5),
  'all target coefficient count':R(114),
 }
 # Last value is metadata, not a mathematical positive comparison.
 constants.pop('all target coefficient count')
 assert all(val>0 for val in constants.values()),constants
 assert g(R(1,4))==R(3,5)
 assert 1-R(1,5)*(1+R(1,3)**2)/(2*R(1,3)**2)==0
 corners={}
 for hh in [R(1,4),R(1,3)]:
  for zz in [R(1,10),R(1,5)]:
   corners[str(hh)+' '+str(zz)]=R(7,12)-F(R(2,5)).subs(z,zz)-q(hh+zz/k(hh))
 assert all(c>0 for c in corners.values())
 result={'result':'passed','deduplicated_rational_targets':14,'new_polynomial_reconstructions':28,
  'new_positive_rational_coefficients':count,'support_identities_checked':len(ids),
  'positive_exact_constants':len(constants),'positive_corner_margins':len(corners),
  'corner_margins':{key:str(val) for key,val in corners.items()},'UNSAT':0,
  'local_theorem':'All positive-C double-direct configurations in the current normalized middle-z model excluded, including h=0',
  'angle_coverage':'[0,1/4], [1/4,1/3], [1/3,sqrt(2)-1]',
  'global_proof_status':'Candidate full closure conditional on historical global reduction; comprehensive audit pending',
  'S6_equals_2_announced':False}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
