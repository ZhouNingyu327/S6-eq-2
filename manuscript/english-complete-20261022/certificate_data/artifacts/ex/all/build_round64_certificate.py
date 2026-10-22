"""Fourteen deduplicated exact targets for the full positive double-direct angle range."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational;a,z,u,v=s.symbols('a z u v')
b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t)
g=lambda t:(1-t)/(1+t);q=lambda t:t/(2-t)
def main():
 X=s.cancel((b(a)+g(z)-2)/(k(a)-k(z)));e=1-g(z)-k(z)*X
 F=lambda aa:b(aa)-k(aa)*(2-g(z))
 RP=b(R(1,4))-1+X+k(R(1,4))*e
 targets=[('low_budget',R(7,12)-F(a)-q(RP),2)]
 for tag,hh in [('quarter',R(1,4)),('third',R(1,3))]:
  P=s.cancel((g(z)+(k(z)-1/k(hh))*X-hh-z)*(a-z)*(1+a*z))
  pp=s.Poly(P,a);assert pp.degree()==2
  targets += [(tag+'_concavity',-pp.coeff_monomial(a*a),1),(tag+'_zero',P.subs(a,0),1),(tag+'_two_fifths',P.subs(a,R(2,5)),1)]
 B=R(1,2)-R(3,4)*z+z*z;H=R(29,70);RT=H+z/k(H)
 for tag,hh in [('third',R(1,3)),('upper',H)]:
  P=s.cancel((g(z)+(k(z)-1/k(hh))*X-hh-z)*(a-z)*(1+a*z))
  pp=s.Poly(P,a);assert pp.degree()==2
  if tag=='upper':targets += [(tag+'_concavity',-pp.coeff_monomial(a*a),1),(tag+'_zero',P.subs(a,0),1)]
  targets.append((tag+'_B',P.subs(a,B),1))
 targets += [('high_budget_B',R(7,12)-F(B)-q(RT),1),('high_budget_gH',R(7,12)-F(g(H))-q(RT),1),('B_above_z',B-z,1)]
 assert len(targets)==14
 records=[];count=0
 for label,expr,dim in targets:
  N,D=s.cancel(expr).as_numer_denom()
  if D.subs({a:R(2,5),z:R(3,20)})<0:N,D=-N,-D
  for kind,poly in [('numerator',N),('denominator',D)]:
   if dim==1:
    p=s.Poly(s.expand(poly.subs(z,R(1,10)+v/10)),v);n=p.degree()
    cc=[sum((p.nth(j)*R(comb(i,j),comb(n,j)) for j in range(i+1)),R(0)) for i in range(n+1)]
    assert all(c>0 for c in cc),(label,kind)
    rec={'variables':['z'],'box':[['1/10','1/5']],'degree':[n],'coefficients':[str(c) for c in cc]};count+=n+1
   else:
    p=s.Poly(s.expand(poly.subs({a:R(2,7)+R(11,35)*u,z:R(1,10)+v/10})),u,v);n,m=p.degree(u),p.degree(v)
    cc=[[sum((c*R(comb(i,ij[0]),comb(n,ij[0]))*R(comb(j,ij[1]),comb(m,ij[1])) for ij,c in p.terms() if ij[0]<=i and ij[1]<=j),R(0)) for j in range(m+1)] for i in range(n+1)]
    assert all(c>0 for row in cc for c in row),(label,kind)
    rec={'variables':['a','z'],'box':[['2/7','3/5'],['1/10','1/5']],'degree':[n,m],'coefficients':[[str(c) for c in row] for row in cc]};count+=(n+1)*(m+1)
   records.append({'name':label,'kind':kind,'polynomial':str(poly),**rec})
 assert len(records)==28 and count==114
 (Path(__file__).resolve().parent/'round64_certificate.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
 print(json.dumps({'deduplicated_rational_targets':14,'full_polynomials':28,'strictly_positive_rational_coefficients':114}))
if __name__=='__main__':main()
