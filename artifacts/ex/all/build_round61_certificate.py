"""Five explicit continuous inequalities; no layout or angle search."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational;a,z,h,u,v=s.symbols('a z h u v')
b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t)
g=lambda t:(1-t)/(1+t);q=lambda t:t/(2-t)
def main():
 X=s.cancel((b(a)+g(z)-2)/(k(a)-k(z)));e=1-g(z)-k(z)*X
 F=lambda t:b(t)-k(t)*(2-g(z))
 Dz=b(z)-1;A=k(h)*(1-h-z);RT=h+z/k(h)
 avg=(2*(b(h)-1+X+k(h)*e)+RT)/3+Dz
 targets=[('high_h_small_z',R(7,12)-F(A)-q(RT+Dz),h,R(3,10),R(5,12),z,R(0),R(1,10))]
 targets += [('large_z_low_'+tag,R(7,12)-F(a)-q(avg.subs(h,hh)),a,R(3,8),R(5,11),z,R(1,5),R(4,15))
             for tag,hh in [('left',R(1,8)),('right',R(3,10))]]
 raw=[]
 for label,ex,pvar,lo,hi,qvar,bot,top in targets:
  N,D=s.cancel(ex).as_numer_denom()
  if D.subs({pvar:(lo+hi)/2,qvar:(bot+top)/2})<0:N,D=-N,-D
  raw += [(label,kind,poly,pvar,lo,hi,qvar,bot,top) for kind,poly in [('numerator',N),('denominator',D)]]
 D0=g(R(3,10))+k(R(3,10))*X-e
 tn,td=s.cancel(2-F(a)-D0).as_numer_denom()
 for tag,hh in [('left',R(3,10)),('right',R(5,12))]:
  M=hh+z/k(hh)+Dz;ln,ld=s.cancel(2-F(a)-q(M)).as_numer_denom()
  TN,TD,LN,LD=[s.Poly(t,a,z) for t in [tn,td,ln,ld]]
  N=(TN**2*(LN**2-LD**2)-LN**2*TD**2).as_expr()
  raw.append(('large_z_F_'+tag,'square_denominator_numerator',N,a,R(3,8),R(5,11),z,R(1,5),R(4,15)))
 records=[];count=0
 for label,kind,poly,pvar,lo,hi,qvar,bot,top in raw:
  p=s.Poly(s.expand(poly.subs({pvar:lo+(hi-lo)*u,qvar:bot+(top-bot)*v})),u,v)
  n,m=p.degree(u),p.degree(v)
  c0=[[p.coeff_monomial(u**i*v**j) for j in range(m+1)] for i in range(n+1)]
  c1=[[sum((c0[ii][j]*R(comb(i,ii),comb(n,ii)) for ii in range(i+1)),R(0)) for j in range(m+1)] for i in range(n+1)]
  cc=[[sum((c1[i][jj]*R(comb(j,jj),comb(m,jj)) for jj in range(j+1)),R(0)) for j in range(m+1)] for i in range(n+1)]
  assert all(c>0 for row in cc for c in row),(label,kind)
  records.append({'name':label,'kind':kind,'variables':[str(pvar),str(qvar)],
    'box':[[str(lo),str(hi)],[str(bot),str(top)]],'degree':[n,m],
    'polynomial':str(poly),'coefficients':[[str(c) for c in row] for row in cc]})
  count+=(n+1)*(m+1)
 assert len(records)==8 and count==628
 (Path(__file__).resolve().parent/'round61_certificate.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
 print(json.dumps({'rational_inequalities':5,'full_polynomials':8,'positive_rational_coefficients':count}))
if __name__=='__main__':main()
