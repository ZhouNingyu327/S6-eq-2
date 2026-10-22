"""Two explicit continuous inequalities; no layout or angle search."""
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
 H=91*a/(140-200*z);D=b(H)-1+z;HF=2-1/(1-D)
 RP=b(H)-1+X+k(H)*e;RT=H+z/k(H)
 targets=[('small_a_P1R',HF-F(a)-q(RP+Dz),a,R(62,315),R(7,20),z,R(0),R(1,10)),
          ('middle_a_RT',HF-F(a)-q(RT+Dz),a,R(7,20),R(79,200),z,R(0),R(1,10))]
 raw=[]
 for label,ex,pvar,lo,hi,qvar,bot,top in targets:
  N,D=s.cancel(ex).as_numer_denom()
  if D.subs({pvar:(lo+hi)/2,qvar:(bot+top)/2})<0:N,D=-N,-D
  raw += [(label,kind,poly,pvar,lo,hi,qvar,bot,top) for kind,poly in [('numerator',N),('denominator',D)]]
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
 assert len(records)==4 and count==338
 (Path(__file__).resolve().parent/'round62_certificate.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
 print(json.dumps({'rational_inequalities':2,'full_polynomials':4,'positive_rational_coefficients':count}))
if __name__=='__main__':main()
