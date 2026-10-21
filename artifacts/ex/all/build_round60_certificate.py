"""Four explicit rational inequalities, eight full polynomial certificates."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational;a,z,h,u,v=s.symbols('a z h u v')
b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t);g=lambda t:(1-t)/(1+t)
q=lambda t:t/(2-t)
def main():
 X=s.cancel((b(a)+g(z)-2)/(k(a)-k(z)));e=1-g(z)-k(z)*X
 F=b(a)-k(a)*(2-g(z));Dz=b(z)-1
 Mlarge=b(R(5,12))-1+X-k(R(5,12))*e+Dz
 Mmid=b(R(3,10))-1+X-k(R(1,8))*e+Dz
 A=1-h-z/k(h);FA=b(A)-k(A)*(2-g(z));MA=g(h)+k(h)*z+Dz
 targets=[
  ('large_z',R(7,12)-F-q(Mlarge),a,R(1,3),R(1,2),z,R(3,20),R(4,15)),
  ('high_h_small_z',R(7,12)-FA-q(MA),h,R(3,10),R(5,12),z,R(0),R(3,20)),
  ('middle_z',R(7,12)-F-q(Mmid),a,R(2,7),R(3,5),z,R(1,10),R(3,20)),
  ('low_h_small_z',2-1/(1-(b(h)-1)-z)-FA-q(MA),h,R(1,8),R(3,10),z,R(0),R(1,10))]
 records=[];count=0
 for label,expr,pvar,lo,hi,qvar,bot,top in targets:
  N,D=s.cancel(expr).as_numer_denom()
  if D.subs({pvar:(lo+hi)/2,qvar:(bot+top)/2})<0:N,D=-N,-D
  for kind,poly in [('numerator',N),('denominator',D)]:
   p=s.Poly(s.expand(poly.subs({pvar:lo+(hi-lo)*u,qvar:bot+(top-bot)*v})),u,v)
   n,m=p.degree(u),p.degree(v);cc=[]
   for i in range(n+1):
    row=[]
    for j in range(m+1):
     value=sum((c*R(comb(i,ij[0]),comb(n,ij[0]))*R(comb(j,ij[1]),comb(m,ij[1])) for ij,c in p.terms() if ij[0]<=i and ij[1]<=j),R(0))
     assert value>0,(label,kind,i,j,value);row.append(str(value))
    cc.append(row)
   records.append({'name':label,'kind':kind,'variables':[str(pvar),str(qvar)],
    'box':[[str(lo),str(hi)],[str(bot),str(top)]],'degree':[n,m],
    'polynomial':str(s.factor(poly)),'coefficients':cc})
   count+=(n+1)*(m+1)
 assert len(records)==8 and count==362
 (Path(__file__).resolve().parent/'round60_certificate.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
 print(json.dumps({'rational_inequalities':4,'full_polynomials':8,'positive_rational_coefficients':362}))
if __name__=='__main__':main()
