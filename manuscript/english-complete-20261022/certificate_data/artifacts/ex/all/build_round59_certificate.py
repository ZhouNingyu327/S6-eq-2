"""Five explicit one-variable certificates for the same-F axis-area proof."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational;x,t,d,u=s.symbols('x t d u')
b=lambda a:(1+a*a)/(1-a*a);k=lambda a:2*a/(1-a*a)
g=lambda a:(1-a)/(1+a);q=lambda a:a/(2-a)
B=lambda a:1+k(a)*(1-(b(a)-1)-a)
def main():
 G=2-1/(1-d-t)-q(x+d)-g(x)+k(x)*(B(t)-1)
 tc=2*x*x/(1-x*x);ds=R(81,70)*x*x;dc=R(2,35)
 records=[];count=0
 for name,expr,lo,hi in [
  ('small_zero',G.subs({d:ds,t:0})/x,R(0),R(1,6)),
  ('small_cos_cap',G.subs({d:ds,t:tc})/x,R(0),R(1,6)),
  ('middle_zero',G.subs({d:dc,t:0}),R(1,6),R(3,4)),
  ('middle_cos_cap',G.subs({d:dc,t:tc}),R(1,6),R(1,4)),
  ('middle_tau_cap',G.subs({d:dc,t:R(1,6)}),R(1,4),R(3,4))]:
  num,den=s.cancel(expr).as_numer_denom()
  if den.subs(x,(lo+hi)/2)<0:num,den=-num,-den
  p=s.Poly(s.expand(num.subs(x,lo+(hi-lo)*u)),u);degree=p.degree();cc=[]
  for i in range(degree+1):
   value=sum((coef*R(comb(i,j[0]),comb(degree,j[0])) for j,coef in p.terms() if j[0]<=i),R(0))
   assert value>0,(name,i,value);cc.append(str(value))
  records.append({'name':name,'interval':[str(lo),str(hi)],'degree':degree,
   'positive_denominator':str(s.factor(den)),'coefficients':cc});count+=len(cc)
 assert len(records)==5 and count==42
 (Path(__file__).resolve().parent/'round59_certificate.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
 print(json.dumps({'new_polynomials':5,'positive_rational_coefficients':42}))
if __name__=='__main__':main()
