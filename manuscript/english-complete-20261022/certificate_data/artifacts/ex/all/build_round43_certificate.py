"""One complete univariate certificate for the small-C interval proof."""
from pathlib import Path
from math import comb
import json
import sympy as s
def main():
 a,z,v=s.symbols("a z v");k=2*a/(1-a*a)
 F=(1+a*a)/(1-a*a)-k*(1+2*z/(1+z))
 E=(1-z)**2-F-a/(2-a);Y=a*a/(1-2*a*a)
 expr=s.cancel((E.subs(z,Y)-s.Rational(13,20)*a)/a)
 num,den=expr.as_numer_denom()
 if den.subs(a,s.Rational(1,6))<0:num,den=-num,-den
 parts=[]
 for name,p in [("numerator",num),("denominator",den)]:
  poly=s.Poly(p.subs(a,v/3),v);n=poly.degree()
  cc=[sum(c*s.Rational(comb(i,j),comb(n,j)) for (j,),c in poly.terms() if j<=i)
      for i in range(n+1)]
  assert min(cc)>0
  parts.append({"part":name,"degree":n,"coefficients":[str(c) for c in cc]})
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round43_certificate.json").write_text(json.dumps({
  "expression":str(s.factor(expr)),"map":"a=v/3; 0<=v<=1","parts":parts},indent=2),encoding="utf-8")
 print("Built 2 complete identities, 20 strictly positive rational coefficients.")
if __name__=="__main__":main()
