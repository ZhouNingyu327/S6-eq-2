"""Analytic rational separators for one exact C angle; no layout search."""
from pathlib import Path
from math import comb
import json
import sympy as sp
def main():
 a,z,v=sp.symbols("a z v")
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
 G=(1-z)/(1+z);X=(b+G-2)/(k-h)
 P=sp.cancel((G+(h-sp.Rational(4,3))*X-sp.Rational(1,3)-z)*
             3*(a-z)*(1+a*z))
 A=sp.Rational(1,2)-sp.Rational(3,4)*z+z*z
 q=lambda t:t/(2-t)
 E=b-k*(2-G)+q(sp.Rational(1,3)+sp.Rational(4,3)*z)-sp.Rational(7,12)
 polynomials={
  "P at separator":sp.cancel(P.subs(a,A)),
  "objective at separator":sp.cancel(-E.subs(a,A)).as_numer_denom()[0],
  "objective high a at one half":sp.cancel(-E.subs(a,sp.Rational(1,2))).as_numer_denom()[0]
 }
 rows=[]
 for name,p in polynomials.items():
  if name=="P at separator":poly=sp.Poly(sp.expand(p.subs(z,sp.Rational(2,9)*v)),v)
  else:poly=sp.Poly(sp.expand(p.subs(z,sp.Rational(2,9)*v)),v)
  n=poly.degree()
  coeff=[sum(c*sp.Rational(comb(i,j),comb(n,j)) for (j,),c in poly.terms() if j<=i)
         for i in range(n+1)]
  row={"name":name,"degree":n,"minimum":str(min(coeff)),
       "nonnegative":all(c>=0 for c in coeff),
       "polynomial":str(sp.factor(p)),"coefficients":[str(c) for c in coeff]}
  rows.append(row);print(json.dumps({k:v for k,v in row.items() if k!="coefficients"}),flush=True)
 Path("work/round42_345_exploration.json").write_text(json.dumps(rows,indent=2),encoding="utf-8")
if __name__=="__main__":main()
