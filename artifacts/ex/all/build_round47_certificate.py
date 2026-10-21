"""Three full analytic charts and one full univariate bottom-chord inequality."""
from pathlib import Path
from math import comb
import json
import sympy as sp
def main():
 x,t,u,v=sp.symbols("x t u v");m=(1-t)**2
 P=3*x*(m-x)*(1-x)+2*x*t*(1+m-x)-(2*t-t*t)*(1-x)
 g=lambda y:(1-y)/(1+y);K=2*x/(1-x*x)
 charts=[
  ("small x",sp.cancel(P.subs(t,2*x*x/(1-x*x)*v)/x),sp.Rational(0),sp.Rational(1,3),(1-x*x)**3),
  ("middle x",sp.cancel(P.subs(t,v/4)),sp.Rational(1,3),sp.Rational(1,2),sp.Integer(32)),
  ("large x",sp.cancel(P.subs(t,(1-x)**2/(2*x)*v)/(1-x)**2),sp.Rational(1,2),sp.Integer(1),4*x*x),
  ("large tau",sp.cancel(1-g(sp.Rational(7,12)-x)-g(x)+K/4),
   sp.Rational(1,3),sp.Rational(1,2),2*(1-x*x)*(19-12*x))]
 saved=[]
 for name,expr,lo,hi,positive_den in charts:
  num,den=expr.as_numer_denom()
  if den.subs({x:(lo+hi)/2,v:sp.Rational(1,2)})<0:num,den=-num,-den
  ratio=sp.cancel(den/positive_den);assert ratio.is_Rational and ratio>0
  poly=sp.Poly(sp.expand(num.subs(x,lo+(hi-lo)*u)),u,v)
  n=poly.degree(u);m=poly.degree(v)
  cc=[[sum(c*sp.Rational(comb(i,j),comb(n,j))*sp.Rational(comb(k,l),comb(m,l))
           for (j,l),c in poly.terms() if j<=i and l<=k)
       for k in range(m+1)] for i in range(n+1)]
  assert min(c for row in cc for c in row)>0
  saved.append({"name":name,"range":[str(lo),str(hi)],"degrees":[n,m],
   "expression":str(sp.factor(expr)),"positive_denominator":str(positive_den),
   "denominator_ratio":str(ratio),"coefficients":[[str(c) for c in row] for row in cc]})
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round47_certificate.json").write_text(json.dumps(saved,indent=2),encoding="utf-8")
 print("Built 4 whole polynomial identities and 76 positive rational coefficients.")
if __name__=="__main__":main()
