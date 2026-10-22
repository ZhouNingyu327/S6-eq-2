"""One complete quartic certificate for the small-x scalar lemma."""
from pathlib import Path
from math import comb
import sympy as sp,json
def main():
 x,v=sp.symbols("x v");I=3*x*(1-x)/((1+x)*(2-x))
 K=2*x/(1-x*x);T=2*x*x/(1-x*x)
 expr=sp.cancel((I+(K-2)*T+T*T)/x-sp.Rational(2,5))
 num,den=expr.as_numer_denom()
 if den.subs(x,sp.Rational(1,9))<0:num,den=-num,-den
 assert sp.cancel(den-5*(2-x)*(1-x)**2*(1+x))==0
 poly=sp.Poly(num.subs(x,2*v/9),v);n=poly.degree()
 cc=[sum(c*sp.Rational(comb(i,j[0]),comb(n,j[0])) for j,c in poly.terms() if j[0]<=i)
     for i in range(n+1)]
 assert n==4 and min(cc)>0
 cert={"degree":n,"map":"x=2v/9; v in [0,1]",
  "positive_denominator":"5*(2-x)*(1-x)^2*(1+x)",
  "coefficients":[str(c) for c in cc]}
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round52_certificate.json").write_text(json.dumps(cert,indent=2),encoding="utf-8")
 print("One full quartic identity; five strictly positive rational coefficients.")
if __name__=="__main__":main()

