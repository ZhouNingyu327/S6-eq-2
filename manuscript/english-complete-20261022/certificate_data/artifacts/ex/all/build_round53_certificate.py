"""Two explicit full analytic charts for the actual LEFT-seam lemma."""
from pathlib import Path
from math import comb
import sympy as sp,json
def main():
 a,z,w,u,v=sp.symbols("a z w u v")
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
 G=(1-z)/(1+z);L=2-G+w;T=b-k*L
 Qmin=2-L+(h-1)*(b-L)/(k-h)
 R=sp.cancel(Qmin*(1+T)-2*T)
 N=(1-a)**2;d=6*a-1-a*a
 D1=(1-a*a)*(a*d-N*v)*(d+a*N*v);D0=D1*(d+N*v)
 exprs=[("base over z",sp.cancel(R.subs(w,0)/z),D0),
        ("derivative at base",sp.cancel(sp.diff(R,w).subs(w,0)),D1)]
 saved=[]
 for name,expr,posden in exprs:
  rat=sp.cancel(expr.subs(z,N*v/d));num,den=rat.as_numer_denom()
  if den.subs({a:sp.Rational(3,5),v:sp.Rational(1,2)})<0:num,den=-num,-den
  ratio=sp.cancel(den/posden);assert ratio.is_Rational and ratio>0
  poly=sp.Poly(sp.expand(num.subs(a,sp.Rational(2,5)+3*u/5)),u,v);n=poly.degree(u);m=poly.degree(v)
  cc=[[sum(c*sp.Rational(comb(i,j),comb(n,j))*sp.Rational(comb(k,l),comb(m,l))
           for (j,l),c in poly.terms() if j<=i and l<=k)
       for k in range(m+1)] for i in range(n+1)]
  assert min(c for row in cc for c in row)>0
  saved.append({"name":name,"degrees":[n,m],"positive_denominator_ratio":str(ratio),
   "coefficients":[[str(c) for c in row] for row in cc]})
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round53_certificate.json").write_text(json.dumps(saved,indent=2),encoding="utf-8")
 print("Two complete LEFT-seam polynomial identities; 57 strictly positive rational coefficients.")
if __name__=="__main__":main()

