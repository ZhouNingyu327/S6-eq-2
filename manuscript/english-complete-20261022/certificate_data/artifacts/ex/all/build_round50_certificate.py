"""Full middle-a rectangle, retaining coupling between a and Delta_z."""
from pathlib import Path
from math import comb
import sympy as sp,json
def main():
 a,z,u,v=sp.symbols("a z u v");q=lambda t:t/(2-t)
 dz=2*z*z/(1-z*z);b=(1+a*a)/(1-a*a);k=2*a/(1-a*a)
 FF=b-k*(2-(1-z)/(1+z))
 expr=sp.cancel((1-z)**2-FF-q(a+dz)-sp.Rational(8,255))
 num,den=expr.as_numer_denom()
 if den.subs({a:sp.Rational(5,12),z:sp.Rational(2,15)})<0:num,den=-num,-den
 positive_den=255*(1-a*a)*(1+z)*((2-a)*(1-z*z)-2*z*z)
 assert sp.cancel(den/positive_den)==1
 poly=sp.Poly(sp.expand(num.subs({a:sp.Rational(1,3)+u/6,z:4*v/15})),u,v)
 n=poly.degree(u);m=poly.degree(v)
 cc=[[sum(c*sp.Rational(comb(i,j),comb(n,j))*sp.Rational(comb(k,l),comb(m,l))
           for (j,l),c in poly.terms() if j<=i and l<=k)
       for k in range(m+1)] for i in range(n+1)]
 assert min(c for row in cc for c in row)>0
 result={"degrees":[n,m],"map":"a=1/3+u/6,z=4v/15; (u,v) in [0,1]^2",
  "positive_denominator":str(positive_den),
  "coefficients":[[str(c) for c in row] for row in cc]}
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round50_certificate.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print("One full two-variable identity; 24 strictly positive rational coefficients.")
if __name__=="__main__":main()

