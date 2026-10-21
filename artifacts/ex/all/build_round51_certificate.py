"""Two true long-leg charts for the middle-a coupled surplus."""
from pathlib import Path
from math import comb
import sympy as sp,json
def main():
 a,z,u,v=sp.symbols("a z u v");q=lambda t:t/(2-t)
 dz=2*z*z/(1-z*z);b=(1+a*a)/(1-a*a);k=2*a/(1-a*a)
 FF=b-k*(2-(1-z)/(1+z))
 base=sp.cancel((1-z)**2-FF-q(a+dz)-sp.Rational(8,63))
 charts=[("cos",sp.Rational(1,3),sp.Rational(5,12),a*a,1-2*a*a,sp.Integer(1)),
         ("sin",sp.Rational(5,12),sp.Rational(1,2),(1-a)**2,6*a-1-a*a,1/(1-a))]
 saved=[]
 for name,lo,hi,N,d,ratio in charts:
  expr=sp.cancel(base.subs(z,N*v/d));num,den=expr.as_numer_denom()
  if den.subs({a:(lo+hi)/2,v:sp.Rational(1,2)})<0:num,den=-num,-den
  posden=63*(1-a*a)*d*d*(d+N*v)*((2-a)*d*d-(4-a)*N*N*v*v)
  assert sp.cancel(den-posden*ratio)==0
  poly=sp.Poly(sp.expand(num.subs(a,lo+(hi-lo)*u)),u,v);n=poly.degree(u);m=poly.degree(v)
  cc=[[sum(c*sp.Rational(comb(i,j),comb(n,j))*sp.Rational(comb(k,l),comb(m,l))
           for (j,l),c in poly.terms() if j<=i and l<=k)
       for k in range(m+1)] for i in range(n+1)]
  assert min(c for row in cc for c in row)>0
  saved.append({"name":name,"range":[str(lo),str(hi)],"degrees":[n,m],
   "positive_denominator_ratio":str(ratio),"coefficients":[[str(c) for c in row] for row in cc]})
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round51_certificate.json").write_text(json.dumps(saved,indent=2),encoding="utf-8")
 print("Two full analytic charts; 162 strictly positive rational coefficients.")
if __name__=="__main__":main()

