"""Four complete scalar charts, with one Bernstein degree elevation."""
from pathlib import Path
from math import comb
import json
import sympy as sp
def main():
 x,v=sp.symbols("x v")
 K=2*x/(1-x*x);I=3*x*(1-x)/((1+x)*(2-x))
 E=lambda T:I+(K-sp.Rational(17,8))*T+T*T
 rows=[
  ("cosine cap",sp.cancel(E(2*x*x/(1-x*x))/x),sp.Rational(0),sp.Rational(2,5),(12,4)),
  ("fixed middle cap",sp.cancel(E(sp.Rational(2,5))),sp.Rational(2,5),sp.Rational(3,7),(3,3)),
  ("sine cap",sp.cancel(E((1-x)**2/(2*x))),sp.Rational(3,7),sp.Rational(1,2),(5,3)),
  ("sine derivative",sp.cancel(-(K-sp.Rational(17,8)+(1-x)**2/x)),
   sp.Rational(3,7),sp.Rational(1,2),(4,3))]
 saved=[]
 for name,expr,lo,hi,degrees in rows:
  num,den=expr.as_numer_denom()
  if den.subs(x,(lo+hi)/2)<0:num,den=-num,-den
  item={"name":name,"x_range":[str(lo),str(hi)],"expression":str(sp.factor(expr)),"parts":[]}
  for label,p,n in zip(("numerator","denominator"),(num,den),degrees):
   poly=sp.Poly(sp.expand(p.subs(x,lo+(hi-lo)*v)),v);assert n>=poly.degree()
   cc=[sum(c*sp.Rational(comb(i,j),comb(n,j)) for (j,),c in poly.terms() if j<=i)
       for i in range(n+1)]
   assert min(cc)>0
   item["parts"].append({"part":label,"polynomial_degree":poly.degree(),"bernstein_degree":n,
                         "coefficients":[str(c) for c in cc]})
  saved.append(item)
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round46_certificate.json").write_text(json.dumps(saved,indent=2),encoding="utf-8")
 print("Built 4 rational charts, 8 whole polynomial identities and 45 positive rational coefficients.")
if __name__=="__main__":main()
