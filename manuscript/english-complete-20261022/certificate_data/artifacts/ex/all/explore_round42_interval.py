"""An analytic interval proof candidate for positive C, not angle sampling."""
from pathlib import Path
from math import comb
import json
import sympy as sp
def bern(poly,v):
 n=poly.degree()
 return [sum(c*sp.Rational(comb(i,j),comb(n,j)) for (j,),c in poly.terms() if j<=i)
         for i in range(n+1)]
def main():
 a,z,v=sp.symbols("a z v")
 eta0=sp.Rational(1,3);eta1=sp.Rational(9,25);cut=sp.Rational(7,30)
 A=sp.Rational(1,2)-sp.Rational(3,4)*z+sp.Rational(4,3)*z*z
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
 G=(1-z)/(1+z);X=(b+G-2)/(k-h)
 q=lambda t:t/(2-t);F=b-k*(2-G)
 Rupper=eta1+sp.Rational(4,3)*z
 expressions={}
 for label,eta in [("eta0",eta0),("eta1",eta1)]:
  KC=2*eta/(1-eta*eta)
  PP=sp.Poly(sp.cancel((G+(h-1/KC)*X-eta-z)*(a-z)*(1+a*z)),a)
  expressions[label+" concavity"]=-PP.coeff_monomial(a*a)
  expressions[label+" at zero"]=PP.as_expr().subs(a,0)
  expressions[label+" at separator"]=sp.cancel(PP.as_expr().subs(a,A))
 expressions["objective low branch"]=sp.cancel(sp.Rational(7,12)-F.subs(a,A)-q(Rupper))
 expressions["objective high branch"]=sp.cancel(sp.Rational(7,12)-F.subs(a,(1-eta1)/(1+eta1))-q(Rupper))
 expressions["separator above z"]=A-z
 rows=[]
 for name,expr in expressions.items():
  num,den=sp.cancel(expr).as_numer_denom()
  if den.subs(z,cut/2)<0:num,den=-num,-den
  record={"name":name,"expression":str(sp.factor(expr)),"parts":[]}
  for part,p in [("numerator",num),("denominator",den)]:
   poly=sp.Poly(sp.expand(p.subs(z,cut*v)),v);cc=bern(poly,v)
   item={"part":part,"degree":poly.degree(),"minimum":str(min(cc)),
         "nonnegative":all(x>=0 for x in cc),"coefficients":[str(x) for x in cc]}
   record["parts"].append(item)
  rows.append(record)
  print(json.dumps({"name":name,"signs":[x["nonnegative"] for x in record["parts"]],
                    "minima":[x["minimum"] for x in record["parts"]]}),flush=True)
 Path("work/round42_interval_exploration.json").write_text(json.dumps(rows,indent=2),encoding="utf-8")
if __name__=="__main__":main()
