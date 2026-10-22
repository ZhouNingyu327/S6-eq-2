"""Independent reconstruction: W-QU bottom short-leg sum strictly below one."""
from pathlib import Path
from math import comb
import json
import sympy as sp
def main():
 x,t,u,v=sp.symbols("x t u v");m=(1-t)**2
 g=lambda y:(1-y)/(1+y);K=2*x/(1-x*x)
 P=3*x*(m-x)*(1-x)+2*x*t*(1+m-x)-(2*t-t*t)*(1-x)
 charts=[
  (sp.cancel(P.subs(t,2*x*x/(1-x*x)*v)/x),sp.Rational(0),sp.Rational(1,3),(1-x*x)**3),
  (sp.cancel(P.subs(t,v/4)),sp.Rational(1,3),sp.Rational(1,2),sp.Integer(32)),
  (sp.cancel(P.subs(t,(1-x)**2/(2*x)*v)/(1-x)**2),sp.Rational(1,2),sp.Integer(1),4*x*x),
  (sp.cancel(1-g(sp.Rational(7,12)-x)-g(x)+K/4),
   sp.Rational(1,3),sp.Rational(1,2),2*(1-x*x)*(19-12*x))]
 folder=Path("work") if Path("work").is_dir() else Path(".")
 cert=json.loads((folder/"round47_certificate.json").read_text(encoding="utf-8"))
 count=0
 for item,(expr,lo,hi,positive_den) in zip(cert,charts):
  num,den=expr.as_numer_denom()
  if den.subs({x:(lo+hi)/2,v:sp.Rational(1,2)})<0:num,den=-num,-den
  ratio=sp.cancel(den/positive_den)
  assert ratio.is_Rational and ratio>0 and str(ratio)==item["denominator_ratio"]
  poly=sp.Poly(sp.expand(num.subs(x,lo+(hi-lo)*u)),u,v);n=poly.degree(u);m=poly.degree(v)
  assert item["degrees"]==[n,m]
  cc=[[sp.Rational(c) for c in row] for row in item["coefficients"]]
  assert len(cc)==n+1 and all(len(row)==m+1 for row in cc)
  assert min(c for row in cc for c in row)>0
  exp=sum(cc[i][j]*comb(n,i)*u**i*(1-u)**(n-i)*comb(m,j)*v**j*(1-v)**(m-j)
          for i in range(n+1) for j in range(m+1))
  assert sp.Poly(sp.expand(exp-poly.as_expr()),u,v).is_zero
  count+=sum(len(row) for row in cc)
 assert count==76 and len(cert)==4
 ids=[]
 def ident(name,expr):
  assert sp.cancel(expr)==0,(name,sp.factor(expr));ids.append(name)
 mm=(1-t)**2
 ident("small tau total-short-leg gap",
       (1-g(mm-x)-g(x)+K*t)*(1-x)*(1+x)*(1+mm-x)-P)
 ident("right cosine cap at tau quarter",
       ((1+x*x)/(1-x*x)-sp.Rational(5,4))-(9*x*x-1)/(4*(1-x*x)))
 ident("right sine cap at tau quarter",
       ((1+x*x)/(2*x)-sp.Rational(5,4))-(2*x-1)*(x-2)/(4*x))
 w1,w2,t1,t2,d=sp.symbols("w1 w2 t1 t2 d")
 de=(w2*t1+w1*t2)/(w1+w2)
 ident("common C F chord meets vertical axis",
       w2*(-w1)/(w1+w2)+w1*w2/(w1+w2))
 ident("common chord effective depth",
       (w2*(-t1)+w1*(-t2))/(w1+w2)+de)
 ident("common overlap triangle",
       (-w1)*(d-t2)-(d-t1)*w2+(w1+w2)*(d-de))
 constants=[]
 def pos(name,expr):
  val=sp.simplify(expr);assert val.is_positive is True,(name,val)
  constants.append({"name":name,"exact":str(val)})
 pos("diameter angular sum threshold",sp.Rational(17,12)**2-2)
 pos("middle x low sum bound domain",1+sp.Rational(9,16)-1)
 pos("large tau lower a bound",sp.Rational(7,12)-sp.Rational(1,2))
 result={"result":"passed","scope":"If W contains QU, S1+S2<1, same F bottom chord >2*mu-1>mu>1; F cannot be axis aligned",
  "UNSAT":0,"algebraic_identities":len(ids),"identity_names":ids,
  "full_polynomial_identities":4,"strictly_positive_rational_coefficients":count,
  "whole_analytic_charts":4,"constant_count":len(constants),"constants":constants,
  "not_proved":"Any remaining whole contact mechanism, entire G2 or S(6)=2"}
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 (out/"S6_round47_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()
