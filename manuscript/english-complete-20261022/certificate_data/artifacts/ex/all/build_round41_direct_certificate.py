"""Analytically chosen whole rectangles for the diagonal direct-contact lemma."""
from pathlib import Path
import json
from math import comb
import sympy as sp
def bernstein(poly):
 n,m=poly.degree_list()
 return [[sum(c*sp.Rational(comb(i,p),comb(n,p))*sp.Rational(comb(j,q),comb(m,q))
              for (p,q),c in poly.terms() if p<=i and q<=j)
          for j in range(m+1)] for i in range(n+1)]
def main():
 a,z,u,v=sp.symbols("a z u v")
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
 q=lambda t:t/(2-t);Q=lambda S:S+(h-1)*(b+S-2)/(k-h)
 T=sp.Rational(7,12)-q(sp.Rational(5,12)+z)
 R2=Q(2-(b-T)/k)-z-sp.Rational(5,12)
 P2=sp.Poly(sp.cancel(R2*24*a*(a-z)*(1+a*z)*(19-12*z)),a,z)
 P=sp.Poly(sp.cancel((Q((1-z)/(1+z))-z-sp.Rational(5,12))*12*(a-z)*(1+a*z)),a,z)
 F=b-k*(2-(1-z)/(1+z))
 # N positive iff F>=T; this sign convention follows from positive denominators.
 N=sp.Poly(sp.cancel((F-T)*12*(1-a*a)*(1+z)*(19-12*z)),a,z)
 A=(27-16*z)/60
 charts=[
  ("Ka>=1 low z R2",P2,sp.Rational(2,5)+(sp.Rational(155,301)-sp.Rational(2,5))*u,
   sp.Rational(3,2)*(sp.Rational(155,301)-a)*v),
  ("Ka<=1 very low z",P,sp.Rational(3,7)*u,sp.Rational(1,7)*v),
  ("Ka<=1 low a",P,sp.Rational(2,5)*u,sp.Rational(1,7)+(sp.Rational(3,16)-sp.Rational(1,7))*v),
  ("Ka<=1 high a objective",-N,sp.Rational(2,5)+(sp.Rational(3,7)-sp.Rational(2,5))*u,
   sp.Rational(1,7)+(sp.Rational(3,16)-sp.Rational(1,7))*v),
  ("Ka<=1 separator lower a",P,A*u,sp.Rational(3,16)+(sp.Rational(2,9)-sp.Rational(3,16))*v),
  ("Ka<=1 separator upper a",-N,A+(sp.Rational(3,7)-A)*u,
   sp.Rational(3,16)+(sp.Rational(2,9)-sp.Rational(3,16))*v),
 ]
 rows=[]
 for name,poly,aa,zz in charts:
  # The z chart may depend on a; then apply it before the a chart.
  if zz.has(a):
   zden=sp.denom(sp.cancel(zz))
   E0=sp.cancel(poly.as_expr().subs(z,zz)*zden**poly.degree(z))
   E=sp.Poly(sp.expand(E0.subs(a,aa)),u,v)
  else:
   aa=sp.cancel(aa)
   a_den=sp.denom(aa)
   E0=sp.cancel(poly.as_expr().subs(a,aa)*a_den**poly.degree(a))
   E=sp.Poly(sp.expand(E0.subs(z,zz)),u,v)
  coeff=bernstein(E);mini=min(x for line in coeff for x in line)
  row={"chart":name,"degrees":list(E.degree_list()),"minimum":str(mini),
       "all_nonnegative":bool(mini>=0),"coefficients":[[str(x) for x in line] for line in coeff]}
  rows.append(row);print(json.dumps({k:v for k,v in row.items() if k!="coefficients"}),flush=True)
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round41_direct_certificate.json").write_text(json.dumps(rows,indent=2),encoding="utf-8")
if __name__=="__main__":main()
