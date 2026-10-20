"""Independent rectangle reconstruction and all new small-angle margins."""
from pathlib import Path
from math import comb,degrees,atan
import sympy as sp,json
def main():
 a,z,u,v=sp.symbols("a z u v");q=lambda t:t/(2-t)
 dz=2*z*z/(1-z*z);b=(1+a*a)/(1-a*a);k=2*a/(1-a*a)
 FF=b-k*(2-(1-z)/(1+z))
 expr=sp.cancel((1-z)**2-FF-q(a+dz)-sp.Rational(8,255))
 num,den=expr.as_numer_denom()
 if den.subs({a:sp.Rational(5,12),z:sp.Rational(2,15)})<0:num,den=-num,-den
 positive_den=255*(1-a*a)*(1+z)*((2-a)*(1-z*z)-2*z*z)
 assert sp.cancel(den-positive_den)==0
 folder=Path("work") if Path("work").is_dir() else Path(".")
 cert=json.loads((folder/"round50_certificate.json").read_text(encoding="utf-8"))
 poly=sp.Poly(sp.expand(num.subs({a:sp.Rational(1,3)+u/6,z:4*v/15})),u,v)
 n=poly.degree(u);m=poly.degree(v);assert [n,m]==cert["degrees"]==[3,5]
 cc=[[sp.Rational(c) for c in row] for row in cert["coefficients"]]
 assert len(cc)==4 and all(len(row)==6 for row in cc) and min(c for row in cc for c in row)>0
 expansion=sum(cc[i][j]*comb(n,i)*u**i*(1-u)**(n-i)*comb(m,j)*v**j*(1-v)**(m-j)
               for i in range(n+1) for j in range(m+1))
 assert sp.Poly(sp.expand(expansion-poly.as_expr()),u,v).is_zero
 ids=[]
 def ident(name,e):
  assert sp.cancel(e)==0,(name,sp.factor(e));ids.append(name)
 ident("positive denominator factorization",den-positive_den)
 ident("extreme z over K cap",sp.Rational(576,7)*sp.Rational(1,16)**2*sp.Rational(32,255)-sp.Rational(24,595))
 ident("extreme S1 coefficient",sp.Rational(6,16)/(1-sp.Rational(12,255))-sp.Rational(85,216))
 constants=[]
 def pos(name,e):
  e=sp.simplify(e);assert e.is_positive is True,(name,e)
  constants.append({"name":name,"exact":str(e)})
 Q=sp.Rational;dm=Q(2,255);km=Q(32,255);eta=Q(1,16)
 pos("K cap",Q(1,7)-km)
 pos("small all q domain",Q(1,2)-Q(1,3)-Q(1,24)-dm)
 pos("small positive C L T coefficient",1-Q(1,7)-eta-Q(3,4))
 pos("small negative C L T coefficient",1-Q(1,3)-eta-Q(1,2))
 pos("small positive final margin",Q(21,40)-Q(1,4))
 pos("small negative final margin",Q(21,40)-Q(9,56))
 pos("middle positive denominator",Q(3,2)*(1-Q(4,15)**2)-2*Q(4,15)**2)
 pos("middle q with delta below one",1-Q(1,2)-Q(32,209)-dm)
 pos("large ordinary q domain",1-Q(240,1463)-Q(1,12))
 pos("large ordinary gamma margin",Q(92,1463))
 pos("extreme z K coefficient",Q(1,20)-Q(24,595))
 pos("extreme Delta z over z cap",Q(1,50)-2*Q(1,140)/(1-Q(1,140)**2))
 pos("extreme S1 coefficient",Q(2,5)-Q(85,216))
 pos("positive extreme right argument",Q(1,4)-eta-Q(1,20)-Q(1,1000))
 pos("positive extreme bottom contradiction",Q(7,12)-Q(2,35)-Q(1,7))
 pos("negative extreme r coefficient",1-eta-Q(1,140)-Q(93,100))
 pos("negative shifted r coefficient",Q(929,1000)-Q(9,10))
 pos("negative q loss K cap",Q(8,9)-km)
 pos("negative F square lower coefficient",Q(1,4)-2*(Q(1,20)+eta))
 pos("negative final gap",Q(3,5)-Q(1,4))
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 result={"result":"passed","UNSAT":0,"algebraic_identities":len(ids),"identity_names":ids,
  "full_polynomial_identities":1,"strictly_positive_rational_coefficients":24,
  "whole_bivariate_rectangles":1,"constant_count":len(constants),"constants":constants,
  "new_closed_subclass":"Right-W bridge: both C rotations eta in [0,1/16]",
  "angle_degrees_max":2*degrees(atan(1/16)),
  "scope":"Enlarges round49 right-W-bridge small C angle to approx 7.152669 degrees, using coupled middle-a surplus",
  "not_proved":"Whole right-W bridge, round48 I/II, other whole remaining mechanisms, G2 or S(6)=2"}
 (out/"S6_round50_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()

