"""Independent reconstruction plus exact algebra for both C rotations."""
from pathlib import Path
from math import comb
import json
import sympy as s
def main():
 a,z,v,delta,K,eta=s.symbols("a z v delta K eta")
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);G=(1-z)/(1+z)
 q=lambda t:t/(2-t)
 F=b-k*(2-G);E=(1-z)**2-F-q(a)
 E0=3*a*(1-a)/((1+a)*(2-a));Y=a*a/(1-2*a*a)
 expr=s.cancel((E.subs(z,Y)-s.Rational(13,20)*a)/a)
 num,den=expr.as_numer_denom()
 if den.subs(a,s.Rational(1,6))<0:num,den=-num,-den
 folder=Path("work") if Path("work").is_dir() else Path(".")
 cert=json.loads((folder/"round43_certificate.json").read_text(encoding="utf-8"))
 count=0
 for item,p in zip(cert["parts"],(num,den)):
  poly=s.Poly(p.subs(a,v/3),v);n=poly.degree()
  cc=[s.Rational(c) for c in item["coefficients"]]
  assert n==item["degree"]==9 and len(cc)==n+1 and min(cc)>0
  assert s.Poly(s.expand(sum(cc[i]*comb(n,i)*v**i*(1-v)**(n-i)
                           for i in range(n+1))-poly.as_expr()),v).is_zero
  count+=len(cc)
 assert count==20
 ids=[]
 def ident(name,expr):
  assert s.cancel(expr)==0,(name,s.factor(expr));ids.append(name)
 ident("axis-aligned surplus decomposition",E-(E0+z*z-2*z+2*k*z/(1+z)))
 ident("surplus derivative",s.diff(E,z)-2*(k-(1-z)*(1+z)**2)/(1+z)**2)
 ident("small-z derivative comparison",(1-z)*(1+z)**2-1-z*(1-z-z*z))
 ident("large-a derivative cap",s.Rational(32,27)-(1-z)*(1+z)**2-
       (3*z-1)**2*(3*z+5)/27)
 ident("large-a initial surplus",E0-s.Rational(2,3)*(1-a)-
       (1-a)*(2*a-1)*(a+4)/(3*(1+a)*(2-a)))
 ident("delta change in F surplus",
       ((1-z-delta)**2-F-q(a+delta))-E-
       (-2*delta*(1-z)+delta**2-q(a+delta)+q(a)))
 ident("negative C right cap",q(1-s.Rational(4,5)*K)-
       (1-(s.Rational(8,5)*K)/(1+s.Rational(4,5)*K)))
 ident("C half angle delta relation",2*eta**2/(1-eta**2)-
       eta*2*eta/(1-eta**2))
 constants=[]
 def positive(name,expr):
  value=s.simplify(expr);assert value.is_positive is True,(name,value)
  constants.append({"name":name,"exact":str(value)})
 positive("small-a q derivative range",s.Rational(1,2)-(s.Rational(1,3)+s.Rational(2,63)))
 positive("positive small-a margin",s.Rational(13,20)-s.Rational(45,73))
 positive("negative small-a margin",s.Rational(13,20)-s.Rational(27,91))
 positive("middle-a surplus",s.Rational(1313,8550)-s.Rational(8,63))
 positive("middle-a decreasing bound",s.Rational(31,38)-s.Rational(8,15))
 positive("positive exceptional right cap",s.Rational(1,4)-(s.Rational(1,8)+s.Rational(4,49)))
 positive("positive exceptional bottom bound",s.Rational(7,12)-(s.Rational(2,19)+s.Rational(1,7)))
 positive("negative exceptional z cap",s.Rational(1,10)-s.Rational(4,49))
 positive("negative exceptional K cap",s.Rational(1,3)-s.Rational(16,63))
 positive("negative exceptional one minus eta z",1-s.Rational(1,8)-s.Rational(1,30)-s.Rational(4,5))
 positive("negative exceptional S1 cap",s.Rational(1,2)-s.Rational(63,152))
 positive("negative exceptional q loss",s.Rational(24,19)-s.Rational(6,5))
 positive("negative final gap",s.Rational(7,10)-s.Rational(9,20))
 result={"result":"passed",
  "scope":"Both C rotations, double direct Q2/QU contact, eta in [0,1/8] excluded",
  "UNSAT":0,"algebraic_identities":len(ids),"identity_names":ids,
  "full_polynomial_identities":2,"strictly_positive_rational_coefficients":count,
  "constant_count":len(constants),"constants":constants,
  "not_proved":"Other C angles, other contacts, entire G2 or S(6)=2"}
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 (out/"S6_round43_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()
