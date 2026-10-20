"""Independent round42 polynomial reconstruction and exact geometric algebra."""
from pathlib import Path
from math import comb
import json
import sympy as sp
import z3

def main():
 a,z,eta,mu,S,e,X,l,u,v=sp.symbols("a z eta mu S e X l u v")
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
 G=(1-z)/(1+z);Xg=(b+G-2)/(k-h)
 eta0=sp.Rational(1,3);eta1=sp.Rational(9,25);cut=sp.Rational(7,30)
 A=sp.Rational(1,2)-sp.Rational(3,4)*z+sp.Rational(4,3)*z*z
 F=b-k*(2-G);q=lambda t:t/(2-t);R=eta1+sp.Rational(4,3)*z
 expressions=[]
 for ee in (eta0,eta1):
  KC=2*ee/(1-ee*ee)
  P=sp.Poly(sp.cancel((G+(h-1/KC)*Xg-ee-z)*(a-z)*(1+a*z)),a)
  expressions.extend([-P.coeff_monomial(a*a),P.as_expr().subs(a,0),
                      sp.cancel(P.as_expr().subs(a,A))])
 expressions.extend([sp.cancel(sp.Rational(7,12)-F.subs(a,A)-q(R)),
                     sp.cancel(sp.Rational(7,12)-F.subs(a,sp.Rational(8,17))-q(R)),A-z])
 folder=Path("work") if Path("work").is_dir() else Path(".")
 saved=json.loads((folder/"round42_interval_certificate.json").read_text(encoding="utf-8"))
 assert len(saved)==len(expressions)==9
 count=0;rebuilds=[]
 for row,expr in zip(saved,expressions):
  num,den=sp.cancel(expr).as_numer_denom()
  if den.subs(z,cut/2)<0:num,den=-num,-den
  for item,p in zip(row["parts"],(num,den)):
   poly=sp.Poly(sp.expand(p.subs(z,cut*v)),v);n=poly.degree()
   cc=[sp.Rational(c) for c in item["coefficients"]]
   assert len(cc)==n+1 and item["degree"]==n
   assert all(c>=0 for c in cc)
   if item["part"]=="denominator":assert min(cc)>0
   if item["part"]=="numerator" and row["name"] in {
     "eta0 concavity","eta1 concavity","objective low branch",
     "objective high branch","separator above z"}:assert min(cc)>0
   expansion=sum(cc[i]*comb(n,i)*v**i*(1-v)**(n-i) for i in range(n+1))
   assert sp.Poly(sp.expand(expansion-poly.as_expr()),v).is_zero
   count+=len(cc);rebuilds.append({"name":row["name"],"part":item["part"],
                                  "degree":n,"minimum":str(min(cc))})
 assert count==56 and len(rebuilds)==18
 ids=[]
 def ident(name,expr):
  assert sp.cancel(expr)==0,(name,sp.factor(expr));ids.append(name)
 XX=(b+S-2*mu)/(k-h);EE=mu-S-h*XX
 XX1=XX.subs(mu,1);EE1=EE.subs(mu,1)
 lm=mu-a+(mu-1)/k
 ident("normalized seam positive height difference",
       EE-EE1-(mu-1)*(1+2*h/(k-h)))
 ident("actual lower-corner edge through axis root",
       mu-XX-lm-EE/k)
 ident("normalized lower-corner edge through axis root",
       1-XX1-(1-a)-EE1/k)
 ident("axis-root translation gap",lm-(1-a)-(mu-1)*(1+1/k))
 ident("normalized seam upper horizontal bound",
       (k-h)*(XX1-a)-(S-1+a*h))
 ident("normalized height comparison with short leg",
       EE1-(1-S-h*XX1))
 ident("short leg limiting height identity",1-G-h*(1-z))
 ident("contained horizontal slice convex combination",
       (-lm+(EE1/EE)*(-mu+XX+lm))-(-lm-EE1/k))
 ident("normalized seam horizontal position gap",
       (lm+EE1/k)-(1-XX1)-(mu-1)*(1+1/k))
 KC=2*eta/(1-eta*eta)
 ident("positive C normalized seam projection",
       (1-XX1)+(KC*((1-z)-EE1))-
       (1-KC+KC*(S+(h-1/KC)*XX1)+KC*(1-z)))
 # Equivalent scalar condition from c*rho+s(u-e)<=1.
 ident("C half-angle intercept ratio",
       ((1+eta*eta)/(1-eta*eta)-1)/KC-eta)
 ident("C complementary half-angle",2*((1-eta)/(1+eta))/
       (1-((1-eta)/(1+eta))**2)-1/KC)
 HH=eta*(1-Xg/2)+Xg/(2*eta)
 ident("concavity parameter identity",
       sp.diff(HH,eta,2)-Xg/eta**3)
 ident("seam comparison is concave in eta",
       G+(h-1/KC)*Xg-eta-z-
       (G+h*Xg-z-HH))
 constants=[]
 def positive(name,expr):
  expr=sp.simplify(expr);assert expr.is_positive is True,(name,expr)
  constants.append({"name":name,"exact":str(expr)})
 positive("global upper root exceeds actual seam height cap",
          sp.Rational(38,79)-sp.Rational(5,12))
 positive("rational diameter threshold",sp.Rational(17,12)**2-2)
 positive("uniform right cap below one",1-(eta1+sp.Rational(4,3)*sp.Rational(4,15)))
 positive("Phi composite decreasing",
          sp.Rational(1575,722)-sp.Rational(135000,83521))
 endpoint=sp.Rational(51,1369)*(37-4*sp.sqrt(77))+sp.Rational(151,299)
 positive("large-z Phi endpoint below 7/12",sp.Rational(7,12)-endpoint)
 positive("high branch half angle",sp.Rational(1,1)-eta1)
 queries=[]
 def linear(name,cs):
  sol=z3.SolverFor("QF_LRA");sol.add(*cs);ans=sol.check();assert ans==z3.unsat
  queries.append({"name":name,"theory":"QF_LRA","result":str(ans)})
 ep,em,top,lp,lone,rr,rl,KK=z3.Reals("ep em top lp lone rr rl KK")
 linear("normalized seam is on contained horizontal slice",[
  em>ep,ep>0,top>em,lp>lone,lone>0,KK>0,
  rl==lp+ep,rr==lone+ep,z3.Or(rr<=0,rr>=rl)])
 ss,qq,total=z3.Reals("ss qq total")
 linear("same F bottom chord contradiction",[
  total>z3.Q(7,12),total<ss+qq,ss+qq<=z3.Q(7,12)])
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 result={"result":"passed","scope":"universal normalized forced seam; positive-C double direct contact excluded for eta in [1/3,9/25]",
  "UNSAT":len(queries),"NRA":0,"LRA":len(queries),"queries":queries,
  "algebraic_identities":len(ids),"identity_names":ids,
  "full_polynomial_identities":len(rebuilds),"nonnegative_rational_coefficients":count,
  "polynomial_checks":rebuilds,"constants":constants,"constant_count":len(constants),
  "not_proved":"negative C rotation in this new interval, the other contacts, all C angles, entire G2 or S(6)=2"}
 (out/"S6_round42_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in
       {"polynomial_checks","constants","identity_names","queries"}},indent=2))
if __name__=="__main__":main()
