"""Independent exact checks: C rotation separation and corner-frontier geometry."""
from pathlib import Path
from math import comb
import json
import sympy as sp
def main():
 a,x,z,t,delta,mu,L,T,v=sp.symbols("a x z t delta mu L T v")
 q=lambda y:y/(2-y);g=lambda y:(1-y)/(1+y)
 KK=lambda y:2*y/(1-y*y)
 bb=lambda y:(1+y*y)/(1-y*y)
 K=KK(x);I=3*x*(1-x)/((1+x)*(2-x))
 E0=(1-t)**2-q(x)-g(x)+K*t
 E=lambda T:I+(K-sp.Rational(17,8))*T+T*T
 rows=[
  (sp.cancel(E(2*x*x/(1-x*x))/x),sp.Rational(0),sp.Rational(2,5),(12,4)),
  (sp.cancel(E(sp.Rational(2,5))),sp.Rational(2,5),sp.Rational(3,7),(3,3)),
  (sp.cancel(E((1-x)**2/(2*x))),sp.Rational(3,7),sp.Rational(1,2),(5,3)),
  (sp.cancel(-(K-sp.Rational(17,8)+(1-x)**2/x)),sp.Rational(3,7),sp.Rational(1,2),(4,3))]
 folder=Path("work") if Path("work").is_dir() else Path(".")
 cert=json.loads((folder/"round46_certificate.json").read_text(encoding="utf-8"))
 assert len(cert)==len(rows)==4
 count=0;polys=0
 for item,(expr,lo,hi,degrees) in zip(cert,rows):
  num,den=expr.as_numer_denom()
  if den.subs(x,(lo+hi)/2)<0:num,den=-num,-den
  for part,p,n in zip(item["parts"],(num,den),degrees):
   po=sp.Poly(sp.expand(p.subs(x,lo+(hi-lo)*v)),v)
   cc=[sp.Rational(c) for c in part["coefficients"]]
   assert n==part["bernstein_degree"] and po.degree()==part["polynomial_degree"]
   assert len(cc)==n+1 and min(cc)>0
   assert sp.Poly(sp.expand(sum(cc[i]*comb(n,i)*v**i*(1-v)**(n-i)
                               for i in range(n+1))-po.as_expr()),v).is_zero
   count+=len(cc);polys+=1
 assert (count,polys)==(45,8)
 ids=[]
 def ident(name,expr):
  assert sp.cancel(expr)==0,(name,sp.factor(expr));ids.append(name)
 ident("upper bridge long right leg",
       2-bb(t)+KK(t)*(2-bb(z))-(1+t)-
       t*((1-t)**2-2*(bb(z)-1))/(1-t*t))
 ident("common surplus decomposition",E0-(I+(K-2)*t+t*t))
 ident("positive surplus target",E0-t/8-E(t))
 ident("rotation loss",
       ((1-t-delta)**2-q(x+delta)-g(x)+K*t)-E0-
       (-2*delta*(1-t)+delta**2-q(x+delta)+q(x)))
 ident("complementary short leg",g(1-x-delta)-q(x+delta))
 p=(1-a*a)/(1+a*a);s=2*a/(1+a*a);ka=s/p
 lm=mu-a+(mu-1)/ka;S=(1-s*L)/p
 Xv=s+p*(1-s*L);Yv=p-s*(1-s*L)
 ident("V1 H endpoint first upper",s*(mu-lm)+p*mu-1)
 ident("V1 inner vertex first upper",s*Xv+p*Yv-1)
 ident("V1 inner vertex second upper",p*Xv-s*Yv-(1-s*L))
 ident("V1 vertex strict negative x decomposition",
       Xv-mu-(-(1-p)*(1-s)-(mu-1)*(1+p*s)-p*s*(L-mu)))
 ident("V1 vertex above bottom",
       Yv-(p+s-1)-((1-s)**2+s*s*(L-1)))
 ident("V1 vertex below H",mu-Yv-(mu-p)-s*(1-s*L))
 xx1=-lm+T/ka
 ident("first frontier branch",s*(xx1+mu)+p*(mu-T)-1)
 xx2=-mu+S+ka*(mu-T)
 ident("second frontier branch",p*(xx2+mu)-s*(mu-T)-(1-s*L))
 ident("frontier branches at vertex",(xx1-xx2).subs(T,mu-Yv))
 constants=[]
 def pos(name,expr):
  val=sp.simplify(expr);assert val.is_positive is True,(name,val)
  constants.append({"name":name,"exact":str(val)})
 pos("uniform right leg excess",sp.Rational(9,25)-sp.Rational(64,209))
 pos("cosine derivative negative",sp.Rational(17,8)-sp.Rational(36,21))
 pos("middle derivative negative",sp.Rational(17,8)-sp.Rational(21,20)-sp.Rational(4,5))
 pos("large x complete square margin",sp.Rational(3,10)-sp.Rational(19,48)**2)
 pos("very large x coefficient",sp.Rational(12,5)-sp.Rational(17,8))
 pos("delta maximum",sp.Rational(1,80))
 pos("low x plus delta below one",1-sp.Rational(1,2)-sp.Rational(1,80))
 result={"result":"passed",
  "scope":"When W contains QU, L2>1+tau and C rotation delta>tau/32; universal left C/F/V1 junction, and right C/F/V2 junction when W-QU",
  "UNSAT":0,"algebraic_identities":len(ids),"full_polynomial_identities":polys,
  "strictly_positive_rational_coefficients":count,"whole_rational_charts":4,
  "constant_count":len(constants),"identity_names":ids,"constants":constants,
  "not_proved":"Any remaining whole contact mechanism, entire G2 or S(6)=2"}
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 (out/"S6_round46_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()
