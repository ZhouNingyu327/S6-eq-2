"""Exact algebra for the extended top seam and its contained normalized point."""
from pathlib import Path
import json
import sympy as sp
def main():
 z,t,mu,L,D=sp.symbols("z t mu L D")
 p=(1-z*z)/(1+z*z);q=2*z/(1+z*z)
 c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
 den=sp.factor(c*q+p*s)
 Y=sp.factor((p+c-2*mu*p*c)/den);X=sp.factor((1-q*Y)/p)
 Y1=Y.subs(mu,1);xx1=sp.cancel(X.subs(mu,1)-1);yy1=1-Y1
 xx=sp.cancel(X-mu);yy=mu-Y
 vx=sp.factor((q*c-p*s)/den);vy=sp.factor(1+2*p*c/den)
 N=(t+z)*(1-t*z)+(1-z*z)*(1-t*t)
 w=1-z-t-z*t
 axis=sp.cancel(xx1-yy1*vx/vy)
 g=lambda v:(1-v)/(1+v)
 identities=[]
 def ident(name,expr):
  assert sp.cancel(expr)==0,(name,sp.factor(expr));identities.append(name)
  print("checked "+name,flush=True)
 ident("top intersection on right first upper support",c*(2*mu-X)+s*Y-1)
 ident("height nonnegative from top leg caps",
       p+c-2*mu*p*c-p*c*((1/p-L)+(1/c-D)+(L+D-2*mu)))
 ident("left second lower support",
       (Y-q*(1-p*L))*den-
       (p*c*(L+D-2*mu)+p*((1-c*D)+(p*c-q*s)*(1-p*L))))
 ident("right second lower support",
       (Y-s*(1-c*D))*den-
       (p*c*(L+D-2*mu)+c*((1-p*L)+(p*c-q*s)*(1-c*D))))
 ident("actual to normalized inward height",Y1-Y-2*p*c*(mu-1)/den)
 ident("uniform maximum height when t above z",
       t-Y1-z*(t-z)*(1-t*t)/((z+t)*(1-z*t)))
 ident("uniform maximum height when z above t",
       z-Y1-t*(z-t)*(1-z*z)/((z+t)*(1-z*t)))
 ident("positive cosine of sum",
       (p*c-q*s)*(1+z*z)*(1+t*t)-w*(1+z+t-z*t))
 ident("normalized top point x",
       xx1-2*z*t*(z-t)/((z+t)*(1-z*t)))
 ident("normalized top point y",
       yy1-(1-z)*(1-t)*(2*z*t+z+t)/((z+t)*(1-z*t)))
 ident("actual seam x displacement",xx-xx1-(mu-1)*vx)
 ident("actual seam y displacement",yy-yy1-(mu-1)*vy)
 ident("positive axis denominator",N-(den+2*p*c)*(1+z*z)*(1+t*t)/2)
 ident("axis intercept formula",axis-(t-z)*w/N)
 ident("axis intercept below W lower horizontal root",
       1-g(t)-axis-
       (1-z)*(1+2*t-t*t)*(2*z*t+z+t)/((1+t)*N))
 ident("normalized seam convex combination",
       (yy1/yy)*xx+(1-yy1/yy)*axis-xx1)
 ident("free W tau cap",60*(g(t)-sp.Rational(19,60))*(1+t)-(41-79*t))
 constants=[]
 def pos(name,expr):
  value=sp.simplify(expr);assert value.is_positive is True,(name,value)
  constants.append({"name":name,"exact":str(value)})
 cap=sp.Rational(41,79);zcap=sp.Rational(4,15)
 pos("right leg diameter lower bound",sp.Rational(17,12)**2-2)
 pos("cosine left above common cap",sp.Rational(209,241)-cap)
 pos("cosine right above common cap",sp.Rational(2280,3961)-cap)
 pos("positive sum-angle margin",1-zcap-cap-zcap*cap)
 pos("maximum height below target center half width",1-cap)
 pos("left halfangle below tau cap",cap-zcap)
 pos("small-z lower-root comparison",sp.Rational(1,2)-zcap*zcap)
 assert sp.Rational(7,12)-zcap==sp.Rational(19,60)
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 result={"result":"passed","scope":"W containing QU forces top seam in original C without a TOPmid assumption; W also containing C right root forces normalized top seam in original C",
  "algebraic_identities":len(identities),"identity_names":identities,
  "constant_count":len(constants),"constants":constants,"UNSAT":0,
  "angle_sampling":False,"subdivision":False,
  "not_proved":"Any whole new contact family, entire G2 or S(6)=2"}
 (out/"S6_round44_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()
