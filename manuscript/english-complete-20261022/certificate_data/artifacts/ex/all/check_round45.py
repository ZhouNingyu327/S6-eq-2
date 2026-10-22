"""Exact algebra for unified top-bridge normalized necessary points."""
from pathlib import Path
import json
import sympy as sp
def main():
 t,z,x,mu,D=sp.symbols("t z x mu D")
 c=(1-t*t)/(1+t*t);s=2*t/(1+t*t);p=(1-z*z)/(1+z*z)
 K=lambda v:2*v/(1-v*v)
 U=lambda v:v-(mu-1)/K(v)
 g=lambda v:(1-v)/(1+v)
 f=-sp.Rational(5,12)+sp.Rational(354,209)*t-sp.Rational(19,12)*t*t
 identities=[]
 def ident(name,expr):
  assert sp.cancel(expr)==0,(name,sp.factor(expr));identities.append(name)
 ident("tau exclusion concave quadratic",
       ((sp.Rational(7,12)*c+sp.Rational(177,209)*s)-1)*(1+t*t)-f)
 ident("top inner trace exact order",
       U(t)-U(z)-(t-z)*(1+(mu-1)/2+(mu-1)/(2*z*t)))
 ident("complementary half angle sine",2*g(t)/(1+g(t)**2)-c)
 ident("complementary half angle tangent",K(g(t))-1/K(t))
 ident("contradictory lower tau threshold",(c+s-1)/s-(1-t))
 ident("actual W first horizontal root",((c+s)*mu-1)/c-(mu-U(g(t))))
 ident("actual horizontal root strict mu increment",
       ((c+s)*mu-1)/c-(1-g(t))-(mu-1)*(c+s)/c)
 ident("actual vertical root strict mu increment",
       ((c+s)*mu-1)/s-(1-t)-(mu-1)*(c+s)/s)
 ident("inner trace derivative",sp.diff(U(x),x)-
       (1+(mu-1)/2+(mu-1)/(2*x*x)))
 B1=(1+t*t)/(1+t);Bmu=(c+s-mu)/(c*s)
 ident("W horizontal feasibility",
       (1-s*mu)/c-(D+(c*mu-1)/s)-(Bmu-D))
 ident("W first square span at mu one",(c+s-1)/(c*s)-B1)
 ident("W square span mu decrease",Bmu-B1+(mu-1)/(c*s))
 ident("W square span derivative",sp.diff(B1,t)-(t*t+2*t-1)/(1+t)**2)
 ident("strict top leg versus span",
       2-1/p-B1.subs(t,z)-z*(z*z-4*z+1)/(1-z*z))
 constants=[]
 def pos(name,expr):
  val=sp.simplify(expr);assert val.is_positive is True,(name,val)
  constants.append({"name":name,"exact":str(val)})
 pos("concave exclusion left endpoint",f.subs(t,sp.Rational(2,5)))
 pos("concave exclusion right endpoint",f.subs(t,sp.Rational(41,79)))
 pos("right-angle order contradiction",sp.Rational(177,418)-sp.Rational(2,5))
 pos("new tau cap improves old",sp.Rational(41,79)-sp.Rational(2,5))
 pos("free W top leg lower bound",2-sp.Rational(241,209))
 pos("uniform normalized top height",1-sp.Rational(2,5))
 pos("strict span gap polynomial at z cap",sp.Rational(4,15)**2-4*sp.Rational(4,15)+1)
 pos("span strictly decreasing through tau cap",1-2*sp.Rational(2,5)-sp.Rational(2,5)**2)
 result={"result":"passed","scope":"W containing QU contributes nothing to target H; whole both-W-bridge mechanism excluded; C must directly contain Q2 or QU; W-QU normalized top seam in original C",
  "algebraic_identities":len(identities),"identity_names":identities,
  "constant_count":len(constants),"constants":constants,"UNSAT":0,
  "not_proved":"The remaining three contact mechanisms, entire G2 or S(6)=2"}
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 (out/"S6_round45_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()
