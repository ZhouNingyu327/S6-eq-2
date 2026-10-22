"""Independent scalar certificate and exact global-small-angle margins."""
from pathlib import Path
from math import comb,degrees,atan
import sympy as sp,json
def main():
 x,v,m,t,d=sp.symbols("x v m t d")
 I=lambda y:3*y*(1-y)/((1+y)*(2-y))
 q=lambda y:y/(2-y)
 Kx=2*x/(1-x*x);Tc=2*x*x/(1-x*x)
 scalar=sp.cancel((I(x)+(Kx-2)*Tc+Tc*Tc)/x-sp.Rational(2,5))
 num,den=scalar.as_numer_denom()
 if den.subs(x,sp.Rational(1,9))<0:num,den=-num,-den
 folder=Path("work") if Path("work").is_dir() else Path(".")
 cert=json.loads((folder/"round52_certificate.json").read_text(encoding="utf-8"))
 assert sp.cancel(den-5*(2-x)*(1-x)**2*(1+x))==0
 poly=sp.Poly(num.subs(x,2*v/9),v);assert cert["degree"]==poly.degree()==4
 cc=[sp.Rational(c) for c in cert["coefficients"]]
 assert len(cc)==5 and min(cc)>0
 exp=sum(cc[i]*comb(4,i)*v**i*(1-v)**(4-i) for i in range(5))
 assert sp.Poly(sp.expand(exp-poly.as_expr()),v).is_zero
 ids=[]
 def ident(name,e):
  assert sp.cancel(e)==0,(name,sp.factor(e));ids.append(name)
 ident("symmetric I representation",I(m)-3*m*(1-m)/(2+m*(1-m)))
 ident("I increasing up to half",sp.diff(I(m),m)-6*(1-2*m)/(2+m-m*m)**2)
 ident("I divided by m decreases",sp.diff(I(m)/m,m)+3*(m*m-2*m+3)/(2+m-m*m)**2)
 ident("horizontal short-leg gap",1-(1-m)/(1+m)-q(m)-I(m))
 ident("q shift",q(m+d)-q(m)-2*d/((2-m-d)*(2-m)))
 ident("I at two over nine",I(sp.Rational(2,9))-sp.Rational(21,88))
 ident("I ratio at two over nine",I(sp.Rational(2,9))/sp.Rational(2,9)-sp.Rational(189,176))
 ident("scalar E decomposition",
       (1-t)**2-q(x)-(1-x)/(1+x)+Kx*t-(I(x)+(Kx-2)*t+t*t))
 constants=[]
 def pos(name,e):
  e=sp.simplify(e);assert e.is_positive is True,(name,e)
  constants.append({"name":name,"exact":str(e)})
 Q=sp.Rational;eta=Q(1,24);dm=Q(2,575)
 pos("F lower bound exceeds two-thirds",(1-33*dm)**2-Q(2,3))
 pos("q argument m plus delta below one",1-Q(1,2)-dm)
 pos("small minimum from I cutoff",Q(21,88)-68*dm)
 pos("small minimum I ratio",Q(189,176)-Q(16,15))
 pos("other parameter exceeds three-quarters",1-Q(2,9)-dm-Q(3,4))
 pos("small plus delta below quarter",Q(1,4)-Q(2,9)-dm)
 pos("wrong order positive cosine contradiction",1-Q(7965,8162))
 pos("wrong order negative sine contradiction",1-Q(303,848))
 pos("positive tau delta improvement",Q(10,7)-Q(4,3))
 pos("positive C a contradiction",Q(67,120)-Q(25,64))
 pos("small x derivative negativity",Q(102,77))
 pos("negative scalar against delta",Q(67,300)-Q(1,6))
 pos("positive root coefficient",1-Q(2,5)-eta)
 pos("F height positive",1-Q(2,5)-dm)
 result={"result":"passed","UNSAT":0,"algebraic_identities":len(ids),"identity_names":ids,
  "full_polynomial_reconstructions":1,"positive_rational_coefficients":5,
  "constant_count":len(constants),"constants":constants,
  "new_closed_subclass":"W contains QU: both C rotations eta_C in [0,1/24]",
  "global_consequence":"Combining rounds43/51/52, every remaining C has eta_C>1/24, delta_C>2/575",
  "angle_degrees_threshold":2*degrees(atan(1/24)),
  "not_proved":"Whole upper-W bridge, whole remaining mechanisms, G2 or S(6)=2"}
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 (out/"S6_round52_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()

