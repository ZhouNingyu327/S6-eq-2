"""Independent chart reconstruction and new large-a/rotation margins."""
from pathlib import Path
from math import comb,degrees,atan
import sympy as sp,json
def main():
 a,z,u,v,K=sp.symbols("a z u v K");q=lambda t:t/(2-t)
 dz=2*z*z/(1-z*z);b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);G=(1-z)/(1+z)
 FF=b-k*(2-G)
 base=sp.cancel((1-z)**2-FF-q(a+dz)-sp.Rational(8,63))
 charts=[("cos",sp.Rational(1,3),sp.Rational(5,12),a*a,1-2*a*a,sp.Integer(1)),
         ("sin",sp.Rational(5,12),sp.Rational(1,2),(1-a)**2,6*a-1-a*a,1/(1-a))]
 folder=Path("work") if Path("work").is_dir() else Path(".")
 cert=json.loads((folder/"round51_certificate.json").read_text(encoding="utf-8"));count=0;ids=[]
 def ident(name,e):
  assert sp.cancel(e)==0,(name,sp.factor(e));ids.append(name)
 for item,(name,lo,hi,N,d,ratio) in zip(cert,charts):
  expr=sp.cancel(base.subs(z,N*v/d));num,den=expr.as_numer_denom()
  if den.subs({a:(lo+hi)/2,v:sp.Rational(1,2)})<0:num,den=-num,-den
  posden=63*(1-a*a)*d*d*(d+N*v)*((2-a)*d*d-(4-a)*N*N*v*v)
  ident(name+" actual denominator positive factorization",den-posden*ratio)
  assert item["name"]==name and item["positive_denominator_ratio"]==str(ratio)
  poly=sp.Poly(sp.expand(num.subs(a,lo+(hi-lo)*u)),u,v);n=poly.degree(u);m=poly.degree(v)
  assert [n,m]==item["degrees"]
  cc=[[sp.Rational(c) for c in row] for row in item["coefficients"]]
  assert len(cc)==n+1 and all(len(row)==m+1 for row in cc)
  assert min(c for row in cc for c in row)>0
  expansion=sum(cc[i][j]*comb(n,i)*u**i*(1-u)**(n-i)*comb(m,j)*v**j*(1-v)**(m-j)
                for i in range(n+1) for j in range(m+1))
  assert sp.Poly(sp.expand(expansion-poly.as_expr()),u,v).is_zero
  count+=sum(len(row) for row in cc)
 assert count==162
 ident("cos long leg derives valid chart",b-(2-G)-2*(a*a*(1+2*z)-z)/((1-a*a)*(1+z)))
 ident("sin long leg derives valid chart",(1+a*a)/(2*a)-(2-G)-
       ((1-a)**2-z*(6*a-1-a*a))/(2*a*(1+z)))
 Ys=(1-a)**2/(6*a-1-a*a)
 ident("sin cap decreases",sp.diff(Ys,a)-4*(a*a-1)/(6*a-1-a*a)**2)
 ident("negative exceptional q loss",1-sp.Rational(24,19)*K-q(1-sp.Rational(4,5)*K)-
       32*K*(1-3*K)/(19*(5+4*K)))
 constants=[]
 def pos(name,e):
  e=sp.simplify(e);assert e.is_positive is True,(name,e)
  constants.append({"name":name,"exact":str(e)})
 Q=sp.Rational;eta=Q(1,8);km=Q(16,63);dm=Q(2,63)
 pos("small q domain",Q(1,2)-Q(1,3)-Q(1,24)-dm)
 pos("small positive final margin",Q(21,40)-Q(21,41))
 pos("small negative final margin",Q(21,40)-Q(9,28))
 pos("cos chart denominator domain",1-2*Q(5,12)**2)
 pos("cos chart z below4over15",Q(4,15)-Q(25,94))
 pos("sin chart denominator domain",6*Q(5,12)-1-Q(5,12)**2)
 pos("sin chart z below4over15",Q(4,15)-Q(49,191))
 pos("middle q domain including C rotation",1-Q(1,2)-Q(32,209)-dm)
 pos("large first q derivative",Q(5,4)-Q(2,1)/(2-Q(17,24))**2)
 pos("large first bracket",Q(25,224))
 pos("large second bracket",Q(97,60))
 pos("large ordinary q domain",1-Q(240,1463)-Q(1,6))
 pos("extreme z over K cap",Q(1,10)-Q(4,49))
 pos("extreme z absolute cap",Q(1,40)-Q(4,49)*km)
 pos("extreme Delta z ratio",Q(1,19)-2*Q(1,40)/(1-Q(1,40)**2))
 pos("extreme shifted root increment",Q(1,100)-Q(1,190))
 pos("extreme S1 coefficient",Q(1,2)-Q(63,152))
 pos("positive exceptional q domain",Q(1,4)-eta-Q(4,49)-Q(1,300))
 pos("positive exceptional bottom contradiction",Q(7,12)-Q(1,6)-Q(1,7))
 pos("negative shifted right coefficient",Q(21,25)-Q(4,5))
 pos("negative q loss comparison",Q(24,19)-Q(6,5))
 pos("negative final gap",Q(7,10)-Q(9,20))
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 result={"result":"passed","UNSAT":0,"algebraic_identities":len(ids),"identity_names":ids,
  "full_polynomial_reconstructions":2,"positive_rational_coefficients":162,
  "whole_analytic_charts":2,"constant_count":len(constants),"constants":constants,
  "new_closed_subclass":"Right-W bridge: both C rotations eta in [0,1/8]",
  "angle_degrees_max":2*degrees(atan(1/8)),
  "not_proved":"General right-W bridge, full I/II, other remaining mechanisms, G2 or S(6)=2"}
 (out/"S6_round51_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"identity_names","constants"}},indent=2))
if __name__=="__main__":main()

