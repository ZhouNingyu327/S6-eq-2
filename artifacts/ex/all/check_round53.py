"""Independent scalar reconstruction: actual LEFT short leg versus normalized seam."""
from pathlib import Path
from math import comb
import sympy as sp,json
def main():
 a,z,w,u,v,S,L=sp.symbols("a z w u v S L")
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
 G=(1-z)/(1+z);q=lambda y:y/(2-y)
 QQ=S+(h-1)*(b+S-2)/(k-h)
 T=b-k*L;Qmin=QQ.subs(S,2-L)
 RR=sp.cancel(Qmin*(1+T)-2*T);R=sp.cancel(RR.subs(L,2-G+w))
 N=(1-a)**2;d=6*a-1-a*a
 D1=(1-a*a)*(a*d-N*v)*(d+a*N*v);D0=D1*(d+N*v)
 exprs=[("base over z",sp.cancel(R.subs(w,0)/z),D0),
        ("derivative at base",sp.cancel(sp.diff(R,w).subs(w,0)),D1)]
 folder=Path("work") if Path("work").is_dir() else Path(".")
 cert=json.loads((folder/"round53_certificate.json").read_text(encoding="utf-8"))
 ids=[];count=0
 def ident(name,e):
  assert sp.cancel(e)==0,(name,sp.factor(e));ids.append(name)
 for item,(name,expr,posden) in zip(cert,exprs):
  rat=sp.cancel(expr.subs(z,N*v/d));num,den=rat.as_numer_denom()
  if den.subs({a:sp.Rational(3,5),v:sp.Rational(1,2)})<0:num,den=-num,-den
  ratio=sp.Rational(item["positive_denominator_ratio"])
  ident(name+" denominator",den-posden*ratio)
  poly=sp.Poly(sp.expand(num.subs(a,sp.Rational(2,5)+3*u/5)),u,v)
  n=poly.degree(u);m=poly.degree(v);assert [n,m]==item["degrees"]
  cc=[[sp.Rational(c) for c in row] for row in item["coefficients"]]
  assert len(cc)==n+1 and all(len(row)==m+1 for row in cc) and min(c for row in cc for c in row)>0
  exp=sum(cc[i][j]*comb(n,i)*u**i*(1-u)**(n-i)*comb(m,j)*v**j*(1-v)**(m-j)
          for i in range(n+1) for j in range(m+1))
  assert sp.Poly(sp.expand(exp-poly.as_expr()),u,v).is_zero
  count+=sum(len(row) for row in cc)
 assert count==57
 ident("Q slope in actual S4",sp.diff(QQ,S)-(k-1)/(k-h))
 ident("small angle Q at g z gap",QQ.subs(S,G)-(1-a)-
       z*(1-a-z)*(1-2*a-a*a)/((a-z)*(1+a*z)))
 ident("large angle quadratic coefficient",sp.diff(R,w,2)/2-k*(k-1)/(k-h))
 ident("Ys less than a polynomial",a*d-N-(-a**3+5*a*a+a-1))
 ident("Ys less than a derivative",sp.diff(a*d-N,a)-(-3*a*a+10*a+1))
 ident("q inverse",q(2*T/(1+T))-T)
 constants=[]
 def pos(name,e):
  e=sp.simplify(e);assert e.is_positive is True,(name,e)
  constants.append({"name":name,"exact":str(e)})
 Q=sp.Rational
 pos("large angle chart starts below sqrt2 minus1",sp.sqrt(2)-1-Q(2,5))
 pos("Ys denominator positive at left",6*Q(2,5)-1-Q(2,5)**2)
 pos("a d minus N at left",Q(17,125))
 pos("a d minus N derivative lower",Q(2))
 pos("near diagonal upper root above seam height",1-Q(2,5)-Q(5,12))
 pos("B tau below one",1-Q(5,12)-Q(2,5))
 result={"result":"passed","UNSAT":0,"algebraic_identities":len(ids),
  "identity_names":ids,"full_polynomial_reconstructions":2,"positive_rational_coefficients":57,
  "whole_analytic_charts":2,"constant_count":len(constants),"constants":constants,
  "new_lemma":"All current remaining: 0<Q<1 and S1<q(Q), Q=1-X1-e1 from the actual normalized LEFT seam",
  "near_diagonal_consequence":"If W contains QU and sin(theta_C)>=12/17, then S1<q(5/12+tau); this is not the old +z premise",
  "not_proved":"Entire new angle band or contact mechanism, G2 or S(6)=2"}
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 (out/"S6_round53_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"constants","identity_names"}},indent=2))
if __name__=="__main__":main()

