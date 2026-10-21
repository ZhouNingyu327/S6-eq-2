"""Exact certificates for the actual upper-W bridge exclusion."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
t,x,u,v=s.symbols("t x u v")
k=lambda a:2*a/(1-a*a)
b=lambda a:(1+a*a)/(1-a*a)
q=lambda a:a/(2-a)
g=lambda a:(1-a)/(1+a)
KAP=R(71,50);H=R(7,12);beta=R(177,209)
Bt=1+k(t)*(1-(b(t)-1)-t)
Bc=1+k(t)*(beta-t)
def joint(B):
 S=b(x)-k(x)*B
 return s.cancel((B*(k(x)+1)-b(x)*(1+k(t))-KAP*(k(x)-k(t)))*(1+H-S)
                 +2*(H-S)*(k(x)-k(t)))
def specs():
 return [
 ("small_tau",H-2*q(KAP-1+t)+k(2-KAP-t)*(Bt-1),[(t,R(0),R(1,6))]),
 ("transition_leg",Bt-R(5,4),[(t,R(1,6),R(1,5))]),
 ("middle_angle_cut",H-q(KAP-1+t)-g(R(9,20))+k(R(9,20))*(Bc-1),[(t,R(1,5),R(3,10))]),
 ("transition_joint",joint(Bt),[(t,R(1,6),R(1,5)),(x,R(19,50),R(1,2))]),
 ("middle_joint",joint(Bc),[(t,R(1,5),R(3,10)),(x,R(1,3),R(9,20))]),
 ("end_joint",joint(Bc),[(t,R(3,10),R(2,5)),(x,R(3,8),R(11,25))])]
def main():
 saved=[]
 for name,expr,axes in specs():
  num,den=s.cancel(expr).as_numer_denom()
  mid={a:(lo+hi)/2 for a,lo,hi in axes}
  if den.subs(mid)<0:num,den=-num,-den
  vs=[u,v][:len(axes)]
  poly=s.Poly(s.expand(num.subs({a:lo+(hi-lo)*w for (a,lo,hi),w in zip(axes,vs)})),*vs)
  ds=poly.degree_list()
  if len(vs)==1:
   n=ds[0]
   cc=[sum(c*R(comb(i,j[0]),comb(n,j[0])) for j,c in poly.terms() if j[0]<=i) for i in range(n+1)]
  else:
   n,m=ds
   cc=[[sum(c*R(comb(i,j),comb(n,j))*R(comb(h,l),comb(m,l))
        for (j,l),c in poly.terms() if j<=i and l<=h) for h in range(m+1)] for i in range(n+1)]
  flat=cc if len(vs)==1 else [c for row in cc for c in row]
  assert min(flat)>0,(name,min(flat))
  saved.append({"name":name,"axes":[[str(a),str(lo),str(hi)] for a,lo,hi in axes],
   "degrees":list(ds),"positive_denominator":str(s.factor(den)),
   "coefficients":[str(c) for c in cc] if len(vs)==1 else [[str(c) for c in row] for row in cc]})
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round54_certificate.json").write_text(json.dumps(saved,indent=2),encoding="utf-8")
 print(json.dumps({"full_polynomials":len(saved),"positive_coefficients":111,"status":"built"}))
if __name__=="__main__":main()

