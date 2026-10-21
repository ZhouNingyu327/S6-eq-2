"""Round56: fixed full-domain rational certificates, not subdivision."""
from pathlib import Path
from itertools import product
from math import comb
import sympy as s,json
R=s.Rational;t,x,h,u,v,w=s.symbols("t x h u v w")
b=lambda z:(1+z*z)/(1-z*z);k=lambda z:2*z/(1-z*z)
q=lambda z:z/(2-z);g=lambda z:(1-z)/(1+z)

def main():
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t);H=R(7,12)
 d0=1+h*h;c0=1-h*h;s0=2*h;specs=[]
 for name,B,lo,hi,xlo,xhi in [
  ("transition",Bt,R(1,6),R(1,5),R(1,3),R(1,2)),
  ("middle",Bt,R(1,5),R(4,15),R(9,25),R(12,25)),
  ("late",Bc,R(4,15),R(3,10),R(3,8),R(5,11)),
  ("end",Bc,R(3,10),R(19,50),R(3,8),R(11,25))]:
  K=k(x)-k(t);S=b(x)-k(x)*B;G=b(x)-B
  N=4*(H-S)*K*d0*d0+(1+H-S)*(
   c0*(c0-s0)*(1-2*x)*K
   +(c0+s0)*(s0*(K-G)+c0*((B-1)*K-k(t)*G))
   +(-4*c0*d0+2*c0*c0-c0*(c0+s0)*t)*K)
  specs.append((name,N,[(t,lo,hi),(x,xlo,xhi),(h,R(3,8),R(5,12))]))
 X=k(h)*(1-h-t);A=(c0+s0)/d0-1+t
 specs.append(("small_t",H-q(A)-g(X)+k(X)*(Bt-1),
  [(h,R(3,8),R(5,12)),(t,R(0),R(1,6))]))
 records=[];count=0
 for name,expr,axes in specs:
  num,den=s.cancel(expr).as_numer_denom()
  if den.subs({z:(lo+hi)/2 for z,lo,hi in axes})<0:num,den=-num,-den
  uvw=[u,v,w][:len(axes)]
  poly=s.Poly(s.expand(num.subs({z:lo+(hi-lo)*p for (z,lo,hi),p in zip(axes,uvw)})),*uvw)
  deg=poly.degree_list();terms=poly.terms();cc=[]
  for index in product(*(range(n+1) for n in deg)):
   total=R(0)
   for powers,val in terms:
    if all(a<=i for a,i in zip(powers,index)):
     for a,i,n in zip(powers,index,deg):val*=R(comb(i,a),comb(n,a))
     total+=val
   assert total>0,(name,index,total)
   cc.append(str(total))
  count+=len(cc)
  records.append({"name":name,"axes":[[str(z),str(lo),str(hi)] for z,lo,hi in axes],
   "degrees":list(deg),"positive_denominator":str(s.factor(den)),
   "coefficient_order":"lexicographic multi-index, last index varies fastest",
   "coefficients":cc})
 assert len(records)==5 and count==1016
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round56_certificate.json").write_text(json.dumps(records,indent=2),encoding="utf-8")
 print(json.dumps({"new_polynomials":5,"new_positive_coefficients":count}))
if __name__=="__main__":main()
