"""Four explicit geometric-domain certificates for round57."""
from pathlib import Path
from itertools import product
from math import comb
import sympy as s,json
R=s.Rational;t,x,h,u,v,w=s.symbols("t x h u v w")
b=lambda a:(1+a*a)/(1-a*a);k=lambda a:2*a/(1-a*a)

def triangle():
 Bt=1+k(t)*(1-(b(t)-1)-t);Bn,Bd=s.cancel(Bt).as_numer_denom()
 if Bd.subs(t,R(1,10))<0:Bn,Bd=-Bn,-Bd
 Z=1-h*h;Y=2*h*(1-h-t)
 TD=(Z*Z-Y*Y)*Bd;TN=(Z*Z+Y*Y)*Bd-2*Bn*Y*Z
 N=5*TD+12*TN;M=19*TD-12*TN;AN=2*h*(1-h)-t*Z
 VN=2*h*N*N-AN*N*M;VD=(N-h*M)*(M+h*N)
 DN=2*h*h+t*Z;QD=4*h-DN
 return s.expand((2*QD*TD-DN*TD-TN*QD)*(VD-VN)-QD*TD*VD)

def combined(B):
 H=R(7,12);K=k(x)-k(t);S=b(x)-k(x)*B;G=b(x)-B
 d=1+h*h;c=1-h*h;ss=2*h
 return 4*(H-S)*K*d*d+(1+H-S)*(c*(c-ss)*(1-2*x)*K
  +(c+ss)*(ss*(K-G)+c*((B-1)*K-k(t)*G))
  +(-4*c*d+2*c*c-c*(c+ss)*t)*K)

def main():
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t)
 specs=[("exit_triangle",triangle(),[(h,R(3,10),R(3,8)),(t,R(0),R(1,5))])]
 for name,B,lo,hi,xlo,xhi,mult in [
  ("middle",Bt,R(1,5),R(4,15),R(9,25),R(12,25),R(1,3)),
  ("late",Bc,R(4,15),R(3,10),R(3,8),R(5,11),R(0)),
  ("end",Bc,R(3,10),R(19,50),R(3,8),R(11,25),R(1,3))]:
  specs.append((name,combined(B)-mult*(b(x)-k(x)*B),
   [(t,lo,hi),(x,xlo,xhi),(h,R(1,3),R(3,8))]))
 records=[];count=0
 for name,expr,axes in specs:
  num,den=s.cancel(expr).as_numer_denom()
  if den.subs({a:(lo+hi)/2 for a,lo,hi in axes})<0:num,den=-num,-den
  uvw=[u,v,w][:len(axes)]
  p=s.Poly(s.expand(num.subs({a:lo+(hi-lo)*q for (a,lo,hi),q in zip(axes,uvw)})),*uvw)
  deg=p.degree_list();cc=[]
  for index in product(*(range(n+1) for n in deg)):
   val=R(0)
   for powers,coef in p.terms():
    if all(j<=i for j,i in zip(powers,index)):
     for j,i,n in zip(powers,index,deg):coef*=R(comb(i,j),comb(n,j))
     val+=coef
   assert val>0,(name,index,val);cc.append(str(val))
  count+=len(cc)
  records.append({"name":name,"axes":[[str(a),str(lo),str(hi)] for a,lo,hi in axes],
   "degrees":list(deg),"positive_denominator":str(s.factor(den)),
   "order":"lexicographic multi-index, last index fastest","coefficients":cc})
 assert count==1017 and len(records)==4
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round57_certificate.json").write_text(json.dumps(records,indent=2),encoding="utf-8")
 print(json.dumps({"new_polynomials":4,"new_positive_coefficients":count}))
if __name__=="__main__":main()
