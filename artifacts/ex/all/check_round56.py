"""Independent inverse coefficient reconstruction and identities for round56."""
from pathlib import Path
from itertools import product
from math import comb
from collections import defaultdict
import sympy as s,json
R=s.Rational

def main():
 src=Path(__file__).resolve().parent
 records=json.loads((src/"round56_certificate.json").read_text(encoding="utf-8"))
 t,x,h,u,v,w,B,H,mu,D,L4,z,e,Q,r,yy,xi,ups=s.symbols("t x h u v w B H mu D L4 z e Q r yy xi ups")
 b=lambda a:(1+a*a)/(1-a*a);k=lambda a:2*a/(1-a*a)
 q=lambda a:a/(2-a);g=lambda a:(1-a)/(1+a)
 c=(1-h*h)/(1+h*h);ss=2*h/(1+h*h)
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t)
 K=k(x)-k(t);S=b(x)-k(x)*B;G=b(x)-B
 Am=2*c*(1-c)+c*(c+ss)*t+c*(c-ss)*x
 # Reconstruct the two distinct necessary inequalities before adding them.
 axis_cleared=2*(H-S)*K-(1+H-S)*Am*K
 joint_cleared=2*(H-S)*K+(1+H-S)*(c*(c-ss)*(1-x)*K
  +(c+ss)*(ss*(K-G)+c*((B-1)*K-k(t)*G))-2*c*K)
 combined=s.cancel((axis_cleared+joint_cleared)*(1+h*h)**2)
 specs=[]
 for name,B0,lo,hi,xlo,xhi in [
  ("transition",Bt,R(1,6),R(1,5),R(1,3),R(1,2)),
  ("middle",Bt,R(1,5),R(4,15),R(9,25),R(12,25)),
  ("late",Bc,R(4,15),R(3,10),R(3,8),R(5,11)),
  ("end",Bc,R(3,10),R(19,50),R(3,8),R(11,25))]:
  specs.append((name,combined.subs({B:B0,H:R(7,12)}),
   [(t,lo,hi),(x,xlo,xhi),(h,R(3,8),R(5,12))],
   (1-t*t)**(4 if name in ("transition","middle") else 2)*(1-x*x)**2))
 X=1-b(h)+k(h)*(1-t);A=c+ss-1+t
 f1=h*h+2*h*t-2*h+1;f2=3*h*h+2*h*t-2*h-1
 f3=h*h*t-4*h*h+2*h+t-2
 specs.append(("small_t",R(7,12)-q(A)-g(X)+k(X)*(Bt-1),
  [(h,R(3,8),R(5,12)),(t,R(0),R(1,6))],(1-t*t)**2*f1*f2*f3))
 total=0
 for rec,(name,expr,axes,base) in zip(records,specs):
  assert rec["name"]==name
  assert rec["axes"]==[[str(z0),str(lo),str(hi)] for z0,lo,hi in axes]
  den=s.sympify(rec["positive_denominator"],locals={"h":h,"t":t,"x":x})
  ratio=s.cancel(den/base);assert ratio.is_Rational and ratio>0,(name,ratio)
  numerator=s.cancel(expr*den);assert s.denom(numerator)==1,name
  uvw=[u,v,w][:len(axes)]
  poly=s.Poly(s.expand(numerator.subs({a:lo+(hi-lo)*p for (a,lo,hi),p in zip(axes,uvw)})),*uvw)
  degrees=rec["degrees"];assert list(poly.degree_list())==degrees,name
  indices=list(product(*(range(n+1) for n in degrees)))
  coefficients=[R(a) for a in rec["coefficients"]]
  assert len(coefficients)==len(indices) and all(a>0 for a in coefficients)
  # Inverse transform: expand each Bernstein basis into power coefficients.
  rebuilt=defaultdict(lambda:R(0))
  for index,a in zip(indices,coefficients):
   for powers in product(*(range(i,n+1) for i,n in zip(index,degrees))):
    value=a
    for i,j0,n in zip(index,powers,degrees):
     value*=comb(n,i)*comb(n-i,j0-i)*(-1)**(j0-i)
    rebuilt[powers]+=value
  assert {p:a for p,a in rebuilt.items() if a}==poly.as_dict(),name
  total+=len(coefficients)
 assert len(records)==len(specs)==5 and total==1016
 Bz=1+k(t)*(1-(b(z)-1)-t)
 p1r=c*(Q+r)+(c+ss)*e
 p1t=ss*Q+c*yy-(c-ss)*e
 p1tr=ss*(Q+xi)+c*ups-(c-ss)*e
 identities=[
  ("unit normals",c*c+ss*ss-1),
  ("actual TOP mu dependence",2*mu-b(t)+k(t)*(2*mu-b(z))-Bz-2*(1+k(t))*(mu-1)),
  ("actual upper coordinate",Bz+2*(1+k(t))*(mu-1)-k(t)*xi-mu-(Bz-1-k(t)*xi+(1+2*k(t))*(mu-1))),
  ("eliminate e at axes",(c-ss)*p1r+(c+ss)*p1t-(Q+c*(c-ss)*r+c*(c+ss)*yy)),
  ("eliminate e at junction",(c-ss)*p1r+(c+ss)*p1tr-(Q+c*(c-ss)*r+(c+ss)*(ss*xi+c*ups))),
  ("negative X factor",X-k(h)*(1-h-t)),
  ("axis bound at X",Am.subs(x,X)-A),
  ("first denominator",f1-(1-h*h)*(1-X)),
  ("second denominator",f2+(1-h*h)*(1+X)),
  ("third denominator",f3-(1+h*h)*(A-2)),
  ("F diameter margin rewrite",(R(17,12)**2-2)-R(1,144))]
 for name,expr in identities:assert s.simplify(expr)==0,name
 constants={
  "last_tau_cap":Bc.subs(t,R(19,50))**2-2,
  "Bc_monotone":R(177,209)-R(4,5),
  "X_lower":k(R(3,8))*(1-R(5,12)-R(1,6)),
  "q_argument_margin":1-(R(1,2)+R(1,4)+R(4,25)),
  "negative_x_derivative_margin":R(1,2)-R(8,25),
  "auxiliary_h_plus_t_margin":1-R(5,12)-R(1,6),
  "auxiliary_h_above_diagonal":(1+R(5,12))**2-2,
  "A0_cap_margin":1-(R(1,2)+R(1,6)),
  "transition_long_leg":Bt.subs(t,R(1,6))-R(5,4),
  "middle_cos":Bt.subs(t,R(1,5))-b(R(9,25)),
  "middle_sin":Bt.subs(t,R(1,5))-(1+R(12,25)**2)/(2*R(12,25)),
  "late_leg":Bc.subs(t,R(4,15))-b(R(3,8)),
  "end_cos":Bc.subs(t,R(3,10))-b(R(3,8)),
  "end_sin":Bc.subs(t,R(3,10))-(1+R(11,25)**2)/(2*R(11,25))}
 assert all(a>0 for a in constants.values()),constants
 assert constants["last_tau_cap"]==R(796687,553613841)
 assert constants["X_lower"]==R(4,11)
 result={"result":"passed","new_polynomial_reconstructions":5,
  "new_positive_coefficients":1016,"algebraic_identities":len(identities),
  "positive_exact_constants":len(constants),"UNSAT":0,
  "theorem":"W contains QU and C has negative rotation with eta_C >= 3/8 is excluded",
  "new_all_rotation_bound":"W contains QU implies tau < 19/50",
  "not_proved":"Negative upper-W eta_C in (1/24,3/8), general double direct, right-W bridge, G2 or S(6)=2"}
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
