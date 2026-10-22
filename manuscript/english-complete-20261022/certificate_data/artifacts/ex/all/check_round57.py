"""Independent inverse polynomial reconstruction and geometry algebra for round57."""
from pathlib import Path
from itertools import product
from collections import defaultdict
from math import comb
import sympy as s,json
R=s.Rational

def main():
 src=Path(__file__).resolve().parent
 recs=json.loads((src/"round57_certificate.json").read_text(encoding="utf-8"))
 h,t,x,a,u,v,w,B,H,N,M,al,VN,VD,DN,QD,TN,TD=s.symbols("h t x a u v w B H N M al VN VD DN QD TN TD")
 b=lambda z:(1+z*z)/(1-z*z);k=lambda z:2*z/(1-z*z)
 g=lambda z:(1-z)/(1+z);q=lambda z:z/(2-z)
 c=(1-h*h)/(1+h*h);ss=2*h/(1+h*h)
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t)
 z=1-h*h;y=2*h*(1-h-t)
 bd=(1-t*t)**2
 bn=s.cancel(Bt*bd);assert s.denom(bn)==1
 td=(z*z-y*y)*bd;tn=(z*z+y*y)*bd-2*y*z*bn
 nn=5*td+12*tn;mm=19*td-12*tn
 alpha_num=2*h*(1-h)-t*z
 vn=nn*(2*h*nn-alpha_num*mm);vd=(nn-h*mm)*(mm+h*nn)
 dn=2*h*h+t*z;qd=4*h-dn
 triangle=s.expand(((2*qd-dn)*td-tn*qd)*(vd-vn)-qd*td*vd)
 specs=[("exit_triangle",triangle,[(h,R(3,10),R(3,8)),(t,R(0),R(1,5))],s.Integer(1))]
 K=k(x)-k(t);S=b(x)-k(x)*B;G=b(x)-B
 Am=2*c*(1-c)+c*(c+ss)*t+c*(c-ss)*x
 axes_clear=2*(H-S)*K-(1+H-S)*Am*K
 joint_clear=2*(H-S)*K+(1+H-S)*(c*(c-ss)*(1-x)*K
  +(c+ss)*(ss*(K-G)+c*((B-1)*K-k(t)*G))-2*c*K)
 combined=s.cancel((axes_clear+joint_clear)*(1+h*h)**2)
 for name,B0,lo,hi,xlo,xhi,mult in [
  ("middle",Bt,R(1,5),R(4,15),R(9,25),R(12,25),R(1,3)),
  ("late",Bc,R(4,15),R(3,10),R(3,8),R(5,11),R(0)),
  ("end",Bc,R(3,10),R(19,50),R(3,8),R(11,25),R(1,3))]:
  expr=(combined-mult*S).subs({B:B0,H:R(7,12)})
  specs.append((name,expr,[(t,lo,hi),(x,xlo,xhi),(h,R(1,3),R(3,8))],
   (1-t*t)**(4 if name=="middle" else 2)*(1-x*x)**2))
 total=0
 for rec,(name,expr,axes,base) in zip(recs,specs):
  assert rec["name"]==name and rec["axes"]==[[str(z0),str(lo),str(hi)] for z0,lo,hi in axes]
  den=s.sympify(rec["positive_denominator"],locals={"h":h,"t":t,"x":x})
  ratio=s.cancel(den/base);assert ratio.is_Rational and ratio>0
  numerator=s.cancel(expr*den);assert s.denom(numerator)==1,name
  uvw=[u,v,w][:len(axes)]
  p=s.Poly(s.expand(numerator.subs({z0:lo+(hi-lo)*r for (z0,lo,hi),r in zip(axes,uvw)})),*uvw)
  deg=rec["degrees"];assert list(p.degree_list())==deg
  indices=list(product(*(range(n+1) for n in deg)))
  cc=[R(val) for val in rec["coefficients"]]
  assert len(cc)==len(indices) and all(val>0 for val in cc)
  rebuilt=defaultdict(lambda:R(0))
  for index,val in zip(indices,cc):
   for powers in product(*(range(i,n+1) for i,n in zip(index,deg))):
    vv0=val
    for i,j,n in zip(index,powers,deg):vv0*=comb(n,i)*comb(n-i,j-i)*(-1)**(j-i)
    rebuilt[powers]+=vv0
  assert {powers:val for powers,val in rebuilt.items() if val}==p.as_dict(),name
  total+=len(cc)
 assert len(recs)==len(specs)==4 and total==1017
 alpha=1-h-t/k(h);delta=b(h)-1;X=k(h)*(1-h-t)
 pp=(1-a*a)/(1+a*a);sa=2*a/(1+a*a)
 identities=[
  ("V1 actual support normalization",(sa+pp-1)/sa-(1-a)),
  ("left-exit bound",(delta+t-k(h)*(1-a))/(1-k(h)/k(a))-2*h*a*(a-alpha)/((a-h)*(1+h*a))),
  ("alpha margin",k(h)*(1-2*h)-R(1,5)-(-19*h*h+10*h-1)/(5*(1-h*h))),
  ("X upper",(1-h*h)*(1-X)-((1-h)**2+2*h*t)),
  ("corner inverse",2*g(a)/(1+g(a))-(1-a)),
  ("short leg reform",g(x)-k(x)*(B-1)-(1+x*x-2*B*x)/(1-x*x)),
  ("amax ratio",g(R(7,12)-TN/TD)-(5*TD+12*TN)/(19*TD-12*TN)),
  ("exit ratio",2*h*(N/M)*(N/M-al)/((N/M-h)*(1+h*N/M))-(2*h*N*N-2*h*al*N*M)/((N-h*M)*(M+h*N))),
  ("triangle rational numerator",((2-DN/QD-TN/TD)*(1-VN/VD)-1)*QD*TD*VD-((2*QD*TD-DN*TD-TN*QD)*(VD-VN)-QD*TD*VD)),
  ("first increasing factor",s.diff(a/(1+h*a),a)-1/(1+h*a)**2),
  ("second increasing factor",s.diff((a-al)/(a-h),a)-(al-h)/(a-h)**2),
  ("left q cap",g(alpha)-q(h+t/k(h)))]
 for name,expr in identities:assert s.cancel(expr)==0,name
 constants={
  "alpha_margin_left":(-19*h*h+10*h-1).subs(h,R(3,10)),
  "alpha_margin_right":(-19*h*h+10*h-1).subs(h,R(3,8)),
  "D_cap_margin":1-(R(3,8)+R(1,5)/k(R(3,10))),
  "X_positive_margin":1-R(3,8)-R(1,5),
  "nonnegative_slack_multiplier":R(1,3),
  "diameter_H_margin":R(17,12)**2-2,
  "inherited_tau_cap":Bc.subs(t,R(19,50))**2-2}
 assert all(val>0 for val in constants.values())
 assert constants["alpha_margin_right"]==R(5,64)
 assert constants["D_cap_margin"]==R(193,600)
 subs={h:R(1,3),t:R(1,6),x:R(39,100),B:Bt.subs(t,R(1,6)),H:R(7,12)}
 Eaxis=axes_clear/(K*(1+H-S));Ejoint=joint_clear/(K*(1+H-S))
 assert s.cancel(Eaxis.subs(subs))==-R(22454953,2597454375)
 assert s.cancel(Ejoint.subs(subs))==-R(1779133542,4118696820625)
 assert Bt.subs(t,R(1,5))-(1+R(7,15)**2)/(2*R(7,15))==-R(31,5040)
 result={"result":"passed","new_polynomial_reconstructions":4,"new_positive_coefficients":1017,
  "algebraic_identities":len(identities),"positive_exact_constants":len(constants),
  "exact_failed_relaxation_checks":3,"UNSAT":0,
  "new_theorem":"W contains QU, negative C: eta_C >= 1/3 excluded; also eta_C in [3/10,3/8] with tau <= 1/5 excluded",
  "remaining_upper_W":"negative eta_C in (1/24,1/3); eta_C >= 3/10 additionally requires tau > 1/5",
  "not_proved":"general double direct, right-W bridge, all G2 or S(6)=2"}
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
