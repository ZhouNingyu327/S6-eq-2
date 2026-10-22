"""Independent full reconstruction for the final round55 theorem."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 folder=Path(__file__).resolve().parent
 records=json.loads((folder/"round55_certificate.json").read_text(encoding="utf-8"))
 old=json.loads((folder/"round54_certificate.json").read_text(encoding="utf-8"))
 t,x,h,a,u,v,B,H,A0,Y=s.symbols("t x h a u v B H A0 Y")
 k=lambda z:2*z/(1-z*z);b=lambda z:(1+z*z)/(1-z*z)
 sn=lambda z:2*z/(1+z*z);q=lambda z:z/(2-z);g=lambda z:(1-z)/(1+z);j=lambda z:2*z/(1+z)
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t)
 K=k(x)-k(t);S=b(x)-k(x)*B;XX=(b(x)-B)/K;M=B-(1+k(t))*XX
 e_axis=s.cancel(K*(1+H-S)*(j(H-S)-XX))
 e_diag=s.cancel(K*(1+H-S)*(M+j(H-S)-R(71,50)))
 e_angle=s.cancel(K*(1+H-S)*((1-a*a)*(j(H-S)+1-XX)+2*a*(B-1-k(t)*XX)-(1+a*a)))
 specs=[]
 for name,B0,lo,hi,xlo,xhi in [
 ("first",Bt,R(3,20),R(1,6),R(33,100),R(101,200)),
 ("transition",Bt,R(1,6),R(1,5),R(1,3),R(1,2)),
 ("middle",Bt,R(1,5),R(4,15),R(9,25),R(12,25)),
 ("late",Bc,R(4,15),R(3,10),R(3,8),R(5,11)),
 ("end",Bc,R(3,10),R(2,5),R(3,8),R(11,25))]:
  base=(1-t*t)**(4 if name in ["first","transition","middle"] else 2)*(1-x*x)**2
  for kind,expr in [("axis",e_axis),("diagonal",e_diag)]:
   specs.append((name+"_"+kind,expr.subs({B:B0,H:R(7,12)}),base,[(t,lo,hi),(x,xlo,xhi)],name=="end" and kind=="diagonal"))
 for name,H0,a0,lo,hi,xlo,xhi in [
 ("cut_mid",R(16,23),R(1,5),R(1,20),R(3,20),R(1,5),R(2,3)),
 ("cut_small",R(12,13),R(1,10),R(1,100),R(1,20),R(1,11),R(5,6))]:
  for kind,aval in [("axis",R(0)),("angle",a0)]:
   specs.append((name+"_"+kind,e_angle.subs({B:Bt,H:H0,a:aval}),
     (1-t*t)**4*(1-x*x)**2,[(t,lo,hi),(x,xlo,xhi)],False))
 AA=g(h)+k(h)*t;XC=1-h-t/k(h);dd=b(h)-1;HF=2-1/(1-dd-t)
 U=q(AA)+g(XC)-k(XC)*(Bt-1)
 f1=h*h*t-2*h*h-t;f2=3*h*h+2*h*t-2*h-1
 f3=h*h*t-3*h*h-t+1;f4=h*h*t-2*h*h+4*h-t
 for name,H0,hlo,hhi,thi in [
 ("C_high",R(7,12),R(1,4),R(5,12),R(3,20)),
 ("C_middle_high",HF,R(1,5),R(1,4),R(3,20)),
 ("C_middle",HF,R(1,10),R(1,5),R(1,20)),
 ("C_small",HF,R(1,24),R(1,10),R(1,100))]:
  base=(1-t*t)**2*f1*f2*f4*(1 if name=="C_high" else f3)
  specs.append((name,H0-U,base,[(h,hlo,hhi),(t,R(0),thi)],False))
 count=index=old_count=0
 for name,expr,base,axes,inherited in specs:
  if inherited:rec=next(r for r in old if r["name"]=="end_joint")
  else:rec=records[index];index+=1;assert rec["name"]==name
  assert rec["axes"]==[[str(z),str(lo),str(hi)] for z,lo,hi in axes]
  den=s.sympify(rec["positive_denominator"],locals={"t":t,"x":x,"h":h})
  ratio=s.cancel(den/base);assert ratio.is_Rational and ratio>0,(name,ratio)
  num=s.cancel(expr*den);assert s.denom(num)==1,name
  poly=s.Poly(s.expand(num.subs({z:lo+(hi-lo)*w for (z,lo,hi),w in zip(axes,[u,v])})),u,v)
  n,m=rec["degrees"];assert list(poly.degree_list())==[n,m],name
  cc=[[R(c) for c in row] for row in rec["coefficients"]]
  assert len(cc)==n+1 and all(len(row)==m+1 for row in cc)
  assert min(c for row in cc for c in row)>0
  rebuilt=sum(c*comb(n,i)*u**i*(1-u)**(n-i)*comb(m,r)*v**r*(1-v)**(m-r)
              for i,row in enumerate(cc) for r,c in enumerate(row))
  assert s.Poly(s.expand(poly.as_expr()-rebuilt),u,v).is_zero,name
  if inherited:old_count+=(n+1)*(m+1)
  else:count+=(n+1)*(m+1)
 assert index==len(records)==17 and count==824 and old_count==25
 P=1-2*t-6*t*t+2*t**3-3*t**4
 c=(1-h*h)/(1+h*h);ss=2*h/(1+h*h);d=s.sqrt(2)-1
 F=(A0-1)+2*h*Y-(A0+1)*h*h
 ids=[
 ("Bt derivative",s.diff(Bt,t)-2*P/(1-t*t)**3),
 ("diagonal endpoint weight",c+d*ss-1-2*h*(d-h)/(1+h*h)),
 ("general concavity",F-((1-h/a)*F.subs(h,0)+(h/a)*F.subs(h,a))-(A0+1)*h*(a-h)),
 ("cos slope delta",dd-h*k(h)),
 ("C Q cap",b(h)-k(h)*(1-t)-AA),
 ("C right-axis cap",1-(dd+t)/k(h)-XC),
 ("first denominator sign",f1+2*h*(1-XC)),
 ("second denominator sign",f2-(1-h*h)*(AA-2)),
 ("third denominator sign",f3-(1-h*h)*(1-dd-t)),
 ("fourth denominator sign",f4-2*h*(1+XC)),
 ("large-angle matching leg",b(R(3,8))-1/sn(R(5,11))),
 ("mid matching leg",b(R(1,5))-1/sn(R(2,3))),
 ("small matching leg",b(R(1,11))-1/sn(R(5,6))),
 ("mid F lower",HF.subs({h:R(1,5),t:R(3,20)})-R(16,23)),
 ("small F lower",HF.subs({h:R(1,10),t:R(1,20)})-R(1702,1841))]
 for name,expr in ids:assert s.simplify(expr)==0,name
 constants={
 "P_right":P.subs(t,R(4,15)),"P_decreasing_margin":2-6*R(4,15)**2,
 "first_cos":Bt.subs(t,R(3,20))-b(R(33,100)),
 "first_sin":Bt.subs(t,R(3,20))-1/sn(R(101,200)),
 "transition_leg":Bt.subs(t,R(1,6))-R(5,4),
 "middle_cos":Bt.subs(t,R(1,5))-b(R(9,25)),
 "middle_sin":Bt.subs(t,R(1,5))-1/sn(R(12,25)),
 "late_leg":Bc.subs(t,R(4,15))-b(R(3,8)),
 "end_cos":Bc.subs(t,R(3,10))-b(R(3,8)),
 "end_sin":Bc.subs(t,R(3,10))-1/sn(R(11,25)),
 "mid_cut_leg":Bt.subs(t,R(1,20))-b(R(1,5)),
 "small_cut_leg":Bt.subs(t,R(1,100))-b(R(1,11)),
 "small_H_slack":R(1702,1841)-R(12,13),
 "kappa_above_sqrt2":R(71,50)**2-2,"F_diameter_margin":R(17,12)**2-2,
 "Bc_monotonicity":R(177,209)-R(4,5)}
 domains=[(R(1,4),R(5,12),R(3,20)),(R(1,5),R(1,4),R(3,20)),
          (R(1,10),R(1,5),R(1,20)),(R(1,24),R(1,10),R(1,100))]
 for i,(lo,hi,thi) in enumerate(domains):
  constants[f"X_lower_{i}"]=1-hi-thi/k(lo)
  constants[f"A_upper_margin_{i}"]=1-hi-thi
  if i:constants[f"F_denominator_margin_{i}"]=1-(b(hi)-1)-thi
 assert all(val>0 for val in constants.values()),constants
 assert constants["X_lower_0"]==R(29,96)
 assert constants["X_lower_1"]==R(39,100)
 assert constants["X_lower_2"]==R(221,400)
 assert constants["X_lower_3"]==R(749,960)
 result={"result":"passed","new_polynomial_reconstructions":17,"new_positive_coefficients":824,
  "inherited_round54_polynomials_replayed":1,"inherited_round54_coefficients_replayed":25,
  "algebraic_checks":len(ids),"positive_exact_constants":len(constants),"UNSAT":0,
  "theorem":"Entire positive-rotation C subclass with W containing QU is excluded",
  "historical_small_C_input":"Round52 eta_C<=1/24, cited rather than mathematically replayed here",
  "not_proved":"Negative upper-W bridge, all double-direct configurations, right-W bridge, G2 or S(6)=2"}
 print(json.dumps(result,indent=2))
 return result
if __name__=="__main__":main()

