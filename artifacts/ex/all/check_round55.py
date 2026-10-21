"""Independent complete reconstruction for the all-positive-angle lemma."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 folder=Path(__file__).resolve().parent
 records=json.loads((folder/"round55_certificate.json").read_text(encoding="utf-8"))
 old_records=json.loads((folder/"round54_certificate.json").read_text(encoding="utf-8"))
 t,x,u,v,B,eta,A,Y=s.symbols("t x u v B eta A Y")
 k=lambda a:2*a/(1-a*a);b=lambda a:(1+a*a)/(1-a*a)
 sin=lambda a:2*a/(1+a*a)
 H=R(7,12);kap=R(71,50);beta=R(177,209)
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(beta-t)
 K=k(x)-k(t);S=b(x)-k(x)*B;X=(b(x)-B)/K;M=B-(1+k(t))*X
 j=lambda a:2*a/(1+a)
 # Reconstruct from the geometric rational inequalities, not builder numerators.
 exprs={"axis":s.cancel(K*(1+H-S)*(j(H-S)-X)),
        "diagonal":s.cancel(K*(1+H-S)*(M+j(H-S)-kap))}
 charts=[
 ("transition",Bt,R(1,6),R(1,5),R(1,3),R(1,2)),
 ("middle",Bt,R(1,5),R(4,15),R(9,25),R(12,25)),
 ("late",Bc,R(4,15),R(3,10),R(3,8),R(5,11)),
 ("end",Bc,R(3,10),R(2,5),R(3,8),R(11,25))]
 def validate(rec,expr,den,axes):
  assert rec["axes"]==axes
  assert s.expand(s.sympify(rec["positive_denominator"],locals={"t":t,"x":x})-den)==0
  num=s.cancel(expr*den);assert s.denom(num)==1
  lo,hi=map(R,axes[0][1:]);xl,xh=map(R,axes[1][1:])
  p=s.Poly(s.expand(num.subs({t:lo+(hi-lo)*u,x:xl+(xh-xl)*v})),u,v)
  n,m=rec["degrees"];assert list(p.degree_list())==[n,m]
  cc=[[R(c) for c in row] for row in rec["coefficients"]]
  assert len(cc)==n+1 and all(len(row)==m+1 for row in cc)
  assert min(c for row in cc for c in row)>0
  rebuilt=sum(c*comb(n,i)*u**i*(1-u)**(n-i)*comb(m,h)*v**h*(1-v)**(m-h)
              for i,row in enumerate(cc) for h,c in enumerate(row))
  assert s.Poly(s.expand(rebuilt-p.as_expr()),u,v).is_zero
  return (n+1)*(m+1)
 count=0;index=0;inherited=0
 for name,B0,lo,hi,xl,xh in charts:
  for kind in ["axis","diagonal"]:
   denbase=(1-t*t)**(4 if name in ["transition","middle"] else 2)*(1-x*x)**2
   mult=(6 if kind=="axis" else 300) if name in ["transition","middle"] else (262086 if kind=="axis" else 13104300)
   axes=[["t",str(lo),str(hi)],["x",str(xl),str(xh)]]
   if name=="end" and kind=="diagonal":
    rec=next(r for r in old_records if r["name"]=="end_joint")
    inherited=validate(rec,exprs[kind].subs(B,B0),mult*denbase,axes)
   else:
    rec=records[index];index+=1;assert rec["name"]==name+"_"+kind
    count+=validate(rec,exprs[kind].subs(B,B0),mult*denbase,axes)
 assert index==len(records)==7 and count==255 and inherited==25
 P=1-2*t-6*t*t+2*t**3-3*t**4
 c=(1-eta*eta)/(1+eta*eta);ss=2*eta/(1+eta*eta);d=s.sqrt(2)-1
 F=(A-1)+2*eta*Y-(A+1)*eta*eta
 ids=[
 ("Bt derivative",s.diff(Bt,t)-2*P/(1-t*t)**3),
 ("endpoint normal decomposition",c*A+ss*Y-((c-ss)*A+ss*(A+Y))),
 ("endpoint weight",c+d*ss-1-2*eta*(d-eta)/(1+eta*eta)),
 ("concavity interpolation",F-((1-eta/d)*F.subs(eta,0)+(eta/d)*F.subs(eta,d))-(A+1)*eta*(d-eta)),
 ("long-leg lower endpoint reciprocal",b(R(3,8))-1/sin(R(5,11))),
 ("new B lower bound",2-b(t)+k(t)*R(33,35)-(1+k(t)*(R(33,35)-t)))]
 for name,e in ids:assert s.simplify(e)==0,name
 constants={
 "P_right":P.subs(t,R(4,15)),
 "P_derivative_negative_margin":2-6*R(4,15)**2,
 "transition_long":Bt.subs(t,R(1,6))-R(5,4),
 "middle_cos":Bt.subs(t,R(1,5))-b(R(9,25)),
 "middle_sin":Bt.subs(t,R(1,5))-1/sin(R(12,25)),
 "late_cos_sin":Bc.subs(t,R(4,15))-b(R(3,8)),
 "end_cos":Bc.subs(t,R(3,10))-b(R(3,8)),
 "end_sin":Bc.subs(t,R(3,10))-1/sin(R(11,25)),
 "kappa_above_sqrt2_squared":kap**2-2,
 "F_diameter_slack":R(17,12)**2-2,
 "Bc_monotonicity":beta-R(4,5)}
 assert all(val>0 for val in constants.values())
 result={"result":"passed","new_polynomial_reconstructions":7,"new_positive_coefficients":255,
  "inherited_round54_polynomials_replayed":1,"inherited_positive_coefficients_replayed":25,
  "algebraic_checks":len(ids),"positive_exact_constants":len(constants),"UNSAT":0,
  "theorem":"If W contains QU and C has positive rotation at any smaller axis angle, tau<1/6",
  "consequences":["z<1/6","u>5/6","D>33/35"],
  "not_proved":"Whole positive upper-W bridge; negative rotation tau bound; other mechanisms; G2 or S(6)=2"}
 print(json.dumps(result,indent=2))
 return result
if __name__=="__main__":main()

