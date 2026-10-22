"""Independent exact reconstruction and algebra checks for round54."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational
def main():
 folder=Path(__file__).resolve().parent
 cert=json.loads((folder/"round54_certificate.json").read_text(encoding="utf-8"))
 t,x,u,v,B,L=s.symbols("t x u v B L")
 k=lambda a:2*a/(1-a*a)
 b=lambda a:(1+a*a)/(1-a*a)
 q=lambda a:a/(2-a)
 g=lambda a:(1-a)/(1+a)
 j=lambda a:2*a/(1+a)
 kap=R(71,50);H=R(7,12);beta=R(177,209)
 Bt=1+k(t)*(1-(b(t)-1)-t)
 Bc=1+k(t)*(beta-t)
 S=b(x)-k(x)*B
 M=B-(1+k(t))*(b(x)-B)/(k(x)-k(t))
 joint=s.cancel((k(x)-k(t))*(1+H-S)*(M+j(H-S)-kap))
 small_den=12*(1-t)**2*(1+t)**2*(79-50*t)*(50*t+21)
 transition_den=300*(1-t)**4*(1+t)**4*(1-x)**2*(1+x)**2
 common_den=13104300*(1-t)**2*(1+t)**2*(1-x)**2*(1+x)**2
 cases=[
  ("small_tau",H-2*q(kap-1+t)+k(2-kap-t)*(Bt-1),small_den,[(t,R(0),R(1,6))]),
  ("transition_leg",Bt-R(5,4),4*(1-t)**2*(1+t)**2,[(t,R(1,6),R(1,5))]),
  ("middle_angle_cut",H-q(kap-1+t)-g(R(9,20))+k(R(9,20))*(Bc-1),
   800052*(1-t)*(1+t)*(79-50*t),[(t,R(1,5),R(3,10))]),
  ("transition_joint",joint.subs(B,Bt),transition_den,[(t,R(1,6),R(1,5)),(x,R(19,50),R(1,2))]),
  ("middle_joint",joint.subs(B,Bc),common_den,[(t,R(1,5),R(3,10)),(x,R(1,3),R(9,20))]),
  ("end_joint",joint.subs(B,Bc),common_den,[(t,R(3,10),R(2,5)),(x,R(3,8),R(11,25))])]
 assert len(cert)==len(cases)==6
 total=0
 for record,(name,expr,den,axes) in zip(cert,cases):
  assert record["name"]==name
  assert record["axes"]==[[str(a),str(lo),str(hi)] for a,lo,hi in axes]
  assert s.expand(s.sympify(record["positive_denominator"],locals={"t":t,"x":x})-den)==0
  num=s.cancel(expr*den); assert s.denom(num)==1
  variables=[u,v][:len(axes)]
  poly=s.Poly(s.expand(num.subs({a:lo+(hi-lo)*w for (a,lo,hi),w in zip(axes,variables)})),*variables)
  ds=record["degrees"];assert list(poly.degree_list())==ds
  def bern(n,i,w):return comb(n,i)*w**i*(1-w)**(n-i)
  if len(ds)==1:
   coeff=[R(c) for c in record["coefficients"]];assert len(coeff)==ds[0]+1
   rebuilt=sum(c*bern(ds[0],i,u) for i,c in enumerate(coeff));flat=coeff
  else:
   coeff=[[R(c) for c in row] for row in record["coefficients"]]
   assert len(coeff)==ds[0]+1 and all(len(row)==ds[1]+1 for row in coeff)
   rebuilt=sum(c*bern(ds[0],i,u)*bern(ds[1],h,v) for i,row in enumerate(coeff) for h,c in enumerate(row))
   flat=[c for row in coeff for c in row]
  assert min(flat)>0 and s.Poly(s.expand(rebuilt-poly.as_expr()),*variables).is_zero,name
  total+=len(flat)
 assert total==111
 eta=s.symbols("eta")
 identities=[
  ("angle ordering",t/(2+t)-t*t-t*(1-2*t-t*t)/(2+t)),
  ("k difference",k(x)-k(t)-2*(x-t)*(1+x*t)/((1-x*x)*(1-t*t))),
  ("b minus one",b(t)-1-t*k(t)),
  ("long leg reduction",2-b(t)+k(t)*(2-b(x))-(1+k(t)*(1-(b(x)-1)-t))),
  ("M derivative",s.diff(M,B)-(k(x)+1)/(k(x)-k(t))),
  ("M combined numerator",(k(x)-k(t))*M-(B*(k(x)+1)-b(x)*(1+k(t)))),
  ("Bc derivative",s.diff(Bc,t)-2*(beta*(1+t*t)-2*t)/(1-t*t)**2),
  ("short leg relation",b(x)-k(x)*B-(g(x)-k(x)*(B-1))),
  ("inverse q",j(q(L))-L),
  ("angle polynomial",(300+125*(1-eta*eta)/(1+eta*eta)-551*2*eta/(1+eta*eta))*(1+eta*eta)-(175*eta*eta-1102*eta+425)),
  ("angle root",175*((551-s.sqrt(229226))/175)**2-1102*(551-s.sqrt(229226))/175+425)]
 for name,expr in identities:assert s.simplify(expr)==0,name
 constants={
  "x_tau_sign_at_two_fifths":1-2*R(2,5)-R(2,5)**2,
  "beta_derivative_margin":beta-R(4,5),
  "middle_cos_margin":Bc.subs(t,R(1,5))-b(R(1,3)),
  "end_cos_margin":Bc.subs(t,R(3,10))-b(R(3,8)),
  "end_sin_margin":Bc.subs(t,R(3,10))-R(373,275),
  "near_diagonal_ratio_square":R(289,288)**2-R(145,144),
  "near_diagonal_kappa_slack":kap-R(17,12)-R(5,3456),
  "F_diameter_square_slack":R(17,12)**2-2,
  "C_angle_polynomial_at_zero":R(425),
  "C_angle_diagonal_sign_after_squaring":R(2*1452**2-2052**2),
  "C_angle_derivative_negative_margin":R(1102-350),
  "top_above_left_e":1-R(2,5)-R(5,12)}
 assert all(c>0 for c in constants.values())
 result={"result":"passed","polynomial_reconstructions":6,
  "strictly_positive_rational_coefficients":total,"algebraic_identities":len(identities),
  "positive_exact_constants":len(constants),"UNSAT":0,
  "theorem":"If W contains QU, both rotations of C with theta_C >= theta_star are excluded",
  "theta_star_degrees_approx":float(360*s.atan((551-s.sqrt(229226))/175)/s.pi),
  "positive_rotation_threshold_degrees_approx":float(180*s.asin(R(50,71))/s.pi),
  "not_proved":"Whole upper-W bridge, other two mechanisms, G2 or S(6)=2"}
 print(json.dumps(result,indent=2))
 return result
if __name__=="__main__":main()

