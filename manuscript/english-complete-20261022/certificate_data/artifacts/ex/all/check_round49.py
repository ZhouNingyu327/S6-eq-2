"""Right-W-bridge small C angle: exact identities and rational margins."""
from pathlib import Path
import json,math
import sympy as sp
def main():
 a,z,d,k,r,h=sp.symbols("a z d k r h")
 q=lambda t:t/(2-t)
 dz=2*z*z/(1-z*z)
 ids=[]
 def ident(name,e):
  assert sp.cancel(e)==0,(name,sp.factor(e));ids.append(name)
 ident("q exact increment",q(a+h)-q(a)-2*h/((2-a-h)*(2-a)))
 ident("F square height perturbation",(1-z-d)**2-(1-z)**2+2*d*(1-z)-d*d)
 ident("small z delta ratio",dz/z-2*z/(1-z*z))
 ident("negative exceptional q loss",
       1-k-q(1-sp.Rational(9,10)*k)-k*(8-9*k)/(10+9*k))
 ident("large-a ordinary positive margin",
       12*(sp.Rational(2,3)-sp.Rational(480,1463))-4-sp.Rational(92,1463))
 ident("middle-a exact q increment maximum",
       q(sp.Rational(1,2)+sp.Rational(32,209))-q(sp.Rational(1,2))-sp.Rational(256,1689))
 constants=[]
 def positive(name,e):
  e=sp.simplify(e);assert e.is_positive is True,(name,e)
  constants.append({"name":name,"exact_margin":str(e)})
 Q=sp.Rational
 eta=Q(1,64);km=Q(128,4095);dm=Q(2,4095)
 positive("K below one over31",Q(1,31)-km)
 positive("small q argument below half",Q(1,2)-(Q(1,3)+Q(1,24)+dm))
 positive("positive L T coefficient",1-Q(1,7)-eta-Q(4,5))
 positive("negative L T coefficient",1-Q(1,3)-eta-Q(1,2))
 positive("small positive rotation margin",Q(21,40)-Q(15,256))
 positive("small negative rotation margin",Q(21,40)-Q(9,224))
 M=Q(1313,8550)-Q(256,1689)
 positive("middle shifted surplus",M)
 positive("middle including C rotation",M-4*dm)
 positive("middle all q arguments below one",1-Q(1,2)-Q(32,209)-dm)
 positive("ordinary large-a q domain",1-Q(240,1463)-Q(1,12))
 positive("ordinary large-a residual",Q(92,1463))
 bound=Q(576,7)*eta**2*km
 assert bound==Q(2,3185)
 positive("exceptional z over K cap",Q(1,100)-bound)
 positive("exceptional delta z over z cap",Q(1,10)-2*Q(1,3100)/(1-Q(1,3100)**2))
 positive("exceptional S1 per K",Q(1,10)-(6*eta)/(1-6*dm))
 positive("positive exceptional right q domain",Q(1,4)-eta-Q(1,100)-Q(1,1000))
 positive("positive exceptional bottom contradiction",Q(7,12)-Q(1,10)-Q(1,7))
 positive("negative exceptional coefficient",1-eta-Q(1,3100)-Q(49,50))
 positive("negative exceptional shifted right root",Q(979,1000)-Q(9,10))
 positive("negative exceptional q loss domain",Q(8,9)-km)
 positive("negative exceptional F lower surplus",Q(1,10)-2*(Q(1,100)+eta))
 positive("negative exceptional final gap",Q(9,10)-Q(1,10))
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 result={"result":"passed","UNSAT":0,"algebraic_identities":len(ids),
  "identity_names":ids,"constant_count":len(constants),"constants":constants,
  "new_closed_subclass":"Right-W bridge: C contains QU but not Q2, both C rotations, eta in [0,1/64]",
  "angle_degrees_max":2*math.degrees(math.atan(1/64)),
  "historical_input":"Round43 full scalar E bounds and its original frozen rational certificate; not counted anew",
  "new_geometric_input":"Actual nonempty W H bridge and TOP chord imply H<sec(theta_z)-1, hence S2<q(r+Delta_z) on the proved argument domain",
  "not_proved":"Entire right-W bridge, either round48 I/II combination, other remaining whole mechanisms, G2 or S(6)=2"}
 (out/"S6_round49_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({n:v for n,v in result.items() if n not in {"identity_names","constants"}},indent=2))
if __name__=="__main__":main()

