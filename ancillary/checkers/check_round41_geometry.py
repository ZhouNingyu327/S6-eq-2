"""Exact small checks and identities for round41."""
from pathlib import Path
import json,time
import sympy as sp
import z3
def main():
 rows=[]
 def query(name,cs,theory="QF_NRA"):
  sol=z3.SolverFor(theory);sol.set(timeout=30000);sol.add(*cs)
  start=time.perf_counter();ans=sol.check()
  row={"name":name,"theory":theory,"result":str(ans),"seconds":time.perf_counter()-start}
  if ans!=z3.unsat:row["detail"]=str(sol.model()) if ans==z3.sat else sol.reason_unknown()
  print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
 a,z,S,mu,t,Y,w,r,u,S1,S2,Sigma,qval,c,s,rho,e=z3.Reals("a z S mu t Y w r u S1 S2 Sigma qval c s rho e")
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
 Q=S+(h-1)*(b+S-2)/(k-h);q=lambda v:v/(2-v)
 base=[a>0,a<1,z>0,15*z<4,z<a,a+2*z<1,S>0,
       S<(1-z)/(1+z),2-S<b,2*a*(2-S)<1+a*a,Q<z3.Q(5,12)+z]
 for name,sign in [("Ka<=1",2*a<=1-a*a),("Ka>=1",2*a>=1-a*a)]:
  query("uniform short cap "+name,base+[sign,k*(2-S)<b-z3.Q(2,7)])
 query("two small top angles have positive cosine sum",[
       z>0,15*z<4,t>0,15*t<4,(1-z*z)*(1-t*t)<=4*z*t])
 cz=(1-z*z)/(1+z*z);sz=2*z/(1+z*z)
 ct=(1-t*t)/(1+t*t);st=2*t/(1+t*t)
 query("top seam inward depth is below z+t",[
       z>0,15*z<4,t>0,15*t<4,mu>=1,
       Y*(ct*sz+cz*st)==cz+ct-2*mu*cz*ct,Y>=z+t])
 query("whole near-diagonal interval gives R/T bound",[
       c>=s,s>=z3.Q(12,17),r>0,u>0,
       z3.Or(s*r+c*u<=1,c*r+s*u<=1),r+u>z3.Q(17,12)])
 query("both near-diagonal rotations give P/T bound",[
       c>=s,s>=z3.Q(12,17),rho>0,u>e,
       z3.Or(c*rho+s*(u-e)<=1,s*rho+c*(u-e)<=1),
       rho+u-e>z3.Q(17,12)])
 query("near-diagonal C direct roots give rational cap",[
       r+u<=w,w<=z3.Q(17,12),u>1-z,r>=z3.Q(5,12)+z],"QF_LRA")
 query("same F bottom diameter final contradiction",[
       Sigma==S1+S2,Sigma>z3.Q(7,12),S2<qval,
       S1+qval<=z3.Q(7,12)],"QF_LRA")

 aa,zz,tt,mm,LL,DD,SS,vv=sp.symbols("a z t mu L D S v")
 c=lambda x:(1-x*x)/(1+x*x)
 s=lambda x:2*x/(1+x*x)
 kk=lambda x:2*x/(1-x*x)
 bb=(1+aa*aa)/(1-aa*aa)
 K=kk(aa);H=kk(zz);g=(1-zz)/(1+zz)
 Qmu=SS+(H-1)*(bb+SS-2*mm)/(K-H)
 Qone=Qmu.subs(mm,1)
 F=bb-K*(2-g)
 E=F+(sp.Rational(5,12)+zz)/(sp.Rational(19,12)-zz)-sp.Rational(7,12)
 cap=sp.Rational(155,301)
 ids=[]
 def ident(name,expr):
  assert sp.cancel(expr)==0,(name,sp.factor(expr));ids.append(name)
 ident("mu relaxation of seam projection",
       Qmu-Qone-2*(mm-1)*(1-H)/(K-H))
 ident("seam projection affine slope",sp.diff(Qone,SS)-(K-1)/(K-H))
 ident("short-cap envelope identity",
       (F-sp.Rational(2,7))*(1+zz)-
       ((1-aa)/(1+aa)-sp.Rational(2,7)-zz*(3*K+sp.Rational(2,7)-bb)))
 ident("objective derivative in top angle",
       sp.diff(E,zz)+2*K/(1+zz)**2-2/(sp.Rational(19,12)-zz)**2)
 ident("objective derivative in bottom angle",
       sp.diff(F,aa)-(4*aa-2*(2-g)*(1+aa*aa))/(1-aa*aa)**2)
 ident("objective zero-angle deficit",
       E.subs(zz,0)-2*(cap-aa)/((1+aa)*(1+cap)))
 cp,sp_,ct_,st_=c(zz),s(zz),c(tt),s(tt)
 den=ct_*sp_+cp*st_
 YY=(cp+ct_-2*mm*cp*ct_)/den
 ident("top seam upper bound factor",
       zz+tt-YY.subs(mm,1)-zz*tt*(2-zz**2-tt**2)/((zz+tt)*(1-zz*tt)))
 ident("top seam lower-support identity",
       (YY-sp_*(1-cp*LL))*den-
       (cp*ct_*(LL+DD-2*mm)+cp*((1-ct_*DD)+
        (cp*ct_-sp_*st_)*(1-cp*LL))))
 ident("top first supports intersect",
       ct_*(2*mm-(1-sp_*YY)/cp)+st_*YY-1)
 ident("Phi derivative with its square relation",
       1-vv-(1+aa)**2/vv-(1-2*vv-1/vv)
       -(vv*vv-aa*(2+aa))/vv)
 constants=[]
 def positive(name,expr):
  expr=sp.simplify(expr);assert expr.is_positive is True,(name,expr)
  constants.append({"name":name,"exact":str(expr)})
 positive("low-a uniform cap margin",
          2-sp.Rational(17,15)-sp.Rational(1,4)-sp.Rational(1,14)-sp.Rational(5,12))
 positive("sqrt2 below 17/12 squared",sp.Rational(17,12)**2-2)
 positive("sqrt2 above 11/8 squared",2-sp.Rational(11,8)**2)
 C=sp.Rational(6,5)+sp.Rational(7,12)-sp.Rational(19,53)
 positive("Ka>=1 objective negative at z=1/9 squared",C*C-2)
 positive("objective uniform slope exceeds 2/3",
          sp.Rational(81,50)-sp.Rational(2592,2809)-sp.Rational(2,3))
 positive("initial objective slope contraction",sp.Rational(7,5)*(1+cap)-2)
 positive("objective decreasing on all z<4/15",
          sp.Rational(450,361)-sp.Rational(7200,6241))
 positive("Phi composite decreases",
          sp.Rational(1575,722)-sp.Rational(7200,6241))
 positive("large-z Phi endpoint deficit",
          sp.Rational(7,12)-sp.Rational(15,121)*(11-2*sp.sqrt(26))-sp.Rational(23,49))
 positive("top cosine above inward depth",sp.Rational(209,241)-sp.Rational(8,15))
 positive("actual upper root above seam height",sp.Rational(11,15)-sp.Rational(5,12))
 positive("near-diagonal interval has positive width",sp.Rational(1,2)-sp.Rational(12,17)**2)
 result={"queries":rows,"query_count":len(rows),"identities":ids,
         "identity_count":len(ids),"constants":constants,"constant_count":len(constants),
         "scope":"C with min normal coefficient >=12/17 and direct QU/Q2 excluded; two local inequalities; repeated-TOPmid forced top seam"}
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 (out/"S6_round41_geometry_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
if __name__=="__main__":main()
