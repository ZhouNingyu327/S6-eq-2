"""Exact algebraic example: entire six-line grid covered, target not covered.

The example is deliberately diagnostic, not a counterexample to S(6)=2.
All inequalities below are decided exactly by SymPy's algebraic sign logic.
"""
from pathlib import Path
import json
import sympy as sp

R=sp.Rational
mu=1+R(1,10**10)
a=1/sp.sqrt(7);x=R(2,5)+R(2,10**9);z=R(1,5)-R(1,10**9);t=R(1,10**5)
L1=R(4,3);L2=1+R(3,10**5);L4=mu;D=mu
c=lambda v:(1-v*v)/(1+v*v)
s=lambda v:2*v/(1+v*v)
K=lambda v:2*v/(1-v*v)
short=lambda v,L:sp.cancel((1+v*v-2*v*L)/(1-v*v))
root=lambda v:sp.cancel(v-(mu-1)/K(v))
S1=short(a,L1);S2=short(x,L2);S4=short(z,L4);A=short(t,D)
U1,U2,U4,Uw=[root(v) for v in (a,x,z,t)]
l=R(623,1000);r=R(59999999821,10**11)
u=(1-R(3,5)*r)/R(4,5);d=R(5,4)-u
alpha=-R(4,5)*l;beta=R(4,5)*u-1
fcx=(S1-S2)/2
vF=1/sp.sqrt(2)+fcx # fcx is negative.
checks=[]
def check(name,expr,strict=True):
    expr=sp.simplify(expr)
    ok=expr.is_positive if strict else expr.is_nonnegative
    assert ok is True,(name,str(expr),ok)
    checks.append({"name":name,"relation":">0" if strict else ">=0",
                   "value_exact":str(expr)})
def identity(name,expr):
    expr=sp.simplify(expr);assert expr==0,(name,expr)
    checks.append({"name":name,"relation":"=0","value_exact":"0"})

for name,v,L in [("V1",a,L1),("V2",x,L2),("V4",z,L4),("W",t,D)]:
    identity(name+" unit normals",c(v)**2+s(v)**2-1)
    check(name+" anchored long leg",L-mu,False)
    check(name+" cosine projection",1-c(v)*L,False)
    check(name+" sine projection",1-s(v)*L,False)
    check(name+" positive central root",root(v))
check("LEFT boundary interval meeting",L1+S4-2*mu)
check("RIGHT boundary interval meeting",L2+A-2*mu)
identity("TOP boundary interval meeting",L4+D-2*mu)
check("BOTTOM complete gap fits F chord",sp.sqrt(2)-(2*mu-S1-S2))
check("negative H closed interval meeting",l+U1-mu)
check("positive H closed interval meeting",r+U2-mu)
check("positive V closed interval meeting",u+U4-mu)
check("negative V closed interval meeting",d+vF-mu)
check("F center lies left of V",-fcx)
check("F contains BOTTOMmid",1/sp.sqrt(2)+fcx)
check("F entire square below H",mu-1/sp.sqrt(2))
check("W does not contain RIGHTmid",mu-A)
identity("C two perpendicular unit normals",R(4,5)**2+R(3,5)**2-1)
for name,val in [("l",l),("r",r),("u",u),("d",d)]:
    check("C positive "+name,val)
    check("C "+name+" below one",1-val)
    check("C "+name+" below global root cap",2-mu-val)
identity("C actual left first face",alpha+R(4,5)*l)
identity("C actual right second face",beta+R(3,5)*r)
identity("C actual top second face",beta+1-R(4,5)*u)
identity("C actual bottom second face",beta+R(4,5)*d)
check("C left endpoint other lower face",R(3,5)*l-beta)
check("C left endpoint other upper face",beta+1-R(3,5)*l)
check("C right endpoint first lower face",R(4,5)*r-alpha)
check("C right endpoint first upper face",alpha+1-R(4,5)*r)
check("C top endpoint first lower face",R(3,5)*u-alpha)
check("C top endpoint first upper face",alpha+1-R(3,5)*u)
check("C bottom endpoint first lower face",-R(3,5)*d-alpha)
check("C bottom endpoint first upper face",alpha+1+R(3,5)*d)
# Every interval used above is a true trace of the displayed unit square.
# Convexity gives the complete closed interval from the two included ends.

qx,qy=-R(3,4),R(1,8)
check("rational witness lies strictly inside target, x",mu+qx)
check("rational witness lies strictly inside target, y",mu-qy)
check("witness outside V1 first upper face",
      s(a)*(qx+mu)+c(a)*(qy+mu)-1)
check("witness outside V4 second upper face",
      -s(z)*(qx+mu)+c(z)*(mu-qy)-(1-s(z)*L4))
check("witness outside C first lower face",
      alpha-(R(4,5)*qx+R(3,5)*qy))
check("witness outside V2 by diameter",(qx-mu)**2+(qy+mu)**2-2)
check("witness outside W by diameter",(qx-mu)**2+(qy-mu)**2-2)
check("witness above all of F",qy+mu-1/sp.sqrt(2))

X=(1/c(a)+S4-2*mu)/(K(a)-K(z))
e=mu-S4-K(z)*X
check("new seam point lies strictly inside the target from LEFT",X)
check("new seam point violates C first lower face",
      alpha-(R(4,5)*(X-mu)+R(3,5)*e))

out={
 "claim":"six actual unit squares cover all four boundary edges and both central axes, but do not cover the target",
 "not_claimed":"a cover of the target or a counterexample to S(6)=2",
 "parameters":{"mu":str(mu),"a":str(a),"x":str(x),"z":str(z),"t":str(t),
               "L1":str(L1),"L2":str(L2),"L4":str(L4),"D":str(D),
               "C_alpha":str(alpha),"C_beta":str(beta),
               "F_center_x":str(fcx),"F_center_y":str(-mu)},
 "uncovered_rational_point":[str(qx),str(qy)],
 "checks":checks,"check_count":len(checks),
 "numerical_display_only":{"Sigma":float(S1+S2),"bottom_gap":float(2*mu-S1-S2),
                           "seam":[float(X-mu),float(e)]}
}
result_dir=Path("outputs") if Path("outputs").is_dir() else Path(".")
(result_dir/"S6_round40_grid_counterexample_verification.json").write_text(
    json.dumps(out,indent=2),encoding="utf-8")
print(json.dumps({"result":"exact checks passed","checks":len(checks),
                  "uncovered_point":out["uncovered_rational_point"]}))
