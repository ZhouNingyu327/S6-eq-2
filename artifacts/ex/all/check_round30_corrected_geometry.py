"""Exact corrected geometry checks; no entire three-meeting exclusion is claimed."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        solver=z3.SolverFor(theory);solver.set(timeout=20000);solver.add(*cs)
        start=time.perf_counter();ans=solver.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        if ans!=z3.unsat:
            row["detail"]=str(solver.model()) if ans==z3.sat else solver.reason_unknown()
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    mu,B,hc,l,r,u,d,c,s,K=z3.Reals("mu B hc l r u d c s K")
    query("side-gap effective grid implies hc-d>mu",[
        mu>1,B<1,12*mu<=8+2*B+hc+mu-d,hc-d<=mu],"QF_LRA")
    query("C side and TOP contact impossible with F H nonempty",[
        mu>1,B<1,d>=0,12*mu<=8+3*B+mu-d],"QF_LRA")
    query("C TOP contact impossible in three meetings with F H nonempty",[
        mu>1,B<1,12*mu<=8+2*B+2*mu],"QF_LRA")
    query("asymmetric chord first active down face",[
        mu>1,l<mu,K>0,K<=1,r<=K*d,d>=0,l+r-d>mu])
    query("asymmetric chord second active down face",[
        mu>1,l>0,r>0,d>0,u>=z3.Q(1,2),l<mu,r<mu,
        c>=s,s>0,c*c+s*s==1,s*l<=c*d,
        c*r+s*u<=1,c*(l+r)<=1,l+r-d>mu])
    z,J,H,A,D,L2,L4,S1,S2,U1,U2,a,b,f=z3.Reals(
        "z J H A D L2 L4 S1 S2 U1 U2 a b f")
    query("CORRECT TOP/H cap H<delta(z)",[
        mu>1,B<1,z>0,z<1,D+L4>=2*mu,D+H<=B,
        L4*(1-z*z)<=1+z*z,H*(1-z*z)>=2*z*z])
    query("CORRECT RIGHT/V cap J<delta(x)",[
        mu>1,B<1,z>0,z<1,A+L2>=2*mu,A+J<=B,
        L2*(1-z*z)<=1+z*z,J*(1-z*z)>=2*z*z])
    query("three-meeting horizontal budget retains J",[
        hc+f+U1+U2+H>=2*mu,b>=2*mu-S1-S2,b+f<=B,
        A+D+H+J<=2,A+L2>=2*mu,D+L4>=2*mu,
        hc<8*mu-B-2-(L2+S2+U2)-(L4+S1+U1)+J],"QF_LRA")
    query("LEFT adjacent lemma gives hc>1+2z-z²+J",[
        mu>1,B<1,U1<a,L2+S2+U2<2,L4+S1+a+2*z-z*z<=2,
        hc>=8*mu-B-2-(L2+S2+U2)-(L4+S1+U1)+J,
        hc<=1+2*z-z*z+J])
    query("three-meeting sum cancels J",[
        hc>1+2*z-z*z+J,u>1-z-J,hc+u<=2+z-z*z])
    query("z at least 1/7 gives sum>104/49",[
        7*z>=1,15*z<4,hc+u>2+z-z*z,49*(hc+u)<=104])
    query("large z full area contradiction",[
        hc>1,70*hc<99,49*(hc+u)>104,hc*u<=1])
    v=z3.Real("v")
    query("small sqrt polynomial decreases",[
        v>=0,12*v<=5,4*v**3+v*v-6*v-1> -z3.Q(29,54)])
    P=z3.Q(8,9)-v-3*v*v+v**3/3+v**4
    query("small sqrt polynomial positive margin",[
        v>=0,12*v<=5,P<z3.Q(13,2304)])
    query("J <=sqrt(z)/3 makes lower u positive",[
        z>0,7*z<1,v>0,v*v==z,J>=0,3*J<=v,1-z-J<=0])
    query("small actual hc*u contradicts too-short J",[
        z>0,7*z<1,v>0,v*v==z,J>=0,3*J<=v,
        hc>1+2*z-z*z+J,u>1-z-J,hc*u<=1])
    query("three-meeting u>41/70",[
        z>0,z<1,hc+u>2+z-z*z,70*hc<99,70*u<=41])
    query("side gaps force J>1/2-z",[
        mu>1,u<z3.Q(1,2),U1<z,u+U1+J>=mu,J<=z3.Q(1,2)-z],"QF_LRA")
    query("RIGHT gap with LEFT meeting forces J>7/30",[
        15*z<4,J>z3.Q(1,2)-z,30*J<=7],"QF_LRA")
    x1,y1,x2,y2,x3,y3=z3.Reals("x1 y1 x2 y2 x3 y3")
    coords=[x1,y1,x2,y2,x3,y3]
    det=(x2-x1)*(y3-y1)-(x3-x1)*(y2-y1)
    query("unit-square triangle determinant <=1",
        [*[p>=0 for p in coords],*[p<=1 for p in coords],det>1])
    query("unit-square triangle determinant >=-1",
        [*[p>=0 for p in coords],*[p<=1 for p in coords],det< -1])
    # Symbolic identities and exact local counterexample to the withdrawn cap.
    Z,V,JJ,HH=sp.symbols("z v J h")
    identities=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,name;identities.append(name)
    cc=(1-HH*HH)/(1+HH*HH);ss=2*HH/(1+HH*HH)
    ident("asymmetric circle simplification",(1/cc-1)/(ss/cc)**2-cc/(1+cc))
    product=(1+2*Z-Z*Z+JJ)*(1-Z-JJ)
    ident("J derivative",sp.diff(product,JJ)-(-3*Z+Z*Z-2*JJ))
    ident("small sqrt product",
        (product-1).subs({Z:V*V,JJ:V/3})-
        V*V*(sp.Rational(8,9)-V-3*V*V+V**3/3+V**4))
    ident("sum cancels J",1+2*Z-Z*Z+JJ+1-Z-JJ-(2+Z-Z*Z))
    ident("large area quadratic margin",
        HH*(sp.Rational(104,49)-HH)-sp.Rational(34353,34300)-
        (sp.Rational(99,70)-HH)*(HH-(sp.Rational(104,49)-sp.Rational(99,70))))
    constants=[]
    def exact(name,expr,expected=None,positive=False):
        value=sp.factor(expr)
        if expected is not None:
            assert value==expected,(name,value,expected)
        if positive:
            assert value>0,(name,value)
        constants.append({"name":name,"value":str(value)})
    exact("rational chord cap square margin",sp.Rational(99,70)**2-2,sp.Rational(1,4900))
    exact("large sum lower",2+sp.Rational(1,7)-sp.Rational(1,49),sp.Rational(104,49))
    exact("large quadratic left",sp.Rational(104,49)-1,sp.Rational(55,49))
    exact("large quadratic right",
        sp.Rational(99,70)*(sp.Rational(104,49)-sp.Rational(99,70)),sp.Rational(34353,34300))
    exact("sqrt polynomial derivative bound",
        4*sp.Rational(5,12)**3+sp.Rational(5,12)**2-1,-sp.Rational(29,54))
    poly=sp.Rational(8,9)-V-3*V*V+V**3/3+V**4
    exact("sqrt polynomial endpoint",poly.subs(V,sp.Rational(5,12)),sp.Rational(13,2304))
    exact("sqrt(1/7)<5/12 square gap",sp.Rational(5,12)**2-sp.Rational(1,7),positive=True)
    exact("three-meeting u lower",2-sp.Rational(99,70),sp.Rational(41,70))
    # A genuine pair of unit corner squares, not a full six-square cover.
    mm=sp.Rational(1001,1000);cw=sp.Rational(3,5);sw=sp.Rational(4,5)
    beta=sp.Rational(99,125);zz=sp.Rational(1,10)
    top=beta/sw;right=(1-beta)/cw
    ymin=(sw*mm-beta)/cw;ymax=(1-cw*mm)/sw;jj=ymax-ymin
    l4=sp.Rational(101,99);c4=sp.Rational(99,101);s4=sp.Rational(20,101)
    u4=(1-mm*c4)/s4
    assert cw*cw+sw*sw==1 and c4*c4+s4*s4==1
    assert 0<top<mm and 0<right<mm and 0<ymin<ymax<mm
    assert l4>mm and c4*l4==1 and s4*l4<=1 and u4>0
    assert l4+top>2*mm
    # Horizontal trace is empty: its inward minimum X exceeds maximum X.
    xmin=(cw*mm-1+beta)/sw;xmax=(1-sw*mm)/cw
    assert xmin>xmax
    delta_z=2*zz*zz/(1-zz*zz)
    exact("local example actual J",jj,sp.Rational(1163,2400))
    exact("local example false-cap violation J-delta(z)",jj-delta_z,positive=True)
    exact("local example genuine TOP meeting surplus",l4+top-2*mm,positive=True)
    example={"mu":str(mm),"W_inward_normals":[str(cw),str(sw)],
        "W_beta":str(beta),"W_TOP_leg":str(top),"W_RIGHT_leg":str(right),
        "W_V_inward_y_min":str(ymin),"W_V_inward_y_max":str(ymax),
        "W_J":str(jj),"W_H":"empty","V4_halfangle":str(zz),"V4_long_TOP":str(l4),
        "V4_U":str(u4),"delta_z":str(delta_z),
        "scope":"Exact local unit-corner pair disproves J<delta(z) from TOP meeting; not a six-square cover"}
    result={"queries":rows,"symbolic_identities":identities,"constants":constants,
        "local_counterexample":example,
        "totals":{"UNSAT":len(rows),"NRA":sum(row["theory"]=="QF_NRA" for row in rows),
                  "LRA":sum(row["theory"]=="QF_LRA" for row in rows),
                  "symbolic_identities":len(identities),"constants":len(constants)},
        "scope":"Correct TOP/H and RIGHT/V caps; side-gap nonempty-F implies u<1/2; "
                "three-meeting nonempty-F implies z<1/7, 9J²>z and u>41/70",
        "not_proved":"Entire LEFT-gap, RIGHT-gap, three-meeting families; entire G2; S(6)=2",
        "historical_input":"round13 adjacent-corner lemma includes 266 exact coefficients; not replayed",
        "withdrawn_candidate_not_replayed":True}
    Path(__file__).with_name("round30_corrected_geometry_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
