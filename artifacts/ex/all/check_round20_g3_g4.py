"""Small exact checks for G3/G4 branch reductions, not covering searches."""
from pathlib import Path
import itertools
import json
import time

import sympy as sp
import z3


def query(name, assumptions, theory="QF_LRA", role="new scalar consequence"):
    solver=z3.SolverFor(theory)
    solver.set(timeout=20000)
    solver.add(*assumptions)
    start=time.perf_counter()
    result=solver.check()
    row={"name":name,"role":role,"theory":theory,"result":str(result),
        "seconds":time.perf_counter()-start}
    if result!=z3.unsat:
        row["detail"]=str(solver.model()) if result==z3.sat else solver.reason_unknown()
    return row


def main():
    rows=[]
    mu,B=z3.Reals("r20_mu r20_B")
    rows.append(query("G3 F vertical nonempty requires top or bottom corner gap",
        [mu>1,B<1,12*mu<=8+2*mu+2*B]))

    L2,S2,U2,L4,S4,U4,A,D,r,u,ell,f=z3.Reals(
        "r20_L2 r20_S2 r20_U2 r20_L4 r20_S4 r20_U4 r20_A r20_D r20_r r20_u r20_ell r20_f")
    quarter=[mu>1,L2+S2+U2<2,L4+S4+U4<2,
        mu+r+ell+u<2,
        4*mu<=L2-mu+U2+L4-mu+U4+2+r+u+f]
    rows.append(query("G4 diagonal upper-right perimeter bound",quarter+[
        4*mu>=8-3*mu-S2-S4-ell+f]))
    b=z3.Real("r20_b")
    rows.append(query("G4 diagonal positive F horizontal is impossible",quarter+[
        B<1,A+D<=2,ell>=2*mu-D-S4,
        b>=2*mu-A-S2,b+f<=B]))
    rows.append(query("G4 diagonal F nonpositive horizontal and left gap impossible",quarter+[
        f==0,ell>=mu-S4,S2>=0]))

    L3,S3,U3,H2=z3.Reals("r20_L3 r20_S3 r20_U3 r20_H2")
    rows.append(query("G4 T8 nonpositive F horizontal and left gap impossible",[
        mu>1,S3+U3<1,L4+S4+U4<2,L4+S3>=2*mu,
        mu+r+ell+u<2,ell>=mu-S4,
        r+U3+H2>=mu,u+U4>=mu,H2<=1]))
    c,s,H=z3.Reals("r20_c r20_s r20_H")
    rows.append(query("a corner's single central horizontal trace is shorter than one",[
        c>0,s>0,c*c+s*s==1,mu>1,H>=1,c*H+s*mu<=1],"QF_NRA"))

    rows.append(query("near three-meeting lemma: C cannot also touch bottom",[
        mu>1,B<1,12*mu<=8+2*mu+2*B],
        role="historical lemma applicability with C midpoint allowed"))
    S3n,U3n,Hn,Jn,h,fn,bn,q,t=z3.Reals(
        "r20_S3n r20_U3n r20_Hn r20_Jn r20_h r20_fn r20_bn r20_q r20_t")
    rows.append(query("near three-meeting exclusion does not need C to avoid midpoints",[
        mu>1,B<1,L2+S2+U2<2,L3+S3n+U3n<2,L4+S4+U4<2,
        L2+S3n>=2*mu,L3+S4>=2*mu,L4+D>=2*mu,
        A+D+Hn+Jn<=2,Jn>=0,bn>=2*mu-A-S2,bn+fn<=B,
        h+fn+U2+U4+Hn>=2*mu,U2<t,
        L3+S2+t+q<=2,h+1-q<2],
        role="historical lemma applicability with C midpoint allowed"))
    L1,S1,U1,Af,Df,Hf=z3.Reals("r20_L1 r20_S1 r20_U1 r20_Af r20_Df r20_Hf")
    rows.append(query("far three-meeting J=0 exclusion does not need C to avoid midpoints",[
        mu>1,B<1,L2+S2+U2<2,L1+S4>=2*mu,
        L2+Af>=2*mu,L4+Df>=2*mu,Af+Df+Hf<=2,
        bn>=2*mu-S1-S2,bn+fn<=B,
        h+fn+U1+U2+Hf>=2*mu,U1<t,L4+S1+t+q<=2,h+1-q<2],
        role="historical lemma applicability with C midpoint allowed"))

    lp,yp,loU,loV=z3.Reals("r20_lp r20_yp r20_loU r20_loV")
    axis=[c>=0,s>=0,c*c+s*s==1,mu>1,lp>0]
    for a0,b0 in [(-c*lp,s*lp),(c*mu+s*yp,-s*mu+c*yp)]:
        axis += [loU<=a0,a0<=loU+1,loV<=b0,b0<=loV+1]
    axis += [z3.Or(loU>0,loU+1<0,loV>0,loV+1<0)]
    rows.append(query("axis propagation, arbitrary translated unit",axis,"QF_NRA",
        role="fresh historical input check"))

    lpar,rpar,dpar=z3.Reals("r20_lpar r20_rpar r20_dpar")
    parallel=[c>=0,s>=0,c*c+s*s==1,mu>1,lpar>=0,rpar>=0,lpar+rpar>=1]
    for p1,p2 in itertools.combinations([(0,0),(0,lpar),(mu,dpar),(mu,dpar+rpar)],2):
        dx,dy=p1[0]-p2[0],p1[1]-p2[1]
        a0,b0=c*dx+s*dy,-s*dx+c*dy
        parallel += [a0>=-1,a0<=1,b0>=-1,b0<=1]
    rows.append(query("two genuinely nonempty parallel traces total <1",parallel,"QF_NRA",
        role="fresh historical input check"))

    beta,Hlong=z3.Reals("r20_beta r20_Hlong")
    rows.append(query("long chord plus perpendicular traces <2",[
        c>0,s>0,c*c+s*s==1,mu>1,mu*c<=1,mu*s<=1,
        beta>=mu*s,beta<=1,Hlong>=mu,Hlong*c<=1,Hlong*s<=beta,
        Hlong*c*s+s*(1-beta)+c*(1-mu*c)>=2*c*s],"QF_NRA",
        role="fresh historical input check"))
    lray,rray,uray=z3.Reals("r20_lray r20_rray r20_uray")
    rows.append(query("three rays in a unit: horizontal + up^2 <=2",[
        c>=0,s>=0,c*c+s*s==1,lray>=0,rray>=0,uray>=0,
        c*(lray+rray)<=1,s*(lray+rray)<=1,
        c*lray+s*uray<=1,s*rray+c*uray<=1,
        lray+rray+uray*uray>2],"QF_NRA",
        role="fresh historical input check"))

    # A genuine exact counterexample to a proposed two-block grid bound.
    # It is NOT a six-square covering. All expressions are algebraic exact.
    M=sp.Rational(101,100)
    Q=sp.sqrt(2)/2
    centreC=-sp.Rational(1,2)
    centreF=sp.Rational(19,20)
    assert M+centreC<Q and -centreC<Q
    assert centreF>Q and M-centreF<Q
    assert Q<M and centreC+Q<centreF-Q
    C_horizontal=M+centreC+Q
    C_left=2*(Q-(M+centreC))
    C_vertical=2*(Q+centreC)
    F_horizontal=M-centreF+Q
    F_right=2*(Q-(M-centreF))
    total=sp.simplify(C_horizontal+C_left+C_vertical+F_horizontal+F_right)
    assert sp.simplify(total-(4*sp.sqrt(2)-sp.Rational(157,100)))==0
    assert total>4
    counterexample={
        "classification":"exact local counterexample to a candidate lemma, not a target covering",
        "target_half_side":str(M),
        "C":"|x+1/2|+|y| <= sqrt(2)/2",
        "F":"|x-19/20|+|y| <= sqrt(2)/2",
        "anchors":"C contains origin and left midpoint; F contains right midpoint and excludes origin",
        "F_vertical_trace":"empty",
        "both_top_bottom_traces":"empty for C and F",
        "horizontal_traces_disjoint":True,
        "C_grid_length":str(sp.simplify(C_horizontal+C_left+C_vertical)),
        "F_grid_length":str(sp.simplify(F_horizontal+F_right)),
        "union_grid_length":str(total),
        "union_grid_length_approx":float(total),
        "false_candidate":"|(C union F) intersect six-line target grid| <=4",
        "not_proved":"the uncovered horizontal gap and all four corners have not been covered by four more units",
    }
    Path(__file__).with_name("round20_G3_local_counterexample.json").write_text(
        json.dumps(counterexample,ensure_ascii=False,indent=2),encoding="utf-8")

    g3=list(itertools.product([3,4],[1,2]))  # top/bottom hosts
    def horizontal_reflect(pair):
        refl={1:4,4:1,2:3,3:2}
        return (refl[pair[1]],refl[pair[0]])
    g3_orbits=[]
    unused=set(g3)
    while unused:
        pair=min(unused)
        orbit=sorted({pair,horizontal_reflect(pair)})
        g3_orbits.append(orbit)
        unused.difference_update(orbit)
    assert len(g3_orbits)==3
    g4=sorted(pair for pair in itertools.product([3,4],[2,3]) if pair[0]!=pair[1])
    assert g4==[(3,2),(4,2),(4,3)]
    result={
        "status":"exact checks passed" if all(row["result"]=="unsat" for row in rows) else "inspect failed query",
        "queries":rows,"query_count":len(rows),
        "new_scalar_consequence_queries":6,
        "historical_applicability_and_input_queries":7,
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "G3_host_orbits":[[list(pair) for pair in orbit] for orbit in g3_orbits],
        "G4_ordered_host_representatives":[list(pair) for pair in g4],
        "exact_counterexample":counterexample,
        "proof_scope":"G3 top/bottom gap necessity; G4 diagonal positive phase and remaining negative phase J>0; G4 T8 negative phase and empty-phase left meeting",
        "historical_dependency":"T8 negative exclusion and diagonal J>0 condition use the audited round13 adjacent-corner certificate",
        "not_proved":"entire G3; entire G4; remaining G2; S(6)=2",
        "no_search":"no target point enumeration, pose optimization, angle sampling or interval subdivision",
    }
    Path(__file__).with_name("round20_g3_g4_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)
    assert result["status"]=="exact checks passed"


if __name__=="__main__":
    main()
