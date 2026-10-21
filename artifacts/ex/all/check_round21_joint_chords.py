"""Small exact scalar checks for joint long-chord and midpoint constraints."""
from pathlib import Path
import itertools
import json
import time
import sympy as sp
import z3


def query(name, premises, theory="QF_LRA"):
    solver=z3.SolverFor(theory)
    solver.set(timeout=30000)
    solver.add(*premises)
    start=time.perf_counter()
    answer=solver.check()
    row={"name":name,"theory":theory,"result":str(answer),
        "seconds":time.perf_counter()-start}
    if answer!=z3.unsat:
        row["detail"]=str(solver.model()) if answer==z3.sat else solver.reason_unknown()
    return row


def main():
    rows=[]
    mu,B,ell,u,S4,U4=z3.Reals("r21_mu r21_B r21_ell r21_u r21_S4 r21_U4")
    rows.append(query("T8: any left gap contradicts two nonempty parallel budgets",[
        mu>1,B<1,ell>=mu-S4,u>=mu-U4,ell+u<=B,S4+U4<=B]))

    x,y,w,L1,epsilon=z3.Reals("r21_x r21_y r21_w r21_L1 r21_epsilon")
    rows.append(query("left meeting gives w > 3x/2",[
        x>0,15*x<4,w>0,w<1,
        L1*(1-w*w)<=1+w*w,x*(3-L1)<L1-1,
        2*w<=3*x],"QF_NRA"))
    rows.append(query("top angle and cosine excess give y+epsilon <5x/12",[
        x>0,15*x<4,y>0,5*y<6*x*x,
        epsilon*(1-y*y)==2*y*y,
        12*(y+epsilon)>=5*x],"QF_NRA"))
    rows.append(query("cosine excess epsilon < y",[
        y>0,15*y<4,epsilon*(1-y*y)==2*y*y,
        epsilon>=y],"QF_NRA"))

    c,s,h,r,d=z3.Reals("r21_c r21_s r21_h r21_r r21_d")
    normal=[c>0,s>0,c>=s,c*c+s*s==1,mu>1]
    rows.append(query("C positive orientation cannot reach u>11/15",normal+[
        u>z3.RealVal("11/15"),c*mu+s*u<=1],"QF_NRA"))
    rows.append(query("C negative orientation half-angle h<x/(2-x)",normal+[
        x>0,15*x<4,u>1-x,s*mu+c*u<=1,h*(1+c)==s,
        (2-x)*h>=x],"QF_NRA"))
    Delta=z3.Real("r21_Delta")
    rows.append(query("C right ray r < Delta(x)",[
        x>0,15*x<4,mu>1,h>=0,(2-x)*h<x,
        2*(1-x)*Delta==x*x,
        (1-h*h)*(mu+r)<=1+h*h,r>=Delta],"QF_NRA"))
    rows.append(query("C downward ray d < h",normal+[
        h*(1+c)==s,c*mu+s*d<=1,d>=h],"QF_NRA"))

    q,e=z3.Reals("r21_q r21_e")
    rows.append(query("bottom-left gap and right gap endpoints cannot both lie in F",[
        mu>1,e>=0,e<1,q>e,
        (mu+q)**2+(mu-e)**2<=2],"QF_NRA"))
    rows.append(query("four outer edges cannot all be covered by four corner units",[
        mu>1,8*mu<=8]))
    E,D,J,f=z3.Reals("r21_E r21_D r21_J r21_f")
    rows.append(query("T8 right meeting and F positive horizontal contradict bottom/horizontal budget",[
        x>0,E<x,q>x,J>=0,D>q+f,D+J<E+f]))
    beta=z3.Real("r21_beta")
    unit_basis=[c>=s,s>=0,c*c+s*s==1,mu>1,e>=0,4*e<1,
        15*beta>11]
    rows.append(query("F positive orientation cannot contain bottom midpoint and high right gap",unit_basis+[
        c*mu+s*(mu-e)<=1],"QF_NRA"))
    rows.append(query("F negative orientation cannot contain bottom midpoint and far horizontal point",unit_basis+[
        s*beta+c*mu<=1],"QF_NRA"))
    rows.append(query("T8 bottom meeting without positive F is impossible",[
        x>0,x<1,r+y<E,E<x,r+y>=1]))

    rows.append(query("q >6x/(2+3x) follows from w>3x/2",[
        x>0,15*x<4,w>0,2*w>3*x,q*(1+w)>2*w,
        q*(2+3*x)<=6*x],"QF_NRA"))
    rows.append(query("d+E <6x/5 from the new chord bounds",[
        x>0,26*d<15*x,132*E<79*x,5*(d+E)>=6*x]))
    b,v=z3.Reals("r21_b r21_v")
    rows.append(query("T8 nonpositive horizontal: bottom chord plus vertical ray exceed unit budget",[
        x>0,15*x<4,q*(2+3*x)>6*x,
        d>=0,E>=0,D>=0,J>=0,5*(d+E)<6*x,D+J<E,
        b>1+q-D,v>1-d-J,b+v*v<=2],"QF_NRA"))

    # G3: four midpoint hosts force one of the two cyclic assignments.
    L2,S2,U2,L3,S3,U3,L4,S1,U1,vert=z3.Reals(
        "r21_L2 r21_S2 r21_U2 r21_L3 r21_S3 r21_U3 r21_L4 r21_S1 r21_U1 r21_vert")
    anchors=[mu>1,B<1,
        L1>=mu,L2>=mu,L3>=mu,L4>=mu,
        S1>=0,S2>=0,S3>=0,S4>=0,U1>=0,U2>=0,U3>=0,U4>=0,
        L1+S1+U1<2,L2+S2+U2<2,L3+S3+U3<2,L4+S4+U4<2,
        L3+S4>=2*mu,ell>=2*mu-L4-S1]
    rows.append(query("G3 cyclic all-corner-midpoint case: F vertical empty impossible",anchors+[
        vert>=2*mu-U1-U3,ell+vert<=B]))
    rows.append(query("G3 cyclic F vertical nonempty: right meeting impossible",anchors+[
        u>=mu-U3,mu+ell+r+u<2,
        b>=2*mu-L1-S2,b+f<=B,r+f+U2>=mu,
        L2+S3>=2*mu]))
    vF,RF=z3.Reals("r21_vF r21_RF")
    rows.append(query("G3 cyclic F right gap plus vertical budgets impossible",anchors+[
        ell+vert<=B,RF>=mu-S3,RF+vF<=B,
        vert+vF+U1+U3>=2*mu]))

    # G2 near right gap: no old double-meeting angle bound is used here.
    up,right_height=z3.Reals("r21_up r21_right_height")
    rows.append(query("G2 right gap: y<=1/2 forces upper height >1/2",[
        y>0,2*y<=1,up>1-y,2*up<=1]))
    rows.append(query("G2 right gap: y>=1/2 forces right height >1/2",[
        y<1,2*y>=1,right_height*(1+y)>2*y,2*right_height<=1],"QF_NRA"))
    rows.append(query("Delta(m)<m for 0<m<4/15",[
        x>0,15*x<4,2*(1-x)*Delta==x*x,Delta>=x],"QF_NRA"))
    t2=z3.Real("r21_t2")
    rows.append(query("G4 diagonal negative, TR top-midpoint duplicate: y controls C contradiction",[
        mu>1,r<y,y+t2<1,U2<t2,r+U2>=mu]))
    rows.append(query("G4 diagonal negative, TR top-midpoint duplicate: x controls bottom contradiction",[
        mu>1,B<1,r<x,S1+x<1,S2+U2<1,r+U2>=mu,
        b>=2*mu-S1-S2,b+f<=B,f>=0]))
    rows.append(query("G4 diagonal nonpositive, TR top-midpoint duplicate: long bottom chord and vertical ray",[
        x>0,15*x<4,q>z3.RealVal("3/2")*x,
        11*S2<2*x,d>=0,26*d<15*x,
        b>1+q-S2,v>1-d,b+v*v<=2],"QF_NRA"))

    X,DD,JJ,AA,EE=sp.symbols("x D J d E")
    K=sp.Rational(6,5)
    polynomial=5-18*X+18*X*X
    identity=6*X/(2+3*X)-2*K*X+K*K*X*X
    assert sp.cancel(identity-6*X*polynomial/(25*(2+3*X)))==0
    assert polynomial.subs(X,sp.Rational(4,15))==sp.Rational(37,25)
    allocation=(1-AA-JJ)**2-DD-(1-AA-EE)**2
    assert sp.expand(allocation-((EE-JJ)*(2-2*AA-EE-JJ)-DD))==0
    rho=2*X**2/(1-X**2)
    half=sp.symbols("h")
    assert sp.cancel(2*(X/(2-X))**2/(1-(X/(2-X))**2)
        -X**2/(2*(1-X)))==0
    constants={
        "9/4 * (4/15) * (23/15) =23/25 <1":
            sp.Rational(9,4)*sp.Rational(4,15)*sp.Rational(23,15)==sp.Rational(23,25)
            and sp.Rational(23,25)<1,
        "1256/3125 <5/12":sp.Rational(1256,3125)<sp.Rational(5,12),
        "15/26+79/132 <6/5":sp.Rational(15,26)+sp.Rational(79,132)<sp.Rational(6,5),
        "6/5 *4/15 =8/25 <1/2":
            K*sp.Rational(4,15)==sp.Rational(8,25) and sp.Rational(8,25)<sp.Rational(1,2),
        "32/375 <1/4":sp.Rational(32,375)<sp.Rational(1,4),
        "sqrt(2)-1 <11/15":sp.sqrt(2)-1<sp.Rational(11,15),
        "sqrt(2)<3/2":2*2**2<3**2,
        "2/11+15/13 <3/2":sp.Rational(2,11)+sp.Rational(15,13)<sp.Rational(3,2),
    }
    assert all(constants.values())
    cyclic=sorted(v for v in itertools.product([1,2],[2,3],[3,4],[4,1])
        if len(set(v))==4)
    assert cyclic==[(1,2,3,4),(2,3,4,1)]
    result={
        "status":"all exact checks passed" if all(row["result"]=="unsat" for row in rows) else "inspect",
        "queries":rows,"query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "symbolic_checks":4,
        "constant_checks":{key:bool(value) for key,value in constants.items()},
        "four_midpoint_corner_matchings":[list(v) for v in cyclic],
        "new_scope":"entire G4 T8 excluded; G3/G4 cannot have all four midpoints with corner hosts; free upper corner in each remaining G4 representative has no outer midpoint; near G2 C right gap implies C avoids bottom",
        "proof_method":"hand long-chord bounds, nonempty parallel traces, endpoint diameter, overlap allocation",
        "no_search":"no target point enumeration, whole layouts, angle samples or interval partition",
        "not_proved":"other G4 representatives; remaining G3/G2; S(6)=2",
    }
    Path(__file__).with_name("round21_joint_chord_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)
    assert result["status"]=="all exact checks passed"


if __name__=="__main__":
    main()
