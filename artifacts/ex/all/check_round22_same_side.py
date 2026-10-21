"""Hand scalar checks for same-side G4: nonpositive F and bottom meeting."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def query(name, premises, theory="QF_NRA"):
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
    mu,k,y,r,dk,L2=z3.Reals("s22_mu s22_k s22_y s22_r s22_dk s22_L2")
    rows.append(query("right meeting puts top angle y below Delta(k)",[
        y>0,L2<2,y*(3-L2)<L2-1,L2<=1+dk,y>=dk]))
    dy=z3.Real("s22_dy")
    rows.append(query("nonpositive F: C cannot contain the top-axis inner endpoint",[
        k>0,7*k<3,y>0,2*(1-k)*dk==k*k,y<dk,
        2*(1-y)*dy==y*y,r<dy,k<r]))
    T,c,s,D,U,u,g,ell=z3.Reals("s22_T s22_c s22_s s22_D s22_U s22_u s22_g s22_ell")
    normal=[c>0,s>0,c*c+s*s==1,T*(1+c)==s,g*(1+T)==1-T,mu>1]
    rows.append(query("original TL corner containing qU bounds its left leg",normal+[
        U<y,s*mu+c*(D-U)<=1,D>=g+y]))
    rows.append(query("original TL corner bridging C up-ray forces u>1-T",normal+[
        c*mu+s*(mu-u)<=1,u<=1-T]))
    rows.append(query("nonpositive F and left gap contradict actual C long chord",[
        mu>1,T>0,T<1,g*(1+T)==1-T,D<g+y,u>1-T,
        ell>=mu-D,mu+ell+r+u<2,y<k,k<r]))
    rows.append(query("left meeting: coarse free-corner angle T<3/7",[
        T>0,T<1,g*(1+T)==1-T,D>z3.RealVal("4/7"),
        y<z3.RealVal("9/56"),D<g+y,7*T>=3]))
    dt=z3.Real("s22_dt")
    rows.append(query("first feedback puts y<81/5264",[
        T>0,7*T<3,2*(1-T)*dt==T*T,
        k>0,k<dt,2*(1-k)*dk==k*k,
        y<dk,5264*y>=81]))
    rows.append(query("left meeting: refined T<2/7",[
        T>0,T<1,g*(1+T)==1-T,D>z3.RealVal("4/7"),
        y<z3.RealVal("81/5264"),D<g+y,7*T>=2]))
    rows.append(query("refined feedback y<T/165",[
        T>0,7*T<2,2*(1-T)*dt==T*T,
        k>0,k<dt,2*(1-k)*dk==k*k,
        y<dk,165*y>=T]))
    L1,w,q,S1,S2,d,b,v,B,U2=z3.Reals(
        "s22_L1 s22_w s22_q s22_S1 s22_S2 s22_d s22_b s22_v s22_B s22_U2")
    rows.append(query("left meeting raises actual L1",[
        mu>1,T>0,7*T<2,g*(1+T)==1-T,
        D<g+y,165*y<T,L1+D>=2*mu,
        L1<=1+z3.RealVal("767/495")*T]))
    rows.append(query("left long leg cosine cap forces w>7T/5",[
        T>0,7*T<2,w>0,w<1,L1>1+z3.RealVal("767/495")*T,
        7*(L1+1)<17,L1*(1-w*w)<=1+w*w,5*w<=7*T]))
    rows.append(query("q>2T from the new w bound",[
        T>0,7*T<2,w>0,5*w>7*T,q*(1+w)>2*w,q<=2*T]))
    rows.append(query("C right connection and nonempty V2 parallel traces give S2<r",[
        mu>1,B<1,S2+U2<=B,r+U2>=mu,S2>=r],"QF_LRA"))
    rows.append(query("left meet nonpositive F violates bottom chord parabola",[
        T>0,7*T<2,d>=0,(2-T)*d<T,
        2*(1-T)*dt==T*T,r<dt,S2<r,q>2*T,
        b>1+q-S2,v>1-d,b+v*v<=2]))
    rows.append(query("F positive horizontal plus bottom midpoint cannot touch left edge",[
        mu>1,r>0,y>=-mu,mu*mu+r*(y+mu)<=1]))
    rows.append(query("positive F, bottom meet, qU in C forces S1>1+r-y",[
        mu>1,D<mu,ell>=2*mu-S1-D,u>mu-y,
        mu+ell+r+u<2,S1<=1+r-y],"QF_LRA"))
    YM=z3.Real("s22_Ymax")
    rows.append(query("positive F, bottom meet, qU in W forces S1>1+r-y",[
        mu>1,ell>=2*mu-S1-D,u>=mu-YM,D+YM<1+y,
        mu+ell+r+u<2,S1<=1+r-y],"QF_LRA"))
    a=z3.Real("s22_a")
    rows.append(query("bottom meet/right meet angle cascade contradicts forced S1",[
        w>0,w<1,y>0,y<a,a<w,
        S1*(1+w)<1-w,S1>1-y]))
    eta=z3.Real("s22_eta")
    rows.append(query("positive F: right cascade gives eta(a)>y/3",[
        a>0,a<1,y>0,y<a,y<1-a,
        eta*(1+a)==a*(1-a),3*eta<=y]))
    rows.append(query("left meeting: T<73/137 without the QR-in-C assumption",[
        T>0,T<1,g*(1+T)==1-T,D>z3.RealVal("4/7"),
        15*y<4,D<g+y,137*T>=73]))
    p,ss,h=z3.Reals("s22_Cp s22_Cs s22_Ch")
    c_normal=[p>0,ss>0,p>=ss,p*p+ss*ss==1,mu>1]
    rows.append(query("positive rotation of C excluded for T<73/137",c_normal+[
        T>0,137*T<73,u>1-T,p*mu+ss*u<=1]))
    rows.append(query("C negative orientation gives half-angle bound for full new T domain",c_normal+[
        T>0,137*T<73,u>1-T,ss*mu+p*u<=1,h*(1+p)==ss,(2-T)*h>=T]))
    rows.append(query("C actual right ray is <Delta(T) for full new T domain",[
        T>0,137*T<73,mu>1,h>=0,(2-T)*h<T,
        2*(1-T)*dt==T*T,
        (1-h*h)*(mu+r)<=1+h*h,r>=dt]))
    rows.append(query("C actual downward ray is <h",c_normal+[
        h*(1+p)==ss,p*mu+ss*d<=1,d>=h]))
    rows.append(query("positive F left meet, T<=y: r<eta(a)",[
        a>0,a<1,y>0,15*y<4,y<a,y<1-a,eta*(1+a)==a*(1-a),
        T>0,T<=y,2*(1-T)*dt==T*T,r<dt,r>=eta]))
    rows.append(query("positive F left meet, T>y: left cosine cap yields w>T/2",[
        T>0,137*T<73,g*(1+T)==1-T,mu>1,
        y<T,D<g+y,L1+D>=2*mu,
        w>0,w<1,L1*(1-w*w)<=1+w*w,2*w<=T]))
    rows.append(query("positive F left meet, T>y: q>Delta(T)",[
        T>0,137*T<73,w>0,2*w>T,q*(1+w)>2*w,
        2*(1-T)*dt==T*T,q<=dt]))
    f=z3.Real("s22_f")
    rows.append(query("positive F left meet: r<eta forces b+f>1",[
        q>0,eta>0,r<eta,b>1+q-S2,
        f>1-a-r,S2<1-a-eta,b+f<1],"QF_LRA"))
    rows.append(query("positive F left meet: q>r forces b+f>1",[
        eta>0,q>r,b>1+q-S2,
        f>1-a-r,S2<1-a-eta,b+f<1],"QF_LRA"))

    X=sp.symbols("t")
    assert sp.cancel((1-X)/(1+X)+X-1+X*(1-X)/(1+X))==0
    assert sp.Rational(14,9)-sp.Rational(1,165)==sp.Rational(767,495)
    assert sp.Rational(767,495)*sp.Rational(7,17)==sp.Rational(5369,8415)
    C,S=sp.symbols("c s")
    assert sp.cancel((1-(S/(1+C)))/(1+S/(1+C))-(1-S)/C
        -(C*C+S*S-1)/(C*(1+C+S)))==0
    assert sp.cancel(2*X/(2+X)-X*X/(2*(1-X))
        -X*(4-6*X-X*X)/(2*(2+X)*(1-X)))==0
    assert sp.cancel(X*(1-X)/(2+3*X-X*X)-X*X/4
        -X*(4-6*X-3*X*X+X**3)/(4*(2+3*X-X*X)))==0
    constants={
        "33/79<3/7":sp.Rational(33,79)<sp.Rational(3,7),
        "Delta(9/56)=81/5264":sp.Rational(9,56)**2/(2*(1-sp.Rational(9,56)))==sp.Rational(81,5264),
        "3/7+81/5264<4/9":sp.Rational(3,7)+sp.Rational(81,5264)<sp.Rational(4,9),
        "Delta(2/7)=2/35":sp.Rational(2,7)**2/(2*(1-sp.Rational(2,7)))==sp.Rational(2,35),
        "Delta(k)/k<1/33 for k<2/35":sp.Rational(2,35)/(2*(1-sp.Rational(2,35)))==sp.Rational(1,33),
        "5369/8415>14/25":sp.Rational(5369,8415)>sp.Rational(14,25),
        "1/5+7/6=41/30<2":sp.Rational(1,5)+sp.Rational(7,6)==sp.Rational(41,30)
            and sp.Rational(41,30)<2,
        "64/137>sqrt(2)-1":201**2>2*137**2,
        "positive left cosine polynomial at 73/137":
            (4-6*X-3*X*X+X**3).subs(X,sp.Rational(73,137))>0,
        "positive chord polynomial at 73/137":
            (4-6*X-X*X).subs(X,sp.Rational(73,137))>0,
    }
    assert all(constants.values())
    result={"status":"all exact checks passed" if all(row["result"]=="unsat" for row in rows) else "inspect",
        "queries":rows,"query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "symbolic_checks":6,"constant_checks":{key:bool(value) for key,value in constants.items()},
        "scope":"G4 same-side top TR/right BR excludes all nonpositive F horizontal; positive F requires both left and bottom corner gaps",
        "proof_method":"actual left gap/top-axis endpoints; reciprocal half-angle feedback; F bottom chord parabola",
        "round13_pair_certificate_needed":False,
        "not_proved":"G4 same-side F positive horizontal with left and bottom gaps; remaining G2/G3; S(6)=2",
        "no_search":"no placements, fixed target points, angle samples or interval trees"}
    Path(__file__).with_name("round22_same_side_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({key:value for key,value in result.items() if key!="queries"},ensure_ascii=False,indent=2))
    for row in rows:
        if row["result"]!="unsat":
            print(json.dumps(row,ensure_ascii=False,indent=2))
    assert result["status"]=="all exact checks passed"


if __name__=="__main__":
    main()
