"""Small exact checks for the empty-F LEFT/negative-C hand proof."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        sol=z3.SolverFor(theory);sol.set(timeout=60000);sol.add(*cs)
        start=time.perf_counter();ans=sol.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        if ans!=z3.unsat:
            row["detail"]=str(sol.model()) if ans==z3.sat else sol.reason_unknown()
        print(json.dumps(row),flush=True);assert ans==z3.unsat,row;rows.append(row)
    mu,r,nu,p,eps=z3.Reals("mu r nu p eps")
    query("new square from overlong right root has half-side>1",[
        mu>1,r>2-mu,nu==(mu+r)/2,nu<=1],"QF_LRA")
    query("new square centre is in original exclusive box",[
        mu>1,0<r,r<mu,r>2-mu,p==(r-mu)/2,eps==mu-1,
        z3.Or(p<=-eps,p>=eps)],"QF_LRA")
    query("new contained square bounds",[
        mu>1,r>0,r<mu,nu==(mu+r)/2,p==(r-mu)/2,
        z3.Or(p-nu< -mu,p+nu>mu,nu>mu)],"QF_LRA")
    d,u,l,b,v,Sigma=z3.Reals("d u l b v Sigma")
    query("same F bottom chord plus actual V arm bound",[
        mu>1,d>0,d<1,v>=mu-d,b>=2*mu-Sigma,b+v*v<=2,
        Sigma<=(1-d)*(1-d)])
    c,s,alpha,beta=z3.Reals("c s alpha beta")
    norm=[c>=s,s>0,c*c+s*s==1]
    e=z3.Real("e")
    query("LEFT P forces first up-root beyond outer mid",norm+[
        mu>1,e>0,-c*mu-s*e>=alpha,-alpha/s<=mu])
    query("LEFT P and l<mu force first right-root active",norm+[
        mu>1,e>0,l<mu,beta==-s*l,-c*mu-s*e>=alpha,
        (alpha+1)/c>=(beta+1)/s])
    query("second down-root activity excluded by real side/V pair",norm+[
        u==(1-s*l)/c,d==s*l/c,u+d<1])
    eta,K=z3.Reals("eta K")
    query("real LEFT P gives e+d<eta",norm+[
        mu>1,eta*(1+c)==s,K*c==s,r==K*d,alpha==c*r-1,
        -c*mu-s*e>=alpha,e+d>=eta])
    query("global l<1 gives u>G",norm+[
        eta*(1+c)==s,K*c==s,l<1,u==(1-s*l)/c,
        u<=(1-eta)/(1+eta)])
    query("u+q(eta-d)>=1 forces d<1/6",[
        eta>0,12*eta<5,d>0,d<eta,u+d<1,
        u+(eta-d)/(2-eta+d)>=1,6*d>=1])
    query("same upper-cap failure forces l<7/10",[
        eta>0,12*eta<5,K*(1-eta*eta)==2*eta,
        u==(1+eta*eta)/(1-eta*eta)-K*l,
        d>0,d<eta,u+(eta-d)/(2-eta+d)>=1,10*l>=7])
    z,x,D,L4,U2,S1,S2=z3.Reals("z x D L4 U2 S1 S2")
    query("TOP meet and original W H bridge bound x",[
        mu>1,D+L4>=2*mu,D<x+r/(2-r),L4<=1+2*z*z/(1-z*z),
        r>0,r<1,z>0,z<1,
        x<=1-2*z*z/(1-z*z)-r/(2-r)])
    query("small z/r imply bounded total V2 deficit",[
        z>0,19*z<5,r>0,6*r<1,
        2*z*z/(1-z*z)+r/(2-r)>=z3.Q(443,1848)])
    vv=z3.Real("vv")
    query("V2 small deficit caps S2",[
        vv>0,1848*vv<443,x>1-vv,x<1,x>0,
        S2<(1-x)/(1+x),S2>=z3.Q(443,3253)])
    query("explicit small root/leg budget contradiction",[
        d>0,6*d<1,S1<z3.Q(7,13),S2<z3.Q(443,3253),
        S1+S2>(1-d)*(1-d)])
    query("W cannot bridge both C roots",[
        mu>1,K>0,K<=1,d>0,u>0,r==K*d,u+d<1,r+u>mu])
    query("high u: Delta(1-u)<u-q(u)",[
        u>=z3.Q(4,7),u<1,
        (1-u)*(1-u)/(2*u)>=u-u/(2-u)])
    query("low u: v-q(v) is increasing to 4/7",[
        u>=0,7*u<=4,1-2/(2-u)**2<z3.Q(1,50)])
    query("angle comparison polynomial is positive",[
        eta>0,12*eta<=5,1-2*eta-2*eta**2+5*eta**3-6*eta**4<=0])
    query("angle comparison polynomial derivative negative",[
        eta>0,-2-4*eta+15*eta*eta-24*eta**3>=0])
    query("low u angle comparison",[
        eta>0,12*eta<=5,
        K*(1-eta*eta)==2*eta,
        (1-eta)/(1+eta)-(1-eta)/(1+3*eta)<=
        (K*eta)*(K*eta)/(2*(1-K*eta))])
    query("direct right contact gives small L2 excess",[
        r>0,r<1,x>1-r,x<1,
        (1-x)*(1-x)/(2*x)>=r*r/(2*(1-r))])
    query("final true W bridge contradiction",[
        z<(eta-d)/(2-eta+d),u+(eta-d)/(2-eta+d)<1,
        u>0,u<1,r>0,r<1,eta>d,
        u/(2-u)+r*r/(2*(1-r))<u,
        z+u/(2-u)+r*r/(2*(1-r))>1])
    query("RIGHT positive C first up-root is beyond outer mid",norm+[
        mu>1,e>0,c*mu+s*e<=alpha+1,(alpha+1)/s<=mu])
    query("RIGHT positive C first left-root is active",norm+[
        mu>1,e>0,r<mu,beta==-s*r,c*mu+s*e<=alpha+1,
        -alpha/c>=(beta+1)/s])
    query("RIGHT positive C real P gives e+d<eta",norm+[
        mu>1,eta*(1+c)==s,K*c==s,l==K*d,alpha==-c*l,
        c*mu+s*e<=alpha+1,e+d>=eta])
    query("RIGHT short left root bounds TOP angle",[
        d>0,2*d<1,l>0,l<=d,z<4*l*l/7,7*z>=2*d])
    query("RIGHT vertical W bridge forces small positive long root",[
        eta>0,12*eta<5,K*(1-eta*eta)==2*eta,u>0,u<1,
        u==(1+eta*eta)/(1-eta*eta)-K*r,
        u/(2-u)>1-eta,16*r>=11])
    query("RIGHT vertical W bridge forces d<1/5",[
        eta>0,12*eta<5,d>0,u>0,u+d<1,
        u/(2-u)>1-eta+5*d/7,5*d>=1])
    query("RIGHT d cap makes z<1/20",[
        d>0,5*d<1,l>0,l<=d,z<4*l*l/7,20*z>=1])
    query("RIGHT small z/r total upper below 211/399",[
        z>0,20*z<1,r>0,16*r<11,
        2*z*z/(1-z*z)+r/(2-r)>=z3.Q(211,399)])
    query("RIGHT explicit two-short-leg contradiction",[
        d>0,5*d<1,S1<z3.Q(1,9),S2<z3.Q(11,21),
        S1+S2>(1-d)*(1-d)])
    query("LEFT positive C first down and first up faces impossible",norm+[
        alpha==-c*l,s*d==c*l,s*u==alpha+1,u+d<1])
    query("LEFT positive C first down and second up faces impossible",norm+[
        mu>1,e>0,alpha==-c*l,s*d==c*l,c*u==beta+1,
        -c*mu+s*e>=alpha,s*mu+c*e<=beta+1,u+d<1])
    query("LEFT positive C same second vertical faces impossible",norm+[
        c*u==beta+1,c*d==-beta,u+d<1])
    query("both W bridges force u>2/3",[
        u>0,u<1,K>0,K*u>2*(1-u)/(2-u),K<1-u/2,3*u<=2])
    query("both W bridges force eta<1/3",[
        eta>0,eta<1,K*(1-eta*eta)==2*eta,K<z3.Q(2,3),3*eta>=1])

    E,V=sp.symbols("eta v")
    q=lambda a:a/(2-a)
    g=lambda a:(1-a)/(1+a)
    kk=2*E/(1-E**2)
    delta=2*E**2/(1-E**2)
    Delta=lambda a:a*a/(2*(1-a))
    poly=1-2*E-2*E**2+5*E**3-6*E**4
    ids=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.cancel(expr));ids.append(name)
    fcap=E+(1-E**2)/(2*(2-E))
    ident("left root cap derivative",sp.diff(fcap,E)-6*(E-1)*(E-3)/(4-2*E)**2)
    ident("angle delta identity",kk*E-delta)
    ident("small angle Delta comparison",
        g(E)-q(g(E))-Delta(delta)-
        2*E*poly/((1-E**2)*(1-3*E**2)*(1+3*E)))
    ident("polynomial derivative square",
        sp.diff(poly,E)-(-2-E*(24*(E-sp.Rational(5,16))**2+sp.Rational(53,32))))
    ident("high u deficit comparison",
        V-q(V)-Delta(1-V)-(1-V)*(V*V+3*V-2)/(2*V*(2-V)))
    ident("low u deficit derivative",sp.diff(V-q(V),V)-(1-2/(2-V)**2))
    ident("S2 rational q cap",q(sp.Rational(25,168)+sp.Rational(1,11))-sp.Rational(443,3253))
    ident("root rescaling right boundary",(sp.Symbol("r")-sp.Symbol("mu"))/2+
        (sp.Symbol("mu")+sp.Symbol("r"))/2-sp.Symbol("r"))
    ident("both bridge feasibility polynomial",
        V*(2-V)**2-4*(1-V)-(V**3-4*V**2+8*V-4))
    ident("both bridge feasibility derivative",sp.diff(V**3-4*V**2+8*V-4,V)-
        (3*(V-sp.Rational(4,3))**2+sp.Rational(8,3)))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,sp.factor(value))
        constants.append({"name":name,"value":str(expected)})
    exact("eta q cap",q(sp.Rational(5,12)),sp.Rational(5,19))
    exact("left root cap endpoint",fcap.subs(E,sp.Rational(5,12)),sp.Rational(103,152))
    exact("left root cap gap",sp.Rational(7,10)-sp.Rational(103,152),sp.Rational(17,760))
    exact("small z long-leg excess",2*sp.Rational(5,19)**2/(1-sp.Rational(5,19)**2),sp.Rational(25,168))
    exact("small r q bound",q(sp.Rational(1,6)),sp.Rational(1,11))
    exact("small bottom budget gap",sp.Rational(25,36)-sp.Rational(7,13)-sp.Rational(443,3253),
        sp.Rational(30145,1522404))
    exact("angle polynomial endpoint",poly.subs(E,sp.Rational(5,12)),sp.Rational(1,3456))
    exact("high u quadratic endpoint",sp.Rational(4,7)**2+3*sp.Rational(4,7)-2,sp.Rational(2,49))
    exact("low u derivative endpoint",1-2/(2-sp.Rational(4,7))**2,sp.Rational(1,50))
    exact("RIGHT long root cap gap",sp.Rational(11,16)-sp.Rational(103,152),sp.Rational(3,304))
    exact("RIGHT d cap below 1/5",sp.Rational(1,5)-sp.Rational(35,186),sp.Rational(11,930))
    exact("RIGHT small deficit bound",q(sp.Rational(2,399)+sp.Rational(11,21)),sp.Rational(211,587))
    exact("RIGHT total short-leg gap",sp.Rational(16,25)-sp.Rational(1,9)-sp.Rational(11,21),sp.Rational(8,1575))
    exact("both bridge cubic at 2/3",sp.Rational(2,3)**3-4*sp.Rational(2,3)**2+
        8*sp.Rational(2,3)-4,sp.Rational(-4,27))
    exact("both bridge square gap",sp.Rational(1,3)-sp.Rational(5,9)**2,sp.Rational(2,81))
    result={"queries":rows,"symbolic_identities":ids,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(t["theory"]=="QF_NRA" for t in rows),
                  "LRA":sum(t["theory"]=="QF_LRA" for t in rows),
                  "symbolic_identities":len(ids),"constants":len(constants)},
        "scope":"Empty-F LEFT negative-C and RIGHT positive-C orientations both excluded",
        "also_proved":"All C roots in [mu-1,2-mu]; LEFT positive double bridge requires u>2/3, eta<1/3",
        "not_proved":"Empty-F LEFT positive C; RIGHT negative C; three meetings; S(6)=2"}
    Path(__file__).with_name("round37_empty_left_negative_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
