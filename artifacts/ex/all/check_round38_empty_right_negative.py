"""Small independent exact checks for the hand proof, not cover enumeration."""
from pathlib import Path
import json,time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        sol=z3.SolverFor(theory);sol.set(timeout=30000);sol.add(*cs)
        start=time.perf_counter();ans=sol.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        if ans!=z3.unsat:
            row["detail"]=str(sol.model()) if ans==z3.sat else sol.reason_unknown()
        print(json.dumps(row),flush=True)
        assert ans==z3.unsat,row
        rows.append(row)
    mu,c,s,alpha,beta,u,d,r,l,e,eta,K=z3.Reals(
        "mu c s alpha beta u d r l e eta K")
    norm=[c>=s,s>0,c*c+s*s==1]
    query("RIGHT negative first down and first up impossible",norm+[
        s*d==alpha+1,s*u==-alpha,u+d<1])
    query("RIGHT negative first down and second up impossible",norm+[
        mu>1,e>0,s*d==alpha+1,c*u==beta+1,
        c*mu-s*e<=alpha+1,s*mu+c*e<=beta+1,u+d<1])
    query("RIGHT negative both second vertical faces impossible",norm+[
        c*d==-beta,c*u==beta+1,u+d<1])
    query("RIGHT negative first right face wins",norm+[
        mu>1,e>0,alpha==-s*u,beta==-c*d,u+d<1,
        c*mu-s*e<=alpha+1,s*mu+c*e<=beta+1,
        alpha+1<c*mu,
        (alpha+1)/c>=(beta+1)/s])
    query("global right root less than one gives u>eta",norm+[
        eta*(1+c)==s,K*c==s,r==(1-s*u)/c,r<1,u<=eta])
    L2,z,a,S1,S2,Sigma,b,w=z3.Reals("L2 z a S1 S2 Sigma b w")
    query("actual lower RIGHT gap end gives long L2",norm+[
        mu>1,eta*(1+c)==s,c*mu-s*(L2-mu)<=1-s*u,
        L2<=1+u-eta])
    query("actual upper RIGHT gap end gives e+d<G",norm+[
        mu>1,eta*(1+c)==s,s*mu+c*(e+d)<=1,
        e+d>=(1-eta)/(1+eta)])
    query("two actual left-root caps force l<1/2",[
        K>0,K<=1,u>0,d>0,l>0,l<=K*u,K*l<=d,u+d<1,2*l>=1])
    query("LEFT meeting denominator exceeds 7/4",[
        l>0,2*l<1,4-4*l-l*l<=z3.Q(7,4)])
    query("u upper and z upper separate C from QU",[
        u<z3.Q(6,7),z<z3.Q(1,7),u+z>=1],"QF_LRA")
    query("sqrt2 bounds imply u<6/7",[
        a>0,a*a==2,eta<=a-1,u<eta+a-1,7*u>=6])
    query("z<4 l squared/7 is also z<d",[
        u>0,u<1,d>0,K>0,l>0,l<=K*u,K*l<=d,
        z<4*l*l/7,z>=d])
    query("original W vertical bridge forces u>4 eta/(1+3 eta)",[
        u>0,u<1,d>0,eta>0,z<d,
        2*eta/(1+eta)+d<z+u/(2-u),
        u<=4*eta/(1+3*eta)])
    query("diameter constant gap at w=2/7",[
        a>0,a*a==2,z3.Q(8,21)-13*a/49<=0])
    query("large eta incompatible with w<2/7",[
        eta>=z3.Q(1,4),12*eta<=5,u-eta<z3.Q(2,7),
        u>4*eta/(1+3*eta)])
    query("small eta gives K<8/15 and u<15/28",[
        eta>0,4*eta<1,K*(1-eta*eta)==2*eta,
        u-eta<z3.Q(2,7),
        z3.Or(15*K>=8,28*u>=15)])
    query("small-u W bridge gives linear budget",[
        eta>0,4*eta<1,u>0,28*u<15,d>0,z<4*u*d/7,
        2*eta/(1+eta)+d<z+u/(2-u),
        8*eta/5+34*d/49>=28*u/41])
    query("q(l) short-leg loss cap",[
        l>0,2*l<1,K>0,15*K<8,u>0,l<=K*u,
        l/(2-l)>=16*u/45])
    query("combine two linear coefficients to 7w/3",[
        u>0,eta>0,d>0,S1<16*u/45,
        8*eta/5+34*d/49<28*u/41,
        2*d+S1>=7*(u-eta)/3],"QF_LRA")
    v=z3.Real("v")
    query("strong Phi loss exceeds 7w/3 on w<2/7",[
        v>0,w==v*v,w<z3.Q(2,7),5*v/4<=7*w/3])
    query("final explicit bottom square contradiction",[
        d>0,w>0,v>0,v*v==w,w<z3.Q(2,7),
        5*v/4<2*d-d*d+S1,2*d+S1<7*w/3])
    query("LEFT double W bridge forces u>7/10",[
        u>0,u<1,K>0,K*u>2*(1-u)/(2-u),K<1-u/2,10*u<=7])
    query("LEFT double W bridge forces eta<3/10",[
        eta>0,eta<1,K*(1-eta*eta)==2*eta,20*K<13,10*eta>=3])
    query("LEFT double bridge long-leg domain forces eta>17/60",[
        u>z3.Q(7,10),u-eta<z3.Q(5,12),eta<=z3.Q(17,60)],"QF_LRA")
    query("LEFT double bridge gives small Phi(2/5)",[
        a>0,a*a==6,z3.Q(7,5)-14*a/25>=z3.Q(1,30)])
    query("LEFT double bridge two bottom legs force S2>1/2",[
        Sigma>z3.Q(7,12),Sigma==S1+S2,S1<z3.Q(1,30),2*S2<=1],"QF_LRA")
    query("LEFT S2>1/2 forces x<1/3",[
        a>0,a<1,S2<(1-a)/(1+a),2*S2>1,3*a>=1])
    query("LEFT double bridge actual d lower and G upper",[
        eta>z3.Q(17,60),eta<z3.Q(3,10),K*(1-eta*eta)==2*eta,
        u<z3.Q(43,60),u>0,u<1,r>1-u/(2-u),d>=K*r,
        z3.Or(d<=z3.Q(289,1155),(1-eta)/(1+eta)>=z3.Q(43,77))])
    query("LEFT double bridge z and q(u) upper",[
        d>z3.Q(289,1155),e<z3.Q(43,77)-d,e>0,
        z<e/(2-e),u>0,u<z3.Q(43,60),
        z+u/(2-u)>=z3.Q(3,4)])

    query("LEFT C direct QU gives stronger bridge budget",[
        u>0,u<1,eta>0,eta<1,d>0,
        e==(1-eta)/(1+eta)-d,e>0,e<1,
        z<e/(2-e),u+z>1,
        2*eta/(1+eta)+d>=u/(2-u)])
    E,V,L=sp.symbols("eta v l",real=True)
    ids=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.cancel(expr));ids.append(name)
    ident("small left root diameter deficit",
          (1-(1-L))/(1+(1-L))-L/(2-L))
    ident("lower bound u creates w lower bound",
          4*E/(1+3*E)-E-3*E*(1-E)/(1+3*E))
    ident("eta quadratic test",
          7*(1+3*E)*(3*E*(1-E)/(1+3*E)-sp.Rational(2,7))
          -(15*E-21*E**2-2))
    ident("strong Phi squared difference",
          (1+V**2)**2*(2+V**2)-(sp.Rational(5,4)+V)**2
          -(4*(V-sp.Rational(5,16))**2+sp.Rational(3,64)+4*V**4+V**6))
    # Phi'(w) = 1 - (1+4w+2w^2)/sqrt(w(2+w)); numerator exceeds root.
    ident("Phi monotone squared difference",
          (1+4*V+2*V**2)**2-V*(2+V)
          -(1+6*V+19*V**2+16*V**3+4*V**4))
    ident("Phi at 2/7 gap",
          2-sp.sqrt(2)-(sp.Rational(1,3)+sp.Rational(9,7)*(1-4*sp.sqrt(2)/7))
          -(sp.Rational(8,21)-13*sp.sqrt(2)/49))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,sp.factor(value))
        constants.append({"name":name,"value":str(expected)})
    exact("eta test at 1/4",(15*E-21*E**2-2).subs(E,sp.Rational(1,4)),sp.Rational(7,16))
    exact("eta test at 5/12",(15*E-21*E**2-2).subs(E,sp.Rational(5,12)),sp.Rational(29,48))
    exact("diameter radical square gap",56**2-2*39**2,94)
    exact("u coefficient slack",sp.Rational(7,3)-sp.Rational(1372,697)-sp.Rational(16,45),
          sp.Rational(293,31365))
    exact("eta coefficient slack",sp.Rational(392,85)-sp.Rational(7,3),sp.Rational(581,255))
    exact("last squared strict margin",sp.Rational(25,16)-sp.Rational(49,9)*sp.Rational(2,7),
          sp.Rational(1,144))
    exact("double bridge cubic at 7/10",
          sp.Rational(7,10)**3-4*sp.Rational(7,10)**2+8*sp.Rational(7,10)-4,
          -sp.Rational(17,1000))
    exact("double bridge K gap",sp.Rational(60,91)-sp.Rational(13,20),sp.Rational(17,1820))
    exact("Phi(2/5) comparison square gap",6*84**2-205**2,311)
    exact("bottom diameter lower comparison square gap",sp.Rational(17,12)**2-2,sp.Rational(1,144))
    exact("W right-leg upper comparison",
          sp.Rational(3,4)-sp.Rational(178,977)-sp.Rational(43,77),
          sp.Rational(2819,300916))
    result={"queries":rows,"symbolic_identities":ids,"constants":constants,
            "totals":{"UNSAT":len(rows),"NRA":sum(x["theory"]=="QF_NRA" for x in rows),
                      "LRA":sum(x["theory"]=="QF_LRA" for x in rows),
                      "symbolic_identities":len(ids),"constants":len(constants)},
            "scope":"RIGHT real-gap family excluded; LEFT double W bridge and double direct C contact excluded",
            "also_proved":"LEFT positive-C C meets exactly one of Q2 and QU; original W cannot contain TOPmid",
            "not_proved":"F empty LEFT positive-C exactly-one direct-contact subcases; three meetings; S(6)=2",
            "exploratory_UNKNOWN_counted":False}
    Path(__file__).with_name("round38_empty_right_negative_checks.json").write_text(
        json.dumps(result,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
