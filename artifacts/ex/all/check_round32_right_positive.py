"""Exact local checks for the RIGHT-gap / positive F-horizontal exclusion."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        solver=z3.SolverFor(theory)
        solver.set(timeout=60000)
        solver.add(*cs)
        start=time.perf_counter()
        ans=solver.check()
        row={"name":name,"theory":theory,"result":str(ans),
             "seconds":time.perf_counter()-start}
        if ans!=z3.unsat:
            row["detail"]=str(solver.model()) if ans==z3.sat else solver.reason_unknown()
        print(json.dumps(row),flush=True)
        assert ans==z3.unsat,row
        rows.append(row)

    mu,c,s,alpha,beta,l,r,u,d,e=z3.Reals("mu c s alpha beta l r u d e")
    norm=[c>=s,s>0,c*c+s*s==1]
    inside=[mu>1,l>0,r>0,u>0,d>0,l<mu,r<mu,u<mu,d<mu,
            alpha<0,alpha>-1,beta<0,beta>-1,l+r-d>mu,e>0]
    # First active cases use only actual endpoint halfplanes, no angle surrogate.
    query("positive C: first lower-face down-root impossible",norm+inside+[
        s*d==-alpha,c*l<=-alpha])
    query("positive C: second down-root and upper right point impossible",norm+inside+[
        c*d==-beta,s*r==-beta,c*l<=-alpha,
        c*mu+s*e<=alpha+1])
    query("negative C: first upper-face down-root impossible",norm+inside+[
        s*d==alpha+1,c*r<=alpha+1])
    query("negative C: second down-root cap",norm+inside+[
        c*d==-beta,c*(l+r)<=1,d>=1/c-mu])
    query("negative C: upper root must use first lower face",norm+inside+[
        c*d==-beta,d<1/c-mu,
        z3.Or(-s*u==alpha,c*u==beta+1),
        -s*u>=alpha,c*u<=beta+1,-s*u!=alpha])
    # The following endpoint query directly verifies the active-root formula.
    query("negative C: second upper face cannot set u below mu",norm+inside+[
        c*d==-beta,d<1/c-mu,c*u==beta+1])
    query("negative C: true left endpoint min formula",norm+inside+[
        alpha==-s*u,beta==-c*d,
        c*l<=s*u,s*l<=c*d,
        z3.Or(c*l==s*u,s*l==c*d),
        l!=z3.If(s*u/c<=c*d/s,s*u/c,c*d/s)])
    query("negative C: left root below one half",norm+[
        u>0,2*u<1,l>0,c*l<=s*u,2*l>=1])
    L2,eta,w,G=z3.Reals("L2 eta w G")
    query("actual lower RIGHT gap endpoint yields long-leg defect",norm+[
        mu>1,eta*(1+c)==s,w==u-eta,
        c*mu-s*(L2-mu)<=1-s*u,L2<=1+w])
    query("actual upper RIGHT endpoint yields e+d<G",norm+[
        mu>1,G*c==1-s,s*mu+c*(e+d)<=1,e+d>=G])
    a,z=z3.Reals("a z")
    query("direct left-axis contact forces a>1-l",[
        mu>1,l>=mu-z,z<a,a<=1-l],"QF_LRA")
    query("short-leg bound via direct left contact",[
        l>0,2*l<1,a>1-l,a<1,
        (1-a)/(1+a)>=l/(2-l)])
    query("Ys denominator on the large-angle left corner is positive",[
        2*a>1,a<1,6*a-1-a*a<=0])
    query("Ys is strictly decreasing for 1/2<a<1",[
        2*a>1,a<1,4*(a*a-1)>=0])
    query("Ys(1-l)<4*l²/7",[
        l>0,2*l<1,7*l*l>=4*l*l*(4-4*l-l*l)])
    K=z3.Real("K")
    query("left corner budget implies z<2u/7",[
        u>0,2*u<1,K>0,K<=1,l>0,l<=K*u,
        z<4*l*l/7,7*z>=2*u])
    v=z3.Real("v")
    query("Phi loss is greater than sqrt(w)",[
        v>0,w==v*v,
        (1+w)*(1+w)*(2+w)<=(1+v)*(1+v)])
    phi,S1,S2=z3.Reals("phi S1 S2")
    query("same actual bottom legs force sqrt(w)<q(l)",[
        v>0,phi<1-v,S1<l/(2-l),S2<=phi,S1+S2>1,
        l>0,2*l<1,v>=l/(2-l)])
    query("q(l)<2l/3 below one half",[
        l>0,2*l<1,l/(2-l)>=2*l/3])
    query("positive w forces w<2u/9",[
        w>0,w<4*l*l/9,l>0,l<=K*u,K>0,K<=1,
        u>0,2*u<1,9*w>=2*u])
    query("either defect sign gives u<9eta/7: positive",[
        eta>0,u==eta+w,9*w<2*u,7*u>=9*eta],"QF_LRA")
    query("either defect sign gives u<9eta/7: nonpositive",[
        eta>0,u==eta+w,w<=0,7*u>=9*eta],"QF_LRA")
    query("C halfangle eta below 5/12",norm+[
        eta*(1+c)==s,12*eta>=5])
    query("combined corner and centre deficits below 1-G",[
        eta>0,12*eta<5,G*(1+eta)==1-eta,
        u>0,7*u<9*eta,z<2*u/7,2*u<1,
        z+u/(2-u)>=1-G])
    cw,sw,T,A,U4=z3.Reals("cw sw T A U4")
    wnorm=[cw>0,sw>0,cw*cw+sw*sw==1]
    query("original W inward projection forces T>1-u",wnorm+[
        mu>1,cw*mu+sw*(mu-u)<=1,T*sw==1-cw,T<=1-u])
    bw=z3.Real("bw")
    query("original W QU and RIGHT support give A<g(T)+U4",wnorm+[
        mu>1,T*sw==1-cw,sw*mu-cw*U4<=bw,
        cw*A<=1-bw,A>=(1-T)/(1+T)+U4])
    query("halfangle monotonicity gives g(T)<q(u)",[
        u>0,u<1,T>1-u,T<1,(1-T)/(1+T)>=u/(2-u)])
    query("real bridge and upper endpoint contradict",[
        mu>1,e==mu-A,A<z+u/(2-u),z+u/(2-u)<1-G,
        d>0,e+d<G,u>0,u<1])

    X,W,V,E=sp.symbols("x w v eta")
    identities=[]
    def ident(name,expr):
        assert sp.factor(expr)==0,(name,sp.factor(expr))
        identities.append(name)
    ys=lambda x:(1-x)**2/(6*x-1-x*x)
    ident("Ys derivative",
          sp.diff(ys(X),X)-4*(X*X-1)/(6*X-1-X*X)**2)
    ident("left root substitution in Ys",
          ys(1-X)-X*X/(4-4*X-X*X))
    ident("Phi positive square difference",
          ((1+W)**2*(2+W)-(1+V)**2).subs(W,V*V)-
          ((1-V)**2+3*V*V+4*V**4+V**6))
    C,S=sp.symbols("c s")
    ident("same-circle long-leg offset",
          ((C+S-1)/S-(1-S/(1+C)))-
          (C*C+S*S-1)/(S*(1+C)))
    ident("C halfangle G",
          ((1-S)/C-(1-S/(1+C))/(1+S/(1+C)))-
          (1-C*C-S*S)/(C*(1+C+S)))
    ident("W halfangle g(T)",
          ((1-S)/C-(1-(1-C)/S)/(1+(1-C)/S))-
          (1-C*C-S*S)/(C*(1+S-C)))
    constants=[]
    def exact(name,value,expected):
        assert sp.factor(value)==expected,(name,value)
        constants.append({"name":name,"value":str(expected)})
    exact("Ys lower denominator at l=1/2",4-4*sp.Rational(1,2)-sp.Rational(1,2)**2,sp.Rational(7,4))
    exact("combined deficit coefficient",sp.Rational(2,7)+sp.Rational(2,3),sp.Rational(20,21))
    exact("after u<9eta/7",sp.Rational(20,21)*sp.Rational(9,7),sp.Rational(60,49))
    exact("1-G coefficient at eta=5/12",2/(1+sp.Rational(5,12)),sp.Rational(24,17))
    exact("positive rational gap",sp.Rational(24,17)-sp.Rational(60,49),sp.Rational(156,833))
    result={"queries":rows,"symbolic_identities":identities,"constants":constants,
        "totals":{"UNSAT":len(rows),"NRA":sum(r["theory"]=="QF_NRA" for r in rows),
                  "LRA":sum(r["theory"]=="QF_LRA" for r in rows),
                  "symbolic_identities":len(identities),"constants":len(constants)},
        "scope":"Entire far RIGHT real gap and positive nonempty F horizontal, including tangency",
        "not_proved":"RIGHT negative/empty F H; LEFT remaining; three meetings with empty F H; S(6)=2"}
    Path(__file__).with_name("round32_right_positive_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
