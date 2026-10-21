"""Exact local checks for the forced interior seam lemma."""
from pathlib import Path
import json,time
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

    a,z,L,M,S,mu,X,e,ca,sa,cz,sz = z3.Reals("a z L M S mu X e ca sa cz sz")
    ba=(1+a*a)/(1-a*a);ka=2*a/(1-a*a)
    kz=2*z/(1-z*z);gz=(1-z)/(1+z)
    Yc=a*a/(1-2*a*a);Ys=(1-a)*(1-a)/(6*a-1-a*a)
    query("cosine range gives z<a and a+2z<1",[
        a>0,5*a<=2,z>0,z<Yc,z3.Or(z>=a,a+2*z>=1)])
    query("sine range gives z<a and a+2z<1",[
        5*a>=2,a<1,z>0,z<Ys,z3.Or(z>=a,a+2*z>=1)])
    query("meeting gives cosine angle envelope",[
        a>0,5*a<=2,z>0,z<1,L>2-gz,L<=ba,z>=Yc])
    query("meeting gives sine angle envelope",[
        5*a>=2,a<1,z>0,z<1,L>2-gz,2*a*L<=1+a*a,z>=Ys])
    query("seam horizontal coordinate is below a",[
        a>0,a<1,z>0,z<a,a+z<1,mu>1,S<gz,
        X*(ka-kz)==ba+S-2*mu,X>=a])
    query("seam height is positive",[
        a>0,a<1,z>0,z<a,a+z<1,mu>1,S<gz,
        X>=0,X<a,e==mu-S-kz*X,e<=0])
    query("positive-normal cap for the upper corner",[
        z>0,z<1,cz*(1+z*z)==1-z*z,sz*(1+z*z)==2*z,
        S<gz,X<1-2*z, X>=cz*(1-sz*S)])
    # The crossing is after the lower corner's turn from one support to the other.
    A0,B0,N,X0,meet=z3.Reals("A0 B0 N X0 meet")
    query("meeting puts seam after the turn",[
        A0>B0,B0>=0,X0>=0,meet>=0,
        N==(A0+1/A0)*X0+meet,
        X*(A0-B0)==N,X<X0])
    query("second side of lower square contains seam",[
        a>0,a<1,ca*(1+a*a)==1-a*a,sa*(1+a*a)==2*a,
        sa*L<=1,X<a,X>ca+sa-ca*sa*L])
    # New upper contact/long-leg link, independent of any C side contact.
    u=z3.Real("u")
    query("direct upper contact forces L>2-q(u)",[
        mu>1,z>0,z<1,u>1-z,u<1,L+S>=2*mu,S<gz,
        L<=2-u/(2-u)])

    aa,zz,ll,ss,mm,xx=sp.symbols("a z L S mu X")
    cc=(1-aa**2)/(1+aa**2);sn=2*aa/(1+aa**2)
    bb=(1+aa**2)/(1-aa**2);kk=2*aa/(1-aa**2)
    czs=(1-zz**2)/(1+zz**2);szs=2*zz/(1+zz**2)
    g=(1-zz)/(1+zz);kzz=2*zz/(1-zz**2)
    ids=[]
    def ident(name,expr):
        assert sp.cancel(expr)==0,(name,sp.factor(expr));ids.append(name)
    ident("seam upper-bound residual",
          bb+g-2-aa*(kk-kzz)-2*zz*(aa+zz-1)/(1-zz**2))
    ident("seam positive-height residual",
          1-g-kzz*aa-2*zz*(1-zz-aa)/(1-zz**2))
    ident("lower-corner turning coordinate",
          (bb-ll)/(kk+1/kk)-sn*(1-cc*ll))
    ident("lower-corner second projection",
          cc*xx-sn*(bb-kk*xx)-(xx/cc-kk))
    ident("upper-corner first support slack",
          czs*(1-szs*g)-(1-2*zz)
          -2*zz**2*(zz**3-zz**2+zz+1)/(1+zz**2)**2)
    ident("upper-corner first projection",
          czs*xx+szs*(ss+kzz*xx)-(xx/czs+szs*ss))

    constants=[]
    def constant(name,expr,expected):
        assert sp.factor(expr)==expected
        constants.append({"name":name,"value":str(expected)})
    constant("cosine a+2z margin",1-sp.Rational(2,5)-2*sp.Rational(4,17),
             sp.Rational(11,85))
    constant("sine angle sum numerator at 2/5",
             (aa**2-8*aa+3).subs(aa,sp.Rational(2,5)),-sp.Rational(1,25))
    constant("sine z<a numerator at 2/5",
             (aa**3-5*aa**2-aa+1).subs(aa,sp.Rational(2,5)),
             -sp.Rational(17,125))
    result={"queries":rows,"query_count":len(rows),"identities":ids,
            "identity_count":len(ids),"constants":constants,
            "constant_count":len(constants),
            "scope":"small algebraic lemmas; geometric covering/closedness argument is in the report"}
    result_dir=Path("outputs") if Path("outputs").is_dir() else Path(".")
    (result_dir/"S6_round40_seam_verification.json").write_text(
        json.dumps(result,indent=2),encoding="utf-8")
if __name__=="__main__":main()
