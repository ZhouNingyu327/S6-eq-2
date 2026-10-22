"""Exact small lemmas for the complete G3 F-side double-host exclusion.

This checks scalar inequalities/identities, not geometric ownership and not
six-square layouts. Read the report and its separate geometric review.
"""
from pathlib import Path
import json
import time
import sympy as sp
import z3

HERE = Path(__file__).resolve().parent


def query(name, premises, theory="QF_NRA"):
    sol = z3.SolverFor(theory)
    sol.set(timeout=20000)
    sol.add(*premises)
    started = time.perf_counter()
    answer = sol.check()
    row = {"name":name, "theory":theory, "result":str(answer),
           "seconds":time.perf_counter()-started}
    if answer != z3.unsat:
        row["detail"] = str(sol.model()) if answer == z3.sat else sol.reason_unknown()
    print(json.dumps(row), flush=True)
    assert answer == z3.unsat, row
    return row


def main():
    rows = []
    h,a,w,e,r,mu,p,s,u,d,G,lam,rho = z3.Reals(
        "r24_h r24_a r24_w r24_e r24_r r24_mu r24_p r24_s "
        "r24_u r24_d r24_G r24_lam r24_rho")
    domain = [h>0,h*h+2*h<=1]
    rows.append(query("C halfangle h<5/12", domain+[12*h>=5]))
    normal = [p>0,s>0,p>=s,p*p+s*s==1,h*(1+p)==s,mu>1]
    rows.append(query("C small upper ray u<h", normal+[p*mu+s*u<=1,u>=h]))
    rows.append(query("C large lower ray d<g(h)", normal+[
        s*mu+p*d<=1,G*(1+h)==1-h,d>=G]))
    rows.append(query("C joint upper-left/down rays lambda+d<g(h)", normal+[
        s*mu+p*(lam+d)<=1,G*(1+h)==1-h,lam+d>=G]))
    rows.append(query("C joint lower-left/up rays rho+u<h", normal+[
        p*mu+s*(rho+u)<=1,rho+u>=h]))
    rows.append(query("C horizontal chord implies r<delta(h)", normal+[
        h<1,p*(mu+r)<=1,r*(1-h*h)>=2*h*h]))

    b,f,S = z3.Reals("r24_b r24_f r24_S")
    rows.append(query("real F right chord and root ray imply S>(1-r)^2",[
        mu>1,r>=0,r<1,b>=2*mu-S,f>=mu-r,b+f*f<=2,
        S<=(1-r)*(1-r)]))
    rows.append(query("real F right chord diameter implies S>4/7",[
        mu>1,b>=0,b>=2*mu-S,b*b<=2,7*S<=4]))

    H = sp.symbols("h")
    g = lambda t:(1-t)/(1+t)
    q = lambda t:t/(2-t)
    delta = lambda t:2*t*t/(1-t*t)
    GS = g(H)
    M = q(H)+q(GS)
    A = 1-GS-q(H)
    Ab = 1-H-q(GS)
    T0 = g(A)
    P = 82-185*H-401*H**2+514*H**3+556*H**4-377*H**5+3*H**6
    Q = 3-7*H-14*H**2+22*H**3+19*H**4-19*H**5
    identities = []

    def identity(name, expr):
        assert sp.cancel(expr) == 0, name
        identities.append(name)

    identity("M simplified",M-H/(2-H)-(1-H)/(1+3*H))
    identity("M derivative",sp.diff(M,H)-14*(H*H+2*H-1)/
             ((2-H)**2*(1+3*H)**2))
    identity("small M budget polynomial",
             (1-delta(H))**2-M-H/12-
             H*P/(12*(2-H)*(1-H*H)**2*(1+3*H)))
    identity("small T0 budget polynomial",
             (1-delta(H))**2-T0-H*Q/
             ((1-H*H)**2*(1+2*H-2*H*H)))
    identity("A simplified",A-3*H*(1-H)/((1+H)*(2-H)))
    identity("A-3/10 sign",A-sp.Rational(3,10)-
             3*(2-3*H)*(3*H-1)/(10*(2-H)*(1+H)))
    identity("Ab-A sign",Ab-A-
             3*H*(1-H)*(1-2*H-H*H)/((2-H)*(1+H)*(1+3*H)))

    def at(expr):
        return sum(z3.RealVal(str(coef))*(h**int(power[0]) if power[0] else 1)
                   for power,coef in sp.Poly(sp.expand(expr),H).terms())

    rows.append(query("P derivative hand bound on [0,1/3]",[
        h>=0,3*h<=1,at(sp.diff(P,H))>-185-z3.RealVal("122/3")*h]))
    rows.append(query("P positive on [0,1/3]",[
        h>=0,3*h<=1,at(P)<=0]))
    rows.append(query("Q derivative hand bound on [0,1/3]",[
        h>=0,3*h<=1,at(sp.diff(Q,H))>-z3.RealVal("113/27")-6*h]))
    rows.append(query("Q positive on [0,1/3]",[
        h>=0,3*h<=1,at(Q)<=0]))
    rows.append(query("large h A>=3/10",domain+[
        3*h>=1,3*h*(1-h)<z3.RealVal("3/10")*(1+h)*(2-h)]))
    rows.append(query("Ab>=A on halfangle domain",domain+[
        3*h*(1-h)*(1-2*h-h*h)<0]))

    T,U,D,c,ss,cornerD = z3.Reals("r24_T r24_U r24_D r24_c r24_ss r24_cornerD")
    rows.append(query("original corner inner endpoint forces T>1-u",[
        c>0,ss>0,c*c+ss*ss==1,T*(1+c)==ss,
        mu>1,u>=0,u<1,c*mu+ss*(mu-u)<=1,T<=1-u]))
    rows.append(query("bridge projection and angle imply D<U+q(u)",[
        u>=0,u<1,T>1-u,T<1,
        cornerD<U+(1-T)/(1+T),
        cornerD>=U+u/(2-u)]))

    # Separate convexity is checked by the chain-rule identity and positivity.
    X,Y,C = sp.symbols("x y C")
    inner=C+X-q(Y)
    outer=g(inner)
    identity("bridge convexity chain rule",
             sp.diff(outer,Y,2)-
             (4/(1+inner)**3*sp.diff(q(Y),Y)**2+
              2/(1+inner)**2*sp.diff(q(Y),Y,2)))
    identity("g second derivative",sp.diff(g(X),X,2)-4/(1+X)**3)
    identity("q second derivative",sp.diff(q(X),X,2)-4/(2-X)**3)
    rows.append(query("q(q(t))<=q(t) on [0,1]",[
        u>=0,u<=1,(u/(2-u))/(2-u/(2-u))>u/(2-u)]))

    # Each of the four direct/bridge combinations is separately convex.
    # Check all 16 symbolic corner values against their stated expressions.
    combos = [
        (1-Y,1-X,[0,q(GS),q(H),M]),
        (1-Y,1-GS+Y-q(X),[q(GS),q(GS),T0,q(GS)+q(q(H))]),
        (1-H+X-q(Y),1-X,[q(H),g(Ab),q(H),q(H)+q(q(GS))]),
        (1-H+X-q(Y),1-GS+Y-q(X),[M,g(Ab),T0,q(q(H))+q(q(GS))])
    ]
    corners = [(0,0),(0,GS),(H,0),(H,GS)]
    for i,(lo2,lo3,expected) in enumerate(combos):
        for j,((xx,yy),value) in enumerate(zip(corners,expected)):
            identity(f"convex corner {i}-{j}",
                     (g(lo2)+g(lo3)).subs({X:xx,Y:yy})-value)

    Mv,J,root = z3.Reals("r24_M r24_J r24_root")
    rows.append(query("small-h M slack excludes J<=h/24",[
        h>0,Mv+h/12<root,S<Mv+2*J,J<=h/24,S>root],"QF_LRA"))
    rows.append(query("large-h M bound excludes J<=h/24",[
        h<z3.RealVal("5/12"),Mv<=z3.RealVal("8/15"),
        S<Mv+2*J,J<=h/24,S>z3.RealVal("4/7")],"QF_LRA"))
    rows.append(query("cosine kappa cap implies w<2a/3 for a<=2/5",[
        a>0,5*a<=2,w>0,w*(1-2*a*a)<a*a,3*w>=2*a]))
    rows.append(query("global kappa cap implies w<2a/3 for a>=2/5",[
        5*a>=2,15*w<4,3*w>=2*a],"QF_LRA"))
    rows.append(query("epsilon<80a/209 from both hand kappa caps",[
        a>0,w>0,15*w<4,3*w<2*a,
        e*(1-w*w)==2*w*w,209*e>=80*a]))
    rows.append(query("negative C rotation small-angle denominator >2",[
        h>0,12*h<5,4-4*h-h*h<=2]))
    rows.append(query("negative C rotation epsilon<h/24",[
        h>0,12*h<5,w>0,w<h*h/2,8*w<1,
        e*(1-w*w)==2*w*w,24*e>=h]))
    rows.append(query("positive C rotation lower axis gives h<a/(2-a)",[
        a>0,a<1,h>0,h<1,G*(1+h)==1-h,
        d<G,d>1-a,h*(2-a)>=a]))
    rows.append(query("positive C rotation r<Delta(a)",[
        a>0,a<1,h>0,h<1,h*(2-a)<a,
        r*(1-h*h)<2*h*h,2*(1-a)*r>=a*a]))
    rows.append(query("positive C rotation q(h)<a/(4-3a)",[
        a>0,a<1,h>0,h<1,h*(2-a)<a,
        h*(4-3*a)>=a*(2-h)]))
    rows.append(query("small-a F root estimate 2Delta<=9a/11",[
        a>0,20*a<=9,a*a/(1-a)>9*a/11]))
    rows.append(query("middle-a Ys cap w<3/14",[
        20*a>=9,a<1,w>0,w*(6*a-1-a*a)<(1-a)*(1-a),14*w>=3]))
    rows.append(query("middle-a epsilon<1/10",[
        w>0,14*w<3,e*(1-w*w)==2*w*w,10*e>=1]))
    rows.append(query("large-a Ys cap w<1/7",[
        2*a>=1,a<1,w>0,w*(6*a-1-a*a)<(1-a)*(1-a),7*w>=1]))
    rows.append(query("large-a epsilon<1/24",[
        w>0,7*w<1,e*(1-w*w)==2*w*w,24*e>=1]))

    Avar = sp.symbols("a")
    Ys=(1-Avar)**2/(6*Avar-1-Avar*Avar)
    identity("Ys derivative",sp.diff(Ys,Avar)-
             4*(Avar*Avar-1)/(6*Avar-1-Avar*Avar)**2)
    identity("Ys(1-h)",Ys.subs(Avar,1-H)-H*H/(4-4*H-H*H))
    identity("delta of a/(2-a)",delta(Avar/(2-Avar))-
             Avar*Avar/(2*(1-Avar)))
    identity("q of a/(2-a)",q(Avar/(2-Avar))-Avar/(4-3*Avar))

    constants = {
        "P(1/3)":P.subs(H,sp.Rational(1,3))==sp.Rational(32,243),
        "Q(1/3)":Q.subs(H,sp.Rational(1,3))==sp.Rational(20,243),
        "M(1/3)":sp.cancel(M.subs(H,sp.Rational(1,3)))==sp.Rational(8,15),
        "409/720<4/7":sp.Rational(409,720)<sp.Rational(4,7),
        "10/7>sqrt2":sp.Rational(100,49)>2,
        "7/13<4/7":sp.Rational(7,13)<sp.Rational(4,7),
        "8/15<4/7":sp.Rational(8,15)<sp.Rational(4,7),
        "10/17<2/3":sp.Rational(10,17)<sp.Rational(2,3),
        "80/209<2/5":sp.Rational(80,209)<sp.Rational(2,5),
        "125/3402<1/24":sp.Rational(125,3402)<sp.Rational(1,24),
        "1060/1189>9/11":sp.Rational(1060,1189)>sp.Rational(9,11),
        "121/599<3/14":sp.Rational(121,599)<sp.Rational(3,14),
        "18/187<1/10":sp.Rational(18,187)<sp.Rational(1,10),
        "274/493<4/7":sp.Rational(274,493)<sp.Rational(4,7),
        "139/456<1/3":sp.Rational(139,456)<sp.Rational(1,3),
    }
    assert all(bool(v) for v in constants.values())
    result = {"status":"all exact small checks passed",
              "queries":rows,
              "totals":{"UNSAT":len(rows),
                        "NRA":sum(x["theory"]=="QF_NRA" for x in rows),
                        "LRA":sum(x["theory"]=="QF_LRA" for x in rows),
                        "symbolic_identities":len(identities),"constants":len(constants)},
              "symbolic_identities":identities,
              "constants":{name:bool(v) for name,v in constants.items()},
              "scope":"G3 TOP V3 / BOTTOM V2 hand proof scalar checks; ownership reviewed separately",
              "not_proved":"Other G3 representatives; remaining G2; S(6)=2"}
    (HERE/"round24_g3_fside_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps({"status":result["status"],"totals":result["totals"]}),flush=True)


if __name__ == "__main__":
    main()
