"""Local exact checks for G2 near TOP gap; no layout or point-cover search."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def main():
    rows=[]
    def query(name,cs,theory="QF_NRA"):
        solver=z3.SolverFor(theory);solver.set(timeout=20000);solver.add(*cs)
        started=time.perf_counter();answer=solver.check()
        row={"name":name,"theory":theory,"result":str(answer),
             "seconds":time.perf_counter()-started}
        if answer!=z3.unsat:
            row["detail"]=str(solver.model()) if answer==z3.sat else solver.reason_unknown()
        print(json.dumps(row),flush=True)
        assert answer==z3.unsat,row
        rows.append(row)

    h,x,y,T,l,r,u,d,z,mu,B,L3,U2,U4,S4=z3.Reals(
        "h x y T l r u d z mu B L3 U2 U4 S4")
    p,s=z3.Reals("p s")
    normal=[mu>1,p>=s,s>0,p*p+s*s==1,h*(1+p)==s]
    query("actual C halfangle h<5/12 and k<=1",
          normal+[z3.Or(12*h>=5,2*h>1-h*h)])
    query("actual positive P/R width forces r+T<h",
          normal+[T>0,r>0,s*(r+T)+p*mu<=1,r+T>=h])
    query("actual positive P/down width forces d<rho-kT",
          normal+[s*T+p*(mu+d)<=1,d*(1-h*h)>=2*h*h-2*h*T])
    query("actual negative P/R width forces r+T<g(h)",
          normal+[p*(r+T)+s*mu<=1,(r+T)*(1+h)>=1-h])
    query("actual negative P/left width forces l<T+h",
          normal+[p*mu+s*(l-T)<=1,l>=T+h])
    query("actual negative P/down width forces d<rho+kT",
          normal+[p*(mu+d)-s*T<=1,d*(1-h*h)>=2*h*h+2*h*T])
    query("parallel C/V4 bounds exclude C containing left inner endpoint",[
        mu>1,B<1,l>=mu-U4,r>=mu-U2,
        l+r+mu+T-L3<=B,T==mu-S4,S4+U4<=B,L3+U2<2],"QF_LRA")
    query("right meeting gives L3+U2<2",[
        x>0,y>0,15*y<4,x+y<1,U2<x,
        L3*(1-y*y)<=1+y*y,L3+U2>=2])
    query("TOP short endpoint forces z<q(T)",[
        z>0,z<1,T>2*z/(1+z),T<1,z>=T/(2-T)])
    query("C top/horizontal width implies l+T<x+delta(y)",[
        mu>1,B<1,y>0,y<1,r>1-x,
        l+r+mu+T-L3<=B,L3*(1-y*y)<=1+y*y,
        (l+T-x)*(1-y*y)>=2*y*y])
    query("positive r+T<h forces x>7/12",[
        h>0,12*h<5,T>0,r>1-x,r+T<h,12*x<=7],"QF_LRA")
    query("Ys decreasing on x>=1/2",[
        2*x>=1,x<1,4*(x*x-1)>=0])
    query("right meeting sine cap gives y<1/7 on x>=1/2",[
        2*x>=1,x<1,y>0,y*(6*x-1-x*x)<(1-x)*(1-x),7*y>=1])
    query("positive C l+d<1",[
        h>0,12*h<5,y>0,7*y<1,
        l<(1-h)/(1+h)+2*h*y/(1-h*h),
        d<2*h*h/(1-h*h),l+d>=1])
    query("negative small C l+d<1",[
        h>0,4*h<1,x+y<1,T<x-2*h/(1+h),
        l<T+h,d<2*h*h/(1-h*h)+y,l+d>=1])
    a,b=z3.Reals("alpha beta")
    query("one original corner cannot contain both C endpoints with l+d<1",[
        mu>1,a>0,b>0,a*a+b*b==1,l+d<1,
        a*(mu-l)+b*mu<=1,a*mu+b*(mu-d)<=1])
    A,U=z3.Reals("A U")
    query("original W bridge gives A<U4+q(l)",[
        mu>1,a>0,b>0,a*a+b*b==1,l>0,l<1,
        a*(mu-l)+b*mu<=1,b*(A-U)+a*mu<=1,
        A>=U+l/(2-l)])
    Sigma,bF,v=z3.Reals("Sigma bF v")
    query("real bottom chord implies Sigma>7/12",[
        mu>1,bF>=2*mu-Sigma,bF*bF<=2,bF>=0,12*Sigma<=7])
    query("real F bottom chord/root implies Sigma>(1-d)^2",[
        mu>1,d>=0,d<1,v>=mu-d,bF>=2*mu-Sigma,
        bF+v*v<=2,Sigma<=(1-d)*(1-d)])
    query("q is superadditive for nonnegative arguments",[
        a>=0,b>=0,a+b<2,a/(2-a)+b/(2-b)>(a+b)/(2-a-b)])
    query("q convex split bounded by outer endpoint",[
        h>0,h<1,T>=0,T<=h,T/(2-T)+(h-T)/(2-h+T)>h/(2-h)])
    query("negative small-h projected ray envelope",[
        h>0,4*h<1,T<x-2*h/(1+h),l<T+h,
        d<2*h*(h+T)/(1-h*h),
        z3.Or(l>=x-h*(1-h)/(1+h),
              d>=2*h*(x-h*(1-h)/(1+h))/(1-h*h))])
    w=z3.Real("w")
    Y=w*w/(4-4*w-w*w)
    R=2*w*w/(4-w*w)
    query("small complementary angle domain and root bound",[
        w>0,2*w<=1,z3.Or(Y>z3.Q(1,7),Y>2*w/7,R+Y>=1)])
    query("small complementary delta(Y)<w",[
        w>0,2*w<=1,2*Y*Y/(1-Y*Y)>=w])
    query("negative small complement d<rho+Z<1",[
        h>0,4*h<=1,2*h*h/(1-h*h)+h*h/(1-2*h-h*h)>=1])
    query("negative compensation criterion covers h>=1/4 at T=0",[
        h>=z3.Q(1,4),12*h<5,
        (2*h/(1-h*h))*(4*h*(1+h)/((1-h)*(1+3*h)))*(2-h)**2<=1])

    H,X,W,YY=sp.symbols("h x w y")
    g=lambda t:(1-t)/(1+t)
    q=lambda t:t/(2-t)
    delta=lambda t:2*t*t/(1-t*t)
    kval=2*H/(1-H*H);G=g(H);rho=delta(H);M=q(H)+q(G)
    bv=1-G;mv=X-H*G
    P5=31*H**5-47*H**4-42*H**3+34*H*H+15*H-7
    P8=424*H**8-716*H**7-1032*H**6-555*H**5+594*H**4+594*H**3+56*H*H-67*H-18
    P9=52*H**9+78*H**8-290*H**7-344*H**6+431*H**5+231*H**4-224*H**3-38*H*H+47*H-7
    Q=51*W**11+440*W**10+508*W**9-3656*W**8-4792*W**7+15424*W**6+8384*W**5-32128*W**4+4480*W**3+26624*W*W-19456*W+4096
    R4=310904*W**4+167680*W**3-385536*W*W+26880*W+53248
    identities=[]
    def ident(name,expr):
        print(json.dumps({"symbolic_check":name}),flush=True)
        assert sp.cancel(expr)==0,name
        identities.append(name)
    ident("negative small angle margin hG-rho",H*G-rho-H*(1-4*H+H*H)/(1-H*H))
    ident("M derivative",sp.diff(M,H)-14*(H*H+2*H-1)/((2-H)**2*(1+3*H)**2))
    ident("small M square gap",(1-rho)**2-M-H*P5/((H-2)*(H-1)**2*(H+1)**2*(3*H+1)))
    E=g(X)+q(X-bv)+q(mv)
    F=(1-kval*mv)**2-E
    ident("small x lower endpoint F(b)",F.subs(X,bv)-(1-rho)**2+M)
    ident("small x half endpoint",F.subs(X,sp.Rational(1,2))-
          H*P8/(3*(H-3)*(H-1)**2*(H+1)**4*(2*H+1)*(7*H+3)))
    K0,B0,C0=sp.symbols("K0 B0 C0")
    freeF=(1-K0*(X-C0))**2-g(X)-q(X-B0)-q(X-C0)
    ident("small x concavity derivative for arbitrary constant offsets",
          sp.diff(freeF,X,2)-
          (2*K0*K0-4/(1+X)**3-4/(2-X+B0)**3-4/(2-X+C0)**3))
    ident("negative compensation endpoint difference",q(H+sp.Symbol("t"))-q(H)-
          2*sp.Symbol("t")/((2-H-sp.Symbol("t"))*(2-H)))
    ident("k logarithmic derivative",sp.diff(2*X/(1-X*X),X)/(2*X/(1-X*X))-
          (1+X*X)/(X*(1-X*X)))
    ident("k log derivative exceeds two",
          (1+X*X)-2*X*(1-X*X)-((1-X)**2+2*X**3))
    comp=(1-2*H)/((1-H)**2*(1+H))*(2-H-G)*(2-H)-(1+kval*G)
    ident("complement M compensation",comp+
          (3*H**4-7*H**3+4*H*H+3*H-1)/((1-H)**2*(1+H)**2))
    ys=lambda t:(1-t)**2/(6*t-1-t*t)
    ident("Ys derivative",sp.diff(ys(X),X)-4*(X*X-1)/(6*X-1-X*X)**2)
    ident("right short leg vanishes at sine cap",g(X)-2*(2*X/(1-X*X))*ys(X)/(1+ys(X)))
    ident("Ys complement h",ys(1-2*H)-H*H/(1-2*H-H*H))
    Z=H*H/(1-2*H-H*H)
    ident("small complementary M root",(1-rho-Z)**2-M-
          H*P9/((H-2)*(H-1)**2*(H+1)**2*(3*H+1)*(H*H+2*H-1)**2))
    ycap=W*W/(4-4*W-W*W);rbound=delta(W/2)
    zero=1-g(1-W)-q(1-W)-2*rbound+rbound*rbound
    ident("convex-y zero endpoint",zero-W*(11*W**4+11*W**3-34*W*W-28*W+24)/
          ((W-2)**2*(W+1)*(W+2)**2))
    end=(1-rbound-ycap)**2-q(1-W+delta(ycap))
    ident("convex-y sine-cap endpoint",end-W*Q/
          ((W-2)**2*(W+2)**2*(W*W+4*W-4)**2*(3*W**4+8*W**3-12*W*W-8*W+8)))
    ident("Q second derivative positive lower bound",sp.diff(Q,W,2)-R4-
          (5610*W**9+39600*W**8+36576*W**7+
           W**4*(151816-201264*W-204736*W*W)))
    weights=[53248,56608,43904,20376,sp.Rational(21391,2)]
    ident("R4 explicit five-term nonnegative decomposition",R4-sum(
        sp.binomial(4,j)*weights[j]*(2*W)**j*(1-2*W)**(4-j) for j in range(5)))
    ident("delta derivative",sp.diff(delta(YY),YY)-4*YY/(1-YY*YY)**2)
    ident("delta second derivative",sp.diff(delta(YY),YY,2)-
          4*(1+3*YY*YY)/(1-YY*YY)**3)
    ident("q superadditivity",q(sp.Symbol("a")+sp.Symbol("b"))-
          q(sp.Symbol("a"))-q(sp.Symbol("b"))-
          sp.Symbol("a")*sp.Symbol("b")*(4-sp.Symbol("a")-sp.Symbol("b"))/
          ((2-sp.Symbol("a"))*(2-sp.Symbol("b"))*(2-sp.Symbol("a")-sp.Symbol("b"))))
    def at(poly,var=H,zvar=h):
        return sum(z3.RealVal(str(c))*(zvar**int(p[0]) if p[0] else 1)
                   for p,c in sp.Poly(sp.expand(poly),var).terms())
    query("P5 derivative positive by projected cap",[
        h>=0,3*h<=1,at(sp.diff(P5,H))<15+z3.Q(46,9)*h])
    query("small x half endpoint numerator negative",[
        h>0,4*h<=1,at(P8)>=0])
    query("complement compensation quartic increases",[
        h>=0,4*h<=1,12*h**3-21*h*h+8*h+3<=0])
    query("P9 second derivative bounded by negative affine expression",[
        h>=0,30*h<=7,
        at(sp.diff(P9,H,2))>(z3.Q(472388812,421875)-1344)*h-76])
    query("Q second derivative lower bound remainder nonnegative",[
        w>=0,2*w<=1,151816-201264*w-204736*w*w<0])
    query("convex-y zero endpoint numerator positive",[
        w>=0,2*w<=1,11*w**4+11*w**3-34*w*w-28*w+24<=0])
    query("convex-y sine endpoint denominator factor positive",[
        w>=0,2*w<=1,3*w**4+8*w**3-12*w*w-8*w+8<=0])
    query("convex-y S term dominates concavity",[
        x>=z3.Q(1,2),x<1,y>=0,7*y<=1,
        4*(2*x/(1-x*x))/(1+y)**3<=2])

    constants=[]
    def const(name,truth):
        assert bool(truth),name
        constants.append(name)
    const("positive compensation constants",sp.Rational(168,95)>sp.Rational(19,15))
    const("M quarter",M.subs(H,sp.Rational(1,4))==sp.Rational(4,7))
    const("M third",M.subs(H,sp.Rational(1,3))==sp.Rational(8,15))
    const("M threshold",M.subs(H,sp.Rational(7,30))==sp.Rational(1576,2703))
    const("M threshold diameter",sp.Rational(1576,2703)<sp.Rational(7,12))
    const("diameter 17/12 exceeds sqrt2",sp.Rational(17,12)**2>2)
    const("large M below 7/12",sp.Rational(8,15)<sp.Rational(7,12))
    const("P5 endpoint",P5.subs(H,sp.Rational(1,3))==-sp.Rational(56,243))
    const("small x concavity constants",sp.Rational(128,225)<sp.Rational(32,27))
    const("P8 positive terms bound",sp.Rational(424,4**8)+sp.Rational(594,4**4)+
          sp.Rational(594,4**3)+sp.Rational(56,4**2)==sp.Rational(123765,8192))
    const("P8 bound below 18",sp.Rational(123765,8192)<18)
    const("large h compensation product",sp.Rational(8,15)*sp.Rational(20,21)*
          sp.Rational(19,12)**2==sp.Rational(722,567))
    const("large h product >1",sp.Rational(722,567)>1)
    quartic=3*H**4-7*H**3+4*H*H+3*H-1
    const("compensation quartic endpoint",quartic.subs(H,sp.Rational(1,4))==-sp.Rational(25,256))
    av=sp.Rational(7,30)
    const("P9 concavity coefficient",3744*av**6+4368*av**5+8620*av*av+2772*av==
          sp.Rational(472388812,421875))
    const("P9 concavity coefficient <1344",sp.Rational(472388812,421875)<1344)
    const("P9 endpoint derivative",sp.diff(P9,H).subs(H,av)==sp.Rational(55151949841,6075000000))
    const("P9 derivative positive",sp.Rational(55151949841,6075000000)>0)
    const("P9 endpoint",P9.subs(H,av)==-sp.Rational(75452942887,2460375000000))
    const("Q endpoint",Q.subs(W,sp.Rational(1,2))==sp.Rational(58835,2048))
    const("Q endpoint derivative",sp.diff(Q,W).subs(W,sp.Rational(1,2))==-sp.Rational(767615,1024))
    const("R4 positive weights",all(weight>0 for weight in weights))
    const("convex y coefficient",sp.Rational(343,96)>2)
    const("convex zero coarse bound",24-sp.Rational(34,4)-14==sp.Rational(3,2))
    const("small-ray margin quarter",1-4*sp.Rational(1,4)+sp.Rational(1,4)**2>0)
    result={"scope":"G2 near C-TOP real gap, RIGHT/LEFT meeting, F horizontal empty excluded",
            "queries":rows,"symbolic_identities":identities,"constants":constants,
            "totals":{"UNSAT":len(rows),"NRA":sum(v["theory"]=="QF_NRA" for v in rows),
                      "LRA":sum(v["theory"]=="QF_LRA" for v in rows),
                      "symbolic_identities":len(identities),"constants":len(constants)}}
    (Path(__file__).resolve().parent/"round26_g2_top_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result["totals"]),flush=True)


if __name__=="__main__":
    main()
