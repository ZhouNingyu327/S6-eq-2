import sympy as s
import z3
h,w=s.symbols("h w")
g=lambda a:(1-a)/(1+a)
q=lambda a:a/(2-a)
delta=lambda a:2*a*a/(1-a*a)
ys=lambda a:(1-a)**2/(6*a-1-a*a)
k=2*h/(1-h*h)
M=q(h)+q(g(h))
rho=delta(h)
G=g(h)
budget=(1-2*h)/((1-h)**2*(1+h))*(2-h-G)*(2-h)-(1+k*G)
small=(1-rho-h*h/(1-2*h-h*h))**2-M
R=delta(w/2)
Y=ys(1-w)
endpoint0=1-g(1-w)-q(1-w)-2*R+R*R
endpointY=(1-R-Y)**2-q(1-w+delta(Y))
exprs=[("complement M compensation",budget,h,s.Rational(1,4)),
       ("small complementary M root",small,h,s.Rational(7,30)),
       ("small angle y=0",endpoint0,w,s.Rational(1,2)),
       ("small angle y=Ys",endpointY,w,s.Rational(1,2))]
for name,expr,var,upper in exprs:
    expr=s.factor(expr);P,D=s.fraction(expr)
    print(name,expr,flush=True)
    zz=z3.Real(str(var))
    def zp(poly):
        return sum(z3.RealVal(str(c))*(zz**int(p[0]) if p[0] else 1)
                   for p,c in s.Poly(poly,var).terms())
    solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000)
    solver.add(zz>0,zz<=z3.RealVal(str(upper)),zp(P)*zp(D)<=0)
    ans=solver.check();print("CHECK",ans,flush=True)
    if ans==z3.sat:print(solver.model(),flush=True)
print("M(7/30)",M.subs(h,s.Rational(7,30)),flush=True)
