import sympy as sp
import z3
h,x=sp.symbols("h x")
g=lambda a:(1-a)/(1+a)
q=lambda a:a/(2-a)
k=2*h/(1-h*h)
b=2*h/(1+h)
m=x-h*g(h)
E=g(x)+q(x-b)+q(m)
F=sp.factor((1-k*m)**2-E)
P,D=sp.fraction(F)
print("factor",F,flush=True)
hh,xx=z3.Reals("h x")
def zz(poly):
    return sum(z3.RealVal(str(c))*(hh**int(p[0]) if p[0] else 1)*(xx**int(p[1]) if p[1] else 1)
               for p,c in sp.Poly(poly,h,x).terms())
solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000)
solver.add(hh>0,4*hh<=1,xx*(1+hh)>2*hh,2*xx<=1,
           zz(P)*zz(D)<0)
ans=solver.check();print("small-negative x<=1/2",ans,flush=True)
if ans==z3.sat:print(solver.model())
