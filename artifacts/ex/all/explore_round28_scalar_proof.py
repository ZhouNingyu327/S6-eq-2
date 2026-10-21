import sympy as s
import z3
h,w=s.symbols("h w")
K=2*h/(1-h*h);G=(1-h)/(1+h)
P=36*h**4-132*h**3-145*h*h+82*h-11
Q=30*w**3-98*w*w+92*w-25
P5=25*w**5-296*w**3+544*w*w-429*w+200
P7=4*w**7-8*w**6-33*w**5+120*w**4-168*w**3+168*w*w-116*w+32
for name,expr,var,upper,positive in [
    ("angle quartic",P,h,s.Rational(5,12),False),
    ("Gamma cubic",Q,w,s.Rational(5,12),False),
    ("W-down endpoint 0",P5,w,s.Rational(5,12),True),
    ("W-down endpoint w",P7,w,s.Rational(5,12),True)]:
    zz=z3.Real(str(var))
    val=sum(z3.RealVal(str(c))*(zz**int(p[0]) if p[0] else 1)
            for p,c in s.Poly(expr,var).terms())
    solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000)
    solver.add(zz>=0,zz<=z3.RealVal(str(upper)),val<=0 if positive else val>=0)
    ans=solver.check();print(name,ans,flush=True)
    if ans==z3.sat:print(solver.model(),flush=True)
print("balance identity",s.factor(s.Rational(6,5)*h*G-K*(1-K)*(h+s.Rational(5,12))+
    h*P/(30*(1-h*h)**2)))
