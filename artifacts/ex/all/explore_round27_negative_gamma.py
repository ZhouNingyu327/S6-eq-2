import z3
h,e,y,u,d,E3,l=z3.Reals("h e y u d E3 l")
K=2*h/(1-h*h);G=(1-h)/(1+h);rho=2*h*h/(1-h*h)
cs=[h>0,h*h+2*h<=1,e>0,e<G,y>0,y<1,
    e>2*y/(1+y),u>1-y,u<e+h,u+d<=1+rho,
    d>0,d+e<G,l>0,l<=K*u,K*l<=d,
    z3.Or(l==K*u,K*l==d),
    E3>0,E3*(2*y)<(e-2*y/(1+y))*(1-y*y),
    (1+E3)*(1-y*y)<=1+y*y,2*y*(1+E3)<=1+y*y]
ss=z3.SolverFor("QF_NRA");ss.set(timeout=20000);ss.add(*cs)
ss.add((E3/(2-E3)+l/(2-l))**2>=e+u+d-1)
ans=ss.check();print("negative C Gamma via long-leg loss",ans,flush=True)
if ans==z3.sat:print(ss.model(),flush=True)
