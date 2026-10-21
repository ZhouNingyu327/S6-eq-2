import z3
h,e,y,l,d,u,x,E2,E3=z3.Reals("h e y l d u x E2 E3")
k=2*h/(1-h*h);rho=2*h*h/(1-h*h);G=(1-h)/(1+h)
ky=2*y/(1-y*y);by=2*y/(1+y)
cs=[h>0,h*h+2*h<=1,y>0,y<1,e>by,e<G,
    l>0,d>0,u>1-y,e+u>1,u<e+h,
    l<rho+k*e,k*l+e<G,d+e<G,u+d<1+rho,k*l<=d,
    E2>0,E2>e+u+d-1,
    x>0,x<1,(1+E2)*(1-x*x)<=1+x*x,2*x*(1+E2)<=1+x*x,
    E3>0,E3<(e-by)/ky,
    (1+E3)*(1-y*y)<=1+y*y,2*y*(1+E3)<=1+y*y]
Sigma=(1-x)/(1+x)-2*x*E2/(1-x*x)+E3/(2-E3)+l/(2-l)
for name,condition in [("F positive H candidate",Sigma>=1),
                       ("F empty H root candidate",Sigma>=(1-d)*(1-d))]:
    ss=z3.SolverFor("QF_NRA");ss.set(timeout=20000);ss.add(*cs)
    if "empty" in name:
        r=z3.Real("r")
        ss.add(r>1-x,r+l<1+rho,r+k*u<=1+rho)
    ss.add(condition)
    ans=ss.check();print(name,ans,flush=True)
    if ans==z3.sat:print(ss.model(),flush=True)
