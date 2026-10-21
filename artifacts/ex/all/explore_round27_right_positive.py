import z3
h,y,e=z3.Reals("h y e")
k=2*h/(1-h*h)
cs=[h>0,h*h+2*h<=1,y>0,e>0,e<h,
    e>2*y/(1+y),e>2*h/(1+h)-y]
q=z3.SolverFor("QF_NRA");q.set(timeout=20000);q.add(*cs)
q.add(y*y/(1-2*y*y)+(k*(h-e))/(2-k*(h-e))>=e-y)
ans=q.check();print("positive C W-bridge feedback",ans,flush=True)
if ans==z3.sat:print(q.model())
x=z3.Real("x")
E=e-y
q2=z3.SolverFor("QF_NRA");q2.set(timeout=20000)
q2.add(*cs,x>0,x<1,(1+E)*(1-x*x)<=1+x*x,
       2*x*(1+E)<=1+x*x)
q2.add((1-x)/(1+x)-2*x*E/(1-x*x)+
       y*y/(1-2*y*y)+(k*(h-e))/(2-k*(h-e))>=z3.Q(7,12))
ans=q2.check();print("positive C bottom diameter feedback",ans,flush=True)
if ans==z3.sat:print(q2.model())
