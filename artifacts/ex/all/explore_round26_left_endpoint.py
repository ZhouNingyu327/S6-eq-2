import z3

h,x,y,z=z3.Reals("h x y z")
base=[h>0,h<z3.Q(5,12),x>0,x<1,y>0,y<z3.Q(4,15),z>0,z<1,
      y<x,y<1-x,
      y*(1-2*x*x)<x*x,
      y*(6*x-1-x*x)<(1-x)*(1-x)]
neg=base+[
    2*z*(1+h)+2*h*(1+z)<x*(1+h)*(1+z),
    2*h*(1-z)<y+(2-y)*h*h,
]
pos=base+[
    2*z<h*(1+z),
    2*h*(1-y)<z*(1-h*h)+2*h*h,
]
for name,cs in [("positive_direct_left",pos),("negative_direct_left",neg)]:
    q=z3.SolverFor("QF_NRA");q.set(timeout=20000);q.add(*cs)
    ans=q.check();print(name,ans)
    if ans==z3.sat:
        print(q.model())
