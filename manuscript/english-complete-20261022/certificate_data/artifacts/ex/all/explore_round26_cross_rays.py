import z3
from itertools import combinations

h,x,y,T,l,r,u,d=z3.Reals("h x y T l r u d")
base=[h>0,h*h+2*h<=1,x>0,x<1,y>0,y<z3.Q(4,15),
      y<x,y<1-x,y*(1-2*x*x)<x*x,
      y*(6*x-1-x*x)<(1-x)*(1-x),
      T>0,l>0,r>1-x,u>1-y,d>0,r+d<1,
      (l+r+T)*(1-y*y)<1+y*y,
      l+d>=1]
points=[(0,0),(r,0),(-l,0),(0,u),(0,-d),(-T,1)]
for sign in [1,-1]:
    cs=list(base)
    for a,b in combinations(points,2):
        dx,dy=a[0]-b[0],a[1]-b[1]
        for val in [(1-h*h)*dx+sign*2*h*dy,-sign*2*h*dx+(1-h*h)*dy]:
            cs.extend([val<=1+h*h,val>=-1-h*h])
    q=z3.SolverFor("QF_NRA");q.set(timeout=20000);q.add(*cs)
    ans=q.check();print(sign,ans,flush=True)
    if ans==z3.sat:print(q.model(),flush=True)
