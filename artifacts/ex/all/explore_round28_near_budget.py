"""Small continuous lemma candidates, not six-square layout searches."""
import z3
h,w,d,l,t=z3.Reals("h w d l t")
K=2*h/(1-h*h);G=(1-h)/(1+h);H=h*G
N=w-d-H
base=[h>0,h*h+2*h<=1,w>0,w*w+2*w<=1,d>0,N>0,w+d<G,
      l>0,l<1,l<=K*(w+h),K*l<=d,
      z3.Or(l==K*(w+h),K*l==d),t>0]
for label,short,extra in [
    ("sqrt loss",1-t,[t*t==w]),
    ("exact max short",(1+w)*(1-t),[t*t==w*(2+w)])]:
    q=z3.SolverFor("QF_NRA");q.set(timeout=20000)
    q.add(*base,*extra,short+N/(2-N)+l/(2-l)>=(1-d)*(1-d))
    ans=q.check();print(label,ans,flush=True)
    if ans==z3.sat:print(q.model(),flush=True)
