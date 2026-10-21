"""One explicit relaxed negative-C scalar lemma, never a layout proof."""
from pathlib import Path
import json
import sympy as sp
import z3
def main():
 a,z,e=sp.symbols("a z e")
 K=2*e/(1-e*e);delta=2*e*e/(1-e*e)
 b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);G=(1-z)/(1+z)
 F=b-k*(2-G);ra=a+delta;rr=1-K*(1-z-e)
 q=lambda v:v/(2-v)
 budget=[sp.Rational(7,12),(1-z-delta)**2,2-1/(1-z-delta)]
 vv=z3.Reals("a z e");mp=dict(zip((a,z,e),vv))
 def conv(expr):
  if expr.is_Number:return z3.RealVal(str(expr))
  if expr.is_Symbol:return mp[expr]
  if expr.is_Add:return sum(conv(x) for x in expr.args)
  if expr.is_Mul:
   ans=z3.RealVal(1)
   for x in expr.args:ans*=conv(x)
   return ans
  if expr.is_Pow:return conv(expr.base)**int(expr.exp)
  raise ValueError(expr)
 checks=[("F positive",F),("actual LEFT cosine cap",b-(2-G)),
         ("negative C L/T",z-K*(1-a-e)),("right cap positive",rr)]
 for j,lower in enumerate(budget):
  checks.extend([(f"a root budget {j}",F+q(ra)-lower),
                 (f"R/T root budget {j}",F+q(rr)-lower)])
 sol=z3.SolverFor("QF_NRA");sol.set(timeout=8000)
 aa,zz,ee=vv
 sol.add(aa>0,aa<1,zz>0,zz<z3.Q(4,15),zz<aa,aa+2*zz<1,
         ee>=z3.Q(1,8),ee*ee+2*ee-1<=0)
 for _,expr in checks:
  num,den=sp.cancel(expr).as_numer_denom()
  sol.add(conv(num)*conv(den)>0)
 ans=sol.check()
 result={"result":str(ans),"scope":"relaxed scalar necessary conditions for negative-C double direct; no complete square placement or coverage",
         "checks":[n for n,_ in checks],"timeout_ms":8000}
 if ans==z3.sat:
  model=sol.model();result["rational_model"]={str(x):str(model.eval(x,model_completion=True)) for x in vv}
  result["model_is_covering"]=False
 if ans==z3.unknown:result["reason"]=sol.reason_unknown()
 Path("work/round46_negative_scalar_exploration.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2),flush=True)
if __name__=="__main__":main()
