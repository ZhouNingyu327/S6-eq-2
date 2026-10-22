"""A single local adjacent-corner lemma probe, not a cover optimizer."""
import json
import time
import z3


def main():
    x,t,L,D=z3.Reals("x t L D")
    k=lambda y:2*y/(1-y*y)
    b=lambda y:(1+y*y)/(1-y*y)
    common=[x>0,x<1,t>0,t*t+2*t<=1,L>=1,
        L*(1-x*x)<=1+x*x,2*x*L<=1+x*x,
        D>=z3.Q(23,24),D<=1,L+b(t)-k(t)*D>=2]
    for factor in [0,2]:
        solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000)
        solver.add(*common,D+b(x)-k(x)*L+x+2*t-t*t>2+factor*(1-D))
        start=time.perf_counter();ans=solver.check()
        row={"factor":factor,"result":str(ans),"seconds":time.perf_counter()-start}
        if ans==z3.sat:
            row["model"]=str(solver.model())
        elif ans==z3.unknown:
            row["reason"]=solver.reason_unknown()
        print(json.dumps(row),flush=True)


if __name__=="__main__":
    main()
