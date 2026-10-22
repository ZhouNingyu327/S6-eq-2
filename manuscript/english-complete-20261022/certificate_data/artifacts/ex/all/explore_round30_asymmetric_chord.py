"""Probe the specific local asymmetric axis-chord lemma, not a cover model."""
import json
import z3


def main():
    mu,l,r,d,u,c,s=z3.Reals("mu l r d u c s")
    solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000)
    solver.add(mu>1,l>0,r>0,d>0,u>=z3.Q(1,2),l<mu,r<mu,
        c>=s,s>0,c*c+s*s==1,
        s*l<=c*d,c*r+s*u<=1,c*(l+r)<=1,l+r-d>mu)
    ans=solver.check()
    row={"lemma":"C h-d>mu forces u<1/2, second active down face",
         "result":str(ans)}
    if ans==z3.sat:
        row["model"]=str(solver.model())
    elif ans==z3.unknown:
        row["reason"]=solver.reason_unknown()
    print(json.dumps(row),flush=True)


if __name__=="__main__":
    main()
