"""Counterexample probe for a stated endpoint relaxation, not a cover search."""
import json
import time
import z3


def main():
    h,E,l,r,d,T,S1,S2=z3.Reals("h E l r d T S1 S2")
    q=lambda x:x/(2-x)
    G=(1-h)/(1+h);K=2*h/(1-h*h)
    common=[h>0,h*h+2*h<=1,E>=0,209*E<32,
        T>=0,T*T==E*(2+E),l>0,r>0,d>0,l+E<G,r<h+E,l+r<1,
        d<=K*r,d<=l/K,S1>=0,S2>=0,S1<q(l),
        S1<l+(1+E)*(1-T)-1,S1+S2>(1-d)*(1-d),12*(S1+S2)>7]
    cases={
        "direct":common+[S2<q(r)],
        "bridge":common+[1-G+l-q(r)>0,S2<(G-l+q(r))/(2-G+l-q(r))],
    }
    for name,cs in cases.items():
        solver=z3.SolverFor("QF_NRA");solver.set(timeout=20000);solver.add(*cs)
        start=time.perf_counter();ans=solver.check()
        result={"case":name,"result":str(ans),"seconds":time.perf_counter()-start,
                "scope":"relaxed endpoint inequalities only, not a six-square configuration"}
        if ans==z3.sat:
            result["model"]={str(v):str(solver.model().eval(v)) for v in [h,E,l,r,d,T,S1,S2]}
        if ans==z3.unknown:
            result["reason"]=solver.reason_unknown()
        print(json.dumps(result),flush=True)


if __name__=="__main__":
    main()
