"""A deliberately relaxed scalar bridge inequality, not a full-layout search."""
import json
import time
import z3


def main():
    a,eta,u,z,v,K,rho=z3.Reals("a eta u z v K rho")
    domains=[eta>0,eta*eta+2*eta<=1,u>0,2*u<1,z>0,
             111*z<29,K*(1-eta*eta)==2*eta,K>0,K<=1]
    for label,sign in [
        ("nonpositive w",[u<=eta,5*z<8*K*u]),
        ("positive w",[u==eta+v*v,v>0,5*z<8*K*u-10*v])]:
        sol=z3.SolverFor("QF_NRA");sol.set(timeout=45000)
        sol.add(*domains,*sign,z+u/(2-u)>=2*eta/(1+eta))
        start=time.perf_counter();ans=sol.check()
        row={"name":label,"result":str(ans),"seconds":time.perf_counter()-start}
        if ans==z3.sat:row["model"]=str(sol.model())
        if ans==z3.unknown:row["reason"]=sol.reason_unknown()
        print(json.dumps(row),flush=True)


if __name__=="__main__":
    main()
