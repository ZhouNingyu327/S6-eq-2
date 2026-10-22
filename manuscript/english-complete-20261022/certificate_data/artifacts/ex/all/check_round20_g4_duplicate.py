"""Exact scalar checks for G4 (3,2) with TL repeating C's left midpoint."""
from pathlib import Path
import json
import time
import sympy as sp
import z3


def query(name, premises, theory="QF_NRA"):
    solver=z3.SolverFor(theory)
    solver.set(timeout=20000)
    solver.add(*premises)
    start=time.perf_counter()
    answer=solver.check()
    row={"name":name,"theory":theory,"result":str(answer),
        "seconds":time.perf_counter()-start}
    if answer!=z3.unsat:
        row["detail"]=str(solver.model()) if answer==z3.sat else solver.reason_unknown()
    return row


def main():
    rows=[]
    x,y,r,u=z3.Reals("r20d_x r20d_y r20d_r r20d_u")
    rows.append(query("nonpositive F horizontal contradicts C exterior-midpoint ray bound",[
        x>0,y>0,x+y<1,r>1-x,u>1-y,r+u<1],"QF_LRA"))
    c,s,mu,h=z3.Reals("r20d_c r20d_s r20d_mu r20d_h")
    orientation=[c>0,s>0,c>=s,c*c+s*s==1,mu>1]
    rows.append(query("positive C orientation cannot reach forced upper ray",orientation+[
        u>z3.RealVal("11/15"),c*mu+s*u<=1]))
    rows.append(query("negative C orientation forces h < y/(2-y)",orientation+[
        y>0,15*y<4,u>1-y,s*mu+c*u<=1,h*(1+c)==s,
        (2-y)*h>=y]))
    RC=z3.Real("r20d_RC")
    rows.append(query("left midpoint and small rotation force RC < y^2",[
        mu>1,y>0,15*y<4,h>=0,(2-y)*h<y,
        (1-h*h)*(mu+RC)<=1+h*h,RC>=y*y]))

    t,L=z3.Reals("r20d_t r20d_L")
    corner=[t>0,t<1,L>1,L*L<=2,
        L*(1-t*t)<=1+t*t,2*t*L<=1+t*t]
    rows.append(query("kappa < t",corner+[L-1>=t*(3-L)]))
    rows.append(query("kappa < 1-t",corner+[L-1>=(1-t)*(3-L)]))
    delta=z3.Real("r20d_delta")
    den=(1-y*y)*(1-3*y*y)
    rows.append(query("top-meeting fourth-order delta < y^2",[
        y>0,15*y<4,delta*den==2*y**4,delta>=y*y]))
    rows.append(query("bottom meeting implies y+delta < x/2",[
        x>0,15*x<4,y>0,y*(1-2*x*x)<x*x,
        delta<y*y,2*(y+delta)>=x]))
    D=z3.Real("r20d_D")
    rows.append(query("bottom host short left leg contradicts left-edge coverage",[
        x>0,y+delta<x/2,D>1-y-delta,D<1-x],"QF_LRA"))
    b,alpha,beta=z3.Reals("r20d_b r20d_alpha r20d_beta")
    rows.append(query("F gap endpoints and axis connection violate parallel budget",[
        x>0,x<1,y>0,15*y<4,y<x,y<1-x,
        b*(1+x)>2*x,beta>1-x,alpha<y*y,
        b+beta-alpha<=1]))

    Y,H=sp.symbols("y h")
    k=Y**2/(1-2*Y**2)
    assert sp.cancel((1+k*k)/(1-k*k)-1
        -2*Y**4/((1-Y**2)*(1-3*Y**2)))==0
    assert sp.cancel(2*(Y/(2-Y))**2/(1-(Y/(2-Y))**2)
        -Y**2/(2*(1-Y)))==0
    assert sp.cancel(2*H*(1-H)/(1-H*H)-2*H/(1+H))==0
    constants={
        "sqrt(2)-1 < 11/15":sp.sqrt(2)-1<sp.Rational(11,15),
        "4/15 < 1/2":sp.Rational(4,15)<sp.Rational(1,2),
        "193/225 >5/6":sp.Rational(193,225)>sp.Rational(5,6),
        "34/75 <1/2":sp.Rational(34,75)<sp.Rational(1,2),
        "4/15 <1/3":sp.Rational(4,15)<sp.Rational(1,3),
    }
    assert all(constants.values())
    result={
        "scope":"G4 hosts top TR/right BR with TL also containing left midpoint: entire branch excluded",
        "status":"all exact checks passed" if all(row["result"]=="unsat" for row in rows) else "inspect",
        "queries":rows,"query_count":len(rows),
        "NRA_queries":sum(row["theory"]=="QF_NRA" for row in rows),
        "LRA_queries":sum(row["theory"]=="QF_LRA" for row in rows),
        "symbolic_identity_checks":3,
        "constant_checks":{key:bool(value) for key,value in constants.items()},
        "proof_method":"hand inequalities; C's real left midpoint simplifies the old double-meeting mechanism",
        "not_proved":"remaining G4 (3,2), other G3/G4; G2; S(6)=2",
        "no_search":"no covering search, angle samples, pose optimization or interval subdivision",
    }
    Path(__file__).with_name("round20_g4_duplicate_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)
    assert result["status"]=="all exact checks passed"


if __name__=="__main__":
    main()
