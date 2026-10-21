"""Exact continuous corner cascade bounds; no angle samples."""
from pathlib import Path
import json,time
import z3


def run(sol,scope):
    sol.set(timeout=60000);start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':scope,'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def k_small():
    L,k,d=z3.Reals('L k sqrt2');sol=z3.SolverFor('QF_NRA')
    sol.add(d>0,d*d==2,L>1,L<=d,k*(3-L)==L-1,k>=z3.RealVal('4/15'))
    return run(sol,'k=(L2-1)/(3-L2) lies strictly between 0 and 4/15')


def t3_small():
    L,k,t,S=z3.Reals('L k t3 S3');sol=z3.SolverFor('QF_NRA')
    sol.add(L>1,L<3,k*(3-L)==L-1,t>0,t<1,S>=0,
            S*(1+t)<=1-t,L+S>2,t>=k)
    return run(sol,'right corner meet forces t3<k')


def t4_small():
    k,t3,t4,L3,S4,w=z3.Reals('k t3 t4 L3 S4 w');sol=z3.SolverFor('QF_NRA')
    sol.add(k>0,k<z3.RealVal('4/15'),t3>0,t3<k,t4>0,t4<1,L3>1,S4>=0,
            L3*(1-t3*t3)<=1+t3*t3,L3+S4>2,S4*(1+t4)<=1-t4,
            w*(1-2*k*k)==k*k,t4>=w)
    return run(sol,'top corner meet forces t4<k^2/(1-2k^2)')


def cap_cosine():
    L,t,k,K=z3.Reals('L t k Kc');sol=z3.SolverFor('QF_NRA')
    sol.add(L>1,L<3,t>0,t<=z3.RealVal('5/12'),L*(1-t*t)<=1+t*t,
            k*(3-L)==L-1,K*(1-2*t*t)==t*t,k>K)
    return run(sol,'cosine long-leg bound gives k<=t^2/(1-2t^2) on t<=5/12')


def cap_sine():
    L,t,k,K=z3.Reals('L t k Ks');sol=z3.SolverFor('QF_NRA')
    sol.add(L>1,L<3,t>=z3.RealVal('2/5'),t<1,2*t*L<=1+t*t,
            k*(3-L)==L-1,K*(6*t-1-t*t)==(1-t)*(1-t),k>K)
    return run(sol,'sine long-leg bound gives k<=(1-t)^2/(6t-1-t^2) on t>=2/5')


if __name__=='__main__':
    records=[k_small(),t3_small(),t4_small(),cap_cosine(),cap_sine()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round5_cascade_checks.json').write_text(json.dumps(records,indent=2))
