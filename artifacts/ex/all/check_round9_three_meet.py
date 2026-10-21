"""Exact checks of the G1 three-meet proof's algebraic reductions."""
from pathlib import Path
import json,time,z3

def result(sol,scope,nonlinear=False):
    sol.set(timeout=60000);start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':scope,'result':str(res),
            'arithmetic':'exact nonlinear reals' if nonlinear else 'exact linear reals',
            'seconds':time.time()-start}

def two_rays():
    c,s,x1,x2,y1,y2=z3.Reals('c s x1 x2 y1 y2');sol=z3.SolverFor('QF_NRA')
    sol.add(c>0,s>0,c*c+s*s==1,x1>=0,y1>=0,x2>=x1,y2>=y1,
            c*(x2-x1)<=1,s*(y2-y1)<=1,c*x2-s*y1<=1,s*y2-c*x1<=1,
            s*x2+c*y2<=1,(x2-x1)+(y2-y1)>2)
    return result(sol,'unit-square sections on two orthogonal positive rays have total length <=2',True)

def span():
    mu,L,S,U=z3.Reals('mu L S U');sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,L<z3.RealVal('3/2'),L+S>=2*mu,S+U<1,2*mu-U<=z3.RealVal('3/2'))
    return result(sol,'previous meet forces opposite midpoint-tip vertical/horizontal span >3/2>sqrt2')

def forced_midpoint():
    c,s,d,mu,T=z3.Reals('c s d mu T');sol=z3.SolverFor('QF_NRA')
    sol.add(c>=0,s>=0,c*c+s*s==1,d>=0,mu>1,T>=mu,
            c*d+s*T<=1,s*d>c*mu)
    return result(sol,'unit containing (-d,0) and (0,T>=mu>1) must also contain (0,mu)',True)

def chain():
    mu=z3.Real('mu');L=z3.Reals('L1 L2 L3 L4');S=z3.Reals('S1 S2 S3 S4');U=z3.Reals('U1 U2 U3 U4')
    sol=z3.SolverFor('QF_LRA');sol.add(mu>1)
    for i in range(4):sol.add(L[i]+S[i]+U[i]<2,S[i]>=0,U[i]>=0,S[i]+U[i]<1)
    for i in [1,2,3]:sol.add(L[i]+S[(i+1)%4]>=2*mu)
    sol.add(S[1]+U[3]>=1)
    return result(sol,'three meets force S2+U4<1, excluding the gap owner from the left middle tip')

def quarter(j):
    mu,R=z3.Reals('mu R');L=z3.Reals('L1 L2 L3 L4');S=z3.Reals('S1 S2 S3 S4');U=z3.Reals('U1 U2 U3 U4')
    sol=z3.SolverFor('QF_LRA');sol.add(mu>1,R>=0)
    for i in range(4):sol.add(L[i]+S[i]+U[i]<2,S[i]>=0,U[i]>=0)
    for i in [1,2,3]:sol.add(L[i]+S[(i+1)%4]>=2*mu)
    V=L[0]+S[1]+U[0]+U[1]
    if j is None:
        sol.add(4*mu<=V+2)
        name='central gap owner: other extra absent from the southeast quarter; perimeter contradiction'
    else:
        deficit=2-L[j]-S[j]-U[j]
        sol.add(R<=U[2]+U[3]-(2*mu-2)+deficit,4*mu<=V+2+R)
        name='noncentral gap owner: central SE rays charged to corner V'+str(j+1)+' deficit; perimeter contradiction'
    return result(sol,name)

if __name__=='__main__':
    rows=[two_rays(),forced_midpoint(),span(),chain(),quarter(None),quarter(2),quarter(3)]
    for row in rows:print('PASS',row,flush=True)
    Path(__file__).with_name('round9_three_meet_checks.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
