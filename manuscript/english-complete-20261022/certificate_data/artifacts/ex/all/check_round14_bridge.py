"""Exact checks of forced horizontal bridging, J=0, and left-gap ownership."""
from pathlib import Path
import json,time
import sympy as sp
import z3

def solve(name,p):
    p.set(timeout=30000);start=time.time();ans=p.check()
    row={'scope':name,'result':str(ans),'seconds':time.time()-start}
    assert ans==z3.unsat,row
    return row

def no_left_tip():
    x,k,w,S,l,r,u=z3.Reals('x k w S l r u')
    p=z3.SolverFor('QF_NRA')
    p.add(x>0,x<1,k>0,k<z3.RealVal('4/15'),w>=0,S>=0,
          1-S-x-2*k+k*k-w>0,l>=1-w,r>=1-x,u>=1-k,l+r+u*u<=2)
    return solve('C cannot contain the left anchored inner tip',p)

def A_bridge():
    mu,c,s,z,A,D,U=z3.Reals('mu c s z A D U')
    p=z3.SolverFor('QF_NRA')
    p.add(mu>1,c>0,s>0,s*z==1-c,s*A+c*D==1,
          c*(mu-D)<=s*U,A>=z+U)
    return solve('W contains left inner tip implies A<z+U4',p)

def left_length():
    mu,z,c,s,l=z3.Reals('mu z c s l')
    p=z3.SolverFor('QF_NRA')
    p.add(mu>1,z>0,z<1,c*(1+z*z)==1-z*z,s*(1+z*z)==2*z,
          c*l>=mu*c-1+mu*s,l*(1+z)<=2*z)
    return solve('forced W inner endpoint gives C left ray >2z/(1+z)',p)

def J_condition():
    mu,z,c,s,D,U,K=z3.Reals('mu z c s D U K')
    p=z3.SolverFor('QF_NRA')
    p.add(mu>1,z>0,z<1,c*(1+z*z)==1-z*z,s*(1+z*z)==2*z,
          c*(mu-D)<=s*U,U>=0,2*U<=(1-z)*(1-z),K*c*s==c+s-mu,K>D)
    return solve('W bridge and 2U4<=(1-z)^2 force J=0',p)

def angle_budget():
    x,L,y,N,T,z,k=z3.Reals('x L y N T z k')
    p=z3.SolverFor('QF_NRA')
    p.add(x>0,x<1,y>0,y<x,y<z3.RealVal('4/15'),z>0,z<1,
          L>=1,N>=1,L*(1-x*x)<=1+x*x,2*x*L<=1+x*x,
          N*(1-y*y)<=1+y*y,2*y*N<=1+y*y,
          T*(1-y*y)==1+y*y-2*y*N,T>=0,L+T>=2,
          k*(3-N)==N-1,k>=0,k<z3.RealVal('4/15'),
          (2*z+(1-x)*(1+z))*(1-y)<=1+z,2*k>(1-z)*(1-z))
    return solve('full physical adjacent domain and C triangle force 2kappa3<=(1-z)^2',p)

def left_gap_owner():
    mu,x,y,r,u=z3.Reals('mu x y r u')
    p=z3.SolverFor('QF_LRA')
    p.add(mu>1,x+y<1,r>=mu-x,u>=mu-y,r+u<1)
    return solve('C cannot contain a left-lower outer point; left gap would belong to F',p)

def identities():
    z,U=sp.symbols('z U');c=(1-z*z)/(1+z*z);s=2*z/(1+z*z)
    K=(c+s-1)/(c*s)
    assert sp.cancel(K-(1+z*z)/(1+z))==0
    assert sp.cancel(1-(1-s)/c-2*z/(1+z))==0
    assert sp.cancel(K-1+(s/c)*U-(s/c)*(U-(1-z)**2/2))==0
    return {'scope':'bridge endpoint and vertical-trace identities','result':'exact identities passed'}

if __name__=='__main__':
    rows=[]
    for f in [no_left_tip,A_bridge,left_length,J_condition,angle_budget,left_gap_owner,identities]:
        row=f();rows.append(row);print('PASS',row,flush=True)
    Path(__file__).with_name('round14_bridge_checks.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
