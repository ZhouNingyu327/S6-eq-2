"""Exact algebraic reductions for all G1 adjacent-two-meet representatives."""
from pathlib import Path
import json,time
import sympy as sp
import z3

def result(sol,scope,nonlinear=False):
    sol.set(timeout=60000);start=time.time();res=sol.check();assert res==z3.unsat,(scope,res)
    return {'scope':scope,'result':str(res),
            'arithmetic':'exact nonlinear reals' if nonlinear else 'exact linear reals',
            'seconds':time.time()-start}

def basic():
    mu=z3.Real('mu');L=z3.Reals('L1 L2 L3 L4');S=z3.Reals('S1 S2 S3 S4');U=z3.Reals('U1 U2 U3 U4')
    sol=z3.SolverFor('QF_LRA');sol.add(mu>1)
    for i in range(4):sol.add(L[i]>=mu,S[i]>=0,U[i]>=0,L[i]+S[i]+U[i]<2,S[i]+U[i]<1)
    for i in [1,2]:sol.add(L[i]+S[i+1]>=2*mu)
    return sol,mu,L,S,U

def chain():
    sol,mu,L,S,U=basic()
    sol.add(S[1]+U[1]+U[2]+U[3]>=1-2*(2*mu-2))
    return result(sol,'right/top meets imply S2+U2+U3+U4<1-2eta')

def central_bottom():
    sol,mu,L,S,U=basic();B=z3.Real('B');sol.add(B<1)
    g=2*mu-L[0]-S[1]
    sol.add(g+mu-U[1]<=B,S[0]+U[2]>2*mu-1)
    return result(sol,'C owns bottom gap and F left gap: parallel sections contradict F left/up diameter')

def lower_tip():
    mu,U1,U3,S1=z3.Reals('mu U1 U3 S1');sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,U1>=0,U3>=0,U3<z3.RealVal('4/15'),S1+U1<1,S1+U3>2*mu-1,
            2*mu-U1-U3<=z3.RealVal('22/15'))
    return result(sol,'C owns left gap: opposite up/down tips have span >22/15>sqrt2, so lower tip belongs F')

def right_tip():
    sol,mu,L,S,U=basic();r,u=z3.Reals('r u')
    sol.add(r>=mu-U[1],u>=mu-U[2],r+u<1)
    return result(sol,'C left/lower outer contact cannot include right and upper middle tips; right tip belongs F')

def orientation():
    c,s,mu,T=z3.Reals('c s mu T');sol=z3.SolverFor('QF_NRA')
    sol.add(c>=s,s>=0,c*c+s*s==1,mu>1,T>=z3.RealVal('11/15'),c*mu+s*T<=1)
    return result(sol,'C left gap and upper tip force c<s; axis-aligned and c>=s cases excluded',True)

def calibration():
    k,h,z=sp.symbols('k h z')
    f=(1+h*h)/(1-h*h)+h
    E=4*z*z/(1-z*z)
    bound=1+k/(2-k)+k*k/(2*(1-k))
    poly=sp.Poly(sp.cancel((f+E-bound)*2*(1-k)*(2-k)*(1-h*h)*(1-z*z)),k,h,z)
    zk,zh,zz=z3.Reals('k h z');zvars=[zk,zh,zz]
    value=z3.RealVal(0)
    for powers,a in poly.terms():
        term=z3.RealVal(str(a))
        for v,n in zip(zvars,powers):
            if n:
                term*=v**n
        value+=term
    sol=z3.SolverFor('QF_NRA')
    sol.add(zk>0,zk<z3.RealVal('4/15'),zh>=0,zh<1,zz>=0,zz<1,
            zz*(2-zk)<=zk,zh*(2-zk+(4-zk)*zz)<=zk-(2-zk)*zz,value>0)
    return result(sol,'universal calibrated L1+h+central orientation excess <=1+k/(2-k)+k^2/[2(1-k)]',True)

def final_case():
    mu,V,R,phi=z3.Reals('mu V R phi');sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,phi>0,V+R<2-phi-(2*mu-2),4*mu<=2+V+R)
    return result(sol,'C owns left gap, F bottom: calibrated envelope makes southeast perimeter impossible')

def opposite():
    mu,B,g1,g3,hC,hF=z3.Reals('mu B g1 g3 hC hF')
    L=z3.Reals('L1 L2 L3 L4');S=z3.Reals('S1 S2 S3 S4');U=z3.Reals('U1 U2 U3 U4')
    sol=z3.SolverFor('QF_LRA');sol.add(mu>1,B<1,g1>0,g3>0,hC>=0,hF>=0)
    for i in range(4):sol.add(L[i]>=mu,S[i]>=0,U[i]>=0,L[i]+S[i]+U[i]<2)
    sol.add(L[1]+S[2]>=2*mu,L[3]+S[0]>=2*mu,
            g1==2*mu-L[0]-S[1],g3==2*mu-L[2]-S[3],
            hC+g1<=B,hF+g3<=B,hC+hF+U[1]+U[3]>=2*mu)
    return result(sol,'opposite two meets: outer gaps and full floating central sections contradict corner budgets')

if __name__=='__main__':
    rows=[chain(),central_bottom(),lower_tip(),right_tip(),orientation(),calibration(),final_case(),opposite()]
    for row in rows:print('PASS',row,flush=True)
    Path(__file__).with_name('round10_adjacent_checks.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
