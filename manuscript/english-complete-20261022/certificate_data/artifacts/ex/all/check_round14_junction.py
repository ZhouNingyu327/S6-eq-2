"""Independent exact checks of the junction-forcing lemma and consequences."""
from pathlib import Path
import json,time,itertools
import sympy as sp
import z3

def solve(name,sol):
    sol.set(timeout=45000)
    start=time.time();ans=sol.check()
    row={'scope':name,'result':str(ans),'seconds':time.time()-start}
    assert ans==z3.unsat,row
    return row

def check_angle_order():
    x,L,y,N,T=z3.Reals('x L y N T')
    p=z3.SolverFor('QF_NRA')
    p.add(x>0,x<1,y>0,y<1,L>=1,N>=1,
          L*(1-x*x)<=1+x*x,2*x*L<=1+x*x,
          T*(1-y*y)==1+y*y-2*y*N,T>=0,L+T>=2,y>=x)
    return solve('right adjacent meeting forces t3<t2',p)

def check_sum():
    x,y,N,S=z3.Reals('x y N S')
    p=z3.SolverFor('QF_NRA')
    p.add(x>0,x<1,y>0,y<1,N>=1,S>=0,
          N+S+x+2*y-y*y<=2,x+y>=1)
    return solve('round13 adjacent budget forces t2+t3<1',p)

def check_mu_geometry():
    mu,R,q,N,T,U,V,X,Y=z3.Reals('mu R q N T U V X Y')
    p=z3.SolverFor('QF_NRA')
    p.add(mu>1,R>q,q>0,N>=mu,U>=0,V>=0,U+V<1,
          T+q*(N-V)==mu,T>V,R*U>=mu-T,
          Y==R*(X-mu+U),Y==mu-T-q*(mu-X),
          z3.Or(X<=mu-U,X>mu,Y<=0,Y>=mu-V))
    return solve('actual junction lies strictly right of qR and below qU inside target',p)

def check_reduced_hull():
    u,X,Y,X0,Y0=z3.Reals('u X Y X0 Y0')
    p=z3.SolverFor('QF_NRA')
    p.add(u>Y,Y>0,X>0,
          X0>0,Y0>0,X0<=X,Y0<=Y,
          z3.Or((u-Y0)*X<(u-Y)*X0))
    return solve('coordinate decrease keeps reduced point below upper hull edge',p)

def identities():
    x,y,N,mu=sp.symbols('x y N mu')
    c2,s2=(1-x*x)/(1+x*x),2*x/(1+x*x)
    c3,s3=(1-y*y)/(1+y*y),2*y/(1+y*y)
    R2,R3=s2/c2,s3/c3
    T=(1-s3*N)/c3
    D=(x-y)*(1+x*y)
    Y=2*x*y*(N-x-y)/D
    X=1-x+y*(1-x*x)*(N-x-y)/D
    assert sp.cancel(s2*X-c2*Y-(s2+c2-1))==0
    assert sp.cancel(s3*X-c3*Y-(s3-c3+c3*T))==0
    Xm=X+(mu-1)*(1+2/(R2-R3))
    Ym=Y+(mu-1)*(2*R2/(R2-R3)-1)
    assert sp.cancel(s2*Xm-c2*Ym-(mu*(s2+c2)-1))==0
    assert sp.cancel(s3*Xm-c3*Ym-(mu*(s3-c3)+c3*T))==0
    assert sp.cancel(sp.diff(Xm,mu)-(1+2/(R2-R3)))==0
    assert sp.cancel(sp.diff(Ym,mu)-(2*R2/(R2-R3)-1))==0
    # Parametric wedge points are outside both defining half planes.
    e=sp.symbols('e')
    wx,wy=Xm-e,Ym-e*(R2+R3)/2
    assert sp.cancel((s2*wx-c2*wy-(mu*(s2+c2)-1))/e-
                     c2*(R3-R2)/2)==0
    assert sp.cancel((s3*wx-c3*wy-(mu*(s3-c3)+c3*T))/e-
                     c3*(R2-R3)/2)==0
    # Unit-square area constraints for the two forced triangles.
    l,u,d=sp.symbols('l u d')
    assert sp.cancel(sp.det(sp.Matrix([[X+l,Y],[l,u]]))-(u*X+l*(u-Y)))==0
    assert sp.cancel(sp.det(sp.Matrix([[0,u+d],[X,Y+d]]))+X*(u+d))==0
    return {'scope':'junction coordinates, mu monotonicity, wedge exclusion and triangle areas',
            'result':'exact symbolic identities passed'}

if __name__=='__main__':
    rows=[]
    for f in [check_angle_order,check_sum,check_mu_geometry,check_reduced_hull,identities]:
        row=f();rows.append(row);print('PASS',row,flush=True)
    Path(__file__).with_name('round14_junction_checks.json').write_text(json.dumps(rows,indent=2),encoding='utf-8')
