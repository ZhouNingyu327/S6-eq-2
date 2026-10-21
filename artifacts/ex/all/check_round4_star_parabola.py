"""Exact checks of full horizontal chord plus upward ray bounds."""
from pathlib import Path
import json,time
import z3


def star_solver():
    sol=z3.SolverFor('QF_NRA');sol.set(timeout=60000)
    p,q,l,r,u=z3.Reals('p q l r u')
    sol.add(p>=0,q>=0,l>=0,r>=0,u>=0,p*p+q*q==1,
            p*(l+r)<=1,q*(l+r)<=1,p*l+q*u<=1,q*r+p*u<=1)
    return sol,p,q,l,r,u


def parabolic():
    sol,p,q,l,r,u=star_solver();sol.add(l+r+u*u>2)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'unit centre tile full horizontal chord H and upward ray U: H+U^2<=2',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def sharp_linear():
    sol,p,q,l,r,u=star_solver();d=z3.Real('sqrt2')
    sol.add(d>0,d*d==2,d*(l+r+u)>3)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'unit centre tile H+U<=3/sqrt(2)',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


def sharp_weighted():
    sol,p,q,l,r,u=star_solver();d=z3.Real('sqrt2')
    sol.add(d>0,d*d==2,l+u+(2*d-2)*r>2)
    start=time.time();res=sol.check();assert res==z3.unsat,res
    return {'scope':'unit three rays l+u+(2*sqrt(2)-2)*r<=2, sharp coefficient',
            'result':str(res),'arithmetic':'exact nonlinear reals','seconds':time.time()-start}


if __name__=='__main__':
    records=[parabolic(),sharp_linear(),sharp_weighted()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_star_parabola_checks.json').write_text(json.dumps(records,indent=2))
