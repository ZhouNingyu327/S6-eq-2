"""Small exact counterexample queries for the hand-derived angle theorem."""
from pathlib import Path
import json,time
import z3

ROOT=Path(__file__).resolve().parent
rows=[]
def check(name,p):
    p.set(timeout=45000)
    start=time.time();result=p.check()
    row={'scope':name,'result':str(result),'seconds':time.time()-start}
    if result==z3.unknown:row['reason']=p.reason_unknown()
    if result==z3.sat:row['model']=str(p.model())
    rows.append(row);print(row,flush=True)
    assert result==z3.unsat, row

x,y,E,k,S,z,r,g,v=z3.Reals('x y E k S z rho g v')
p=z3.SolverFor('QF_NRA')
p.add(x>0,x<1,y>0,y<z3.RealVal('4/15'),E>=0,k>=0,k<=E,S>=0,
      E+S+x+2*y-y*y<=1,r>=0,r<=z3.RealVal('5/12'),
      z>0,z<1,z+2*r<=x,g>2-z-k-S,v>1-y-r,g+v*v<=2)
check('F three-ray budget forces z+2rho>x',p)

x,r,z=z3.Reals('x rho z')
p=z3.SolverFor('QF_NRA')
p.add(x>0,x<1,r>=0,5*r<=x*(1-x),z>=0,z<1,
      2*z<=(x+r)*(1+z),z+2*r>=x)
check('horizontal span forbids rho<=x(1-x)/5',p)

x,y,r=z3.Reals('x y rho')
p=z3.SolverFor('QF_NRA')
p.add(x>0,x<=z3.RealVal('3/14'),y>=0,y*(1-2*x*x)<=x*x,
      r>=x*(1-x)/5,r<=z3.RealVal('5/12'),
      (1-y)*(1-y)*r*(2+r)<=(x+r)*(x+r))
check('small t2 contradicts right/up projection',p)

x,y,Y,l=z3.Reals('x y Y l')
p=z3.SolverFor('QF_NRA')
p.add(x>=z3.RealVal('1/2'),x<1,Y*(6*x-1-x*x)==(1-x)*(1-x),
      y>=0,y<=Y,l>=0,(l+1-x)*(1-y)<=1,l>=1-y)
check('large t2 forces left helper below up helper',p)

r,q,l=z3.Reals('rho q l')
p=z3.SolverFor('QF_NRA')
p.add(r>=z3.RealVal('1/6'),r<=z3.RealVal('5/12'),q>=0,q*q==r*(2+r),
      l>=z3.RealVal('13228/22063'),l+q*z3.RealVal('46/47')<=1+r)
check('large t2 and rho>=1/6 contradict left/up projection',p)

x,z,r,q,l=z3.Reals('x z rho q l')
p=z3.SolverFor('QF_NRA')
p.add(x>=z3.RealVal('3/4'),x<1,r>=x*(1-x)/5,r<=z3.RealVal('1/6'),
      q>=0,q*q==r*(2+r),z>0,z<1,z+2*r>x,l*(1+z)==2*z,
      l+q*z3.RealVal('46/47')<=1+r)
check('large t2 and rho<=1/6 contradict left/up projection',p)

x,r=z3.Reals('x rho')
p=z3.SolverFor('QF_NRA')
p.add(x>z3.RealVal('3/14'),x<z3.RealVal('3/4'),
      5*r>x*(1-x),r<=z3.RealVal('33/980'))
check('angle interval forces uniform rho>33/980',p)

result={'classification':'exact nonlinear real counterexample checks',
        'queries':rows,'unsat_count':len(rows),'passed':True}
(ROOT/'round15_rotation_checks.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
