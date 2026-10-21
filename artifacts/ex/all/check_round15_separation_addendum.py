"""Exact follow-on checks; separate from the frozen round-15 proof ZIP."""
from pathlib import Path
import json,time
import sympy as s
import z3

x=s.symbols('x')
Kc=x*x/(1-2*x*x)
Ks=(1-x)**2/(6*x-1-x*x)
assert s.cancel(s.diff(x-Kc,x,2)+2*(1+6*x*x)/(1-2*x*x)**3)==0
assert (x-Kc).subs(x,s.Rational(3,14))==s.Rational(102,623)>s.Rational(3,20)
assert (x-Kc).subs(x,s.Rational(5,12))==s.Rational(85,564)>s.Rational(3,20)
assert (x-Ks).subs(x,s.Rational(5,12))==s.Rational(367,2292)>s.Rational(3,20)
assert s.cancel(s.diff(Ks,x,2)-8*(x**3-3*x+6)/(6*x-1-x*x)**3)==0
assert (x+Kc).subs(x,s.Rational(5,12))==s.Rational(385,564)<s.Rational(3,4)
assert (x+Ks).subs(x,s.Rational(5,12))==s.Rational(1543,2292)<s.Rational(3,4)
assert (x+Ks).subs(x,s.Rational(5,7))==s.Rational(177,238)<s.Rational(3,4)

rows=[]
def check(name,p):
    p.set(timeout=45000);start=time.time();ans=p.check()
    row={'scope':name,'result':str(ans),'seconds':time.time()-start}
    if ans==z3.unknown:row['reason']=p.reason_unknown()
    if ans==z3.sat:row['model']=str(p.model())
    rows.append(row);print(row,flush=True)
    assert ans==z3.unsat,row

for name,violation in [('angle separation',lambda x,y:x-y<=z3.RealVal('3/20')),
                       ('angle sum',lambda x,y:x+y>=z3.RealVal('3/4'))]:
    xx,yy=z3.Reals('x y')
    p=z3.SolverFor('QF_NRA')
    p.add(xx>=z3.RealVal('3/14'),xx<=z3.RealVal('5/7'),yy>=0,
          yy*(6*xx-1-xx*xx)<=(1-xx)*(1-xx),
          z3.Implies(xx<=z3.RealVal('5/12'),yy*(1-2*xx*xx)<=xx*xx),
          violation(xx,yy))
    check(name,p)

for name,violation in [
    ('junction horizontal separation',lambda x,y,dx,dy:dx<=z3.RealVal('9/2000')),
    ('junction vertical separation',lambda x,y,dx,dy:dy<=z3.RealVal('21/1600')),
]:
    xx,yy=z3.Reals('x y');den=(xx-yy)*(1+xx*yy)
    dx=yy*(1-xx*xx)*(1-xx-yy)/den
    dy=2*xx*yy*(1-xx-yy)/den
    p=z3.SolverFor('QF_NRA')
    p.add(xx>z3.RealVal('3/14'),xx<z3.RealVal('5/7'),
          yy>z3.RealVal('1/32'),yy<z3.RealVal('4/15'),
          xx-yy>z3.RealVal('3/20'),xx+yy<z3.RealVal('3/4'),
          violation(xx,yy,dx,dy))
    check(name,p)

result={'classification':'exact supplementary consequences, independently checked but outside frozen round-15 ZIP',
        'proved_scope':'t2-t3>3/20, t2+t3<3/4; Q0_x-(1-t2)>9/2000 and Q0_y>21/1600',
        'queries':rows,'unsat_count':4,'symbolic_identities_and_endpoint_values':'passed'}
Path(__file__).with_name('round15_separation_addendum_checks.json').write_text(
    json.dumps(result,indent=2),encoding='utf-8')
