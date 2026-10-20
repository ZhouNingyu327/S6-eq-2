"""Exact algebra for the original W's TOP/H obstruction; no solver or sampling."""
from pathlib import Path
import sympy as s,json
R=s.Rational
def main():
 t,z,h,w,a,mu,xi,DD=s.symbols('t z h w a mu xi DD',real=True)
 b=lambda v:(1+v*v)/(1-v*v);k=lambda v:2*v/(1-v*v)
 g=lambda v:(1-v)/(1+v);q=lambda v:v/(2-v)
 c=(1-t*t)/(1+t*t);ss=2*t/(1+t*t)
 delta=lambda v:2*v*v/(1-v*v)
 RT=h+z/k(h);F=b(a)-k(a)*(2-g(z))
 V=s.sqrt(w*(2+w));Phi=(1+w)*(1-V)
 M=R(23,7)*delta(z)
 ids={
  'unit normals':c*c+ss*ss-1,
  'parallel chord limit':(c+ss-1)/(c*ss)-(1+t*t)/(1+t),
  'parallel chord loss':1-(1+t*t)/(1+t)-t*g(t),
  'loss increasing on small-angle domain':s.diff(t*g(t),t)-(1-2*t-t*t)/(1+t)**2,
  'q increasing':s.diff(q(w),w)-2/(2-w)**2,
  'RT h convex':s.diff(RT,h,2)-z/h**3,
  'small W orientation left bound':mu-DD+(1-c*mu)/ss-(mu-DD+t-c*(mu-1)/ss),
  'small W orientation right bound':mu-(1-c*mu)/ss-(1-t+(mu-1)*(1+c/ss)),
  'bridge surplus coefficient':2+R(9,7)-R(23,7),
  'delta derivative':s.diff(delta(z),z)-4*z/(1-z*z)**2,
  'delta derivative increasing':s.diff(delta(z),z,2)-4*(1+3*z*z)/(1-z*z)**3,
  'Phi derivative':s.diff(Phi,w)-(1-2*V-1/V),
  'w derivative':s.diff(2*z/(1+z),z)-2/(1+z)**2,
  'q M derivative':s.diff(q(M),z)-2/(2-M)**2*R(23,7)*4*z/(1-z*z)**2,
  'F a upper endpoint':F.subs({a:R(3,5),z:R(1,10)})+R(1,11),
 }
 for name,ex in ids.items():assert s.simplify(ex)==0,name
 constants={
  'C half-angle cap':R(17,12)**2-2,
  'a upper contradiction':R(1,11),
  'C low h right root':R(7,8)-R(17,20),
  'C high h first endpoint':R(17,20)-(R(1,3)+R(1,5)/k(R(1,3))),
  'C high h second endpoint':R(17,20)-(R(5,12)+R(1,5)/k(R(5,12))),
  'global q domain margin':1-R(17,20)-delta(R(1,5)),
  'W threshold gap':R(1,8)*g(R(1,8))-delta(R(1,5)),
  'small W g lower':g(R(1,8)),
  'M domain margin':1-R(23,7)*delta(R(1,5)),
  'Phi derivative gap squared':8-R(11,4)**2,
  'combined derivative margin':R(175,72)-R(1610,841),
  'Phi endpoint squared comparison':3*468**2-803**2,
  'q endpoint comparison':R(1,20)-R(23,670),
  'final short-leg contradiction':R(7,12)-R(4,9)-R(1,20),
 }
 assert all(v>0 for v in constants.values()),constants
 assert R(1,3)+R(1,5)/k(R(1,3))==R(3,5)
 assert R(5,12)+R(1,5)/k(R(5,12))==R(123,200)
 assert R(17,20)+delta(R(1,5))==R(14,15)
 assert R(1,8)*g(R(1,8))-delta(R(1,5))==R(1,72)
 assert R(23,7)*delta(R(1,5))==R(23,84)
 assert s.diff(delta(z),z).subs(z,R(1,5))==R(125,144)
 assert R(2)/(2-R(23,84))**2*R(23,7)*R(125,144)==R(1610,841)
 assert q(R(23,7)*delta(R(1,10)))==R(23,670)
 assert s.simplify(Phi.subs(w,R(2,11))-13*(11-4*s.sqrt(3))/121)==0
 new_names={'parallel chord limit','parallel chord loss','loss increasing on small-angle domain',
  'small W orientation left bound','small W orientation right bound','bridge surplus coefficient','q M derivative'}
 assert len(new_names)==7 and new_names.issubset(ids)
 result={'result':'passed','new_algebraic_identities':len(new_names),
  'replayed_algebraic_identities':len(ids)-len(new_names),'positive_exact_comparisons':len(constants),
  'new_polynomial_certificates':0,'UNSAT':0,
  'new_theorem':'Entire remaining right-W bridge excluded; in remaining double-direct W contains neither R nor Q2',
  'remaining_mechanism':'positive-C double-direct, W avoids QU and Q2 and R, 1/10 < z < 1/5',
  'not_proved':'entire double-direct, G2 or S(6)=2','global_bound':'2 <= S(6) < 2.03'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
