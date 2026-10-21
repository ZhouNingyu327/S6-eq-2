"""Independent rational targets and inverse Bernstein reconstruction for round58.
Does not import the certificate generator or any exploratory/LP program.
"""
from pathlib import Path
from itertools import product
from collections import defaultdict
from math import comb
import sympy as s,json
R=s.Rational

def main():
 src=Path(__file__).resolve().parent
 recs=json.loads((src/'round58_certificate.json').read_text(encoding='utf-8'))
 h,t,x,a,u,v,w=s.symbols('h t x a u v w')
 b=lambda y:(1+y*y)/(1-y*y);k=lambda y:2*y/(1-y*y)
 g=lambda y:(1-y)/(1+y);q=lambda y:y/(2-y);j=lambda y:2*y/(1+y)
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t)
 C,D,Z,JN,JD,KN,GN,BD,DT,YN=s.symbols('C D Z JN JD KN GN BD DT YN')
 jj=JN/JD;xx=GN/KN;yy=YN/(BD*DT*KN)
 EH=C/D*(jj+1-x)-1
 EJ=Z/D*(jj+1-xx)+C/D*yy-1
 EA=jj-(2*C*(D-C)+C*(C+Z)*t+C*(C-Z)*x)/D**2
 EP=jj+C*(C-Z)*(1-x)/D**2+(C+Z)*(Z*(1-xx)+C*yy)/D**2-2*C/D
 abs_low=s.cancel((EH+h/C*EJ)*C*D*JD*BD*DT*KN)
 abs_high=s.cancel((3*EH+2*EA+2*EP)*D**2*JD*BD*DT*KN)
 assert s.denom(abs_low)==s.denom(abs_high)==1
 specs=[]
 for name,B0,lo,hi,xlo,xhi in [
  ('middle',Bt,R(1,5),R(4,15),R(9,25),R(12,25)),
  ('late',Bc,R(4,15),R(3,10),R(3,8),R(5,11)),
  ('end',Bc,R(3,10),R(19,50),R(39,100),R(11,25))]:
  bd=(1-t*t)**2 if name=='middle' else 209*(1-t*t)
  bn=s.cancel(B0*bd);assert s.denom(bn)==1
  dt=1-t*t;dx=1-x*x
  sd=dx*bd;sn=(1+x*x)*bd-2*x*bn
  kn=2*(x-t)*(1+x*t)*bd
  gn=((1+x*x)*bd-bn*dx)*dt
  jd=19*sd-12*sn;jn=14*sd-24*sn
  yn=(bn-bd)*dt*kn-2*t*bd*gn
  mapping={C:1-h*h,D:1+h*h,Z:2*h,JN:jn,JD:jd,KN:kn,GN:gn,BD:bd,DT:dt,YN:yn}
  low=s.expand(abs_low.subs(mapping));high=s.expand(abs_high.subs(mapping))
  specs.append(('width_low_'+name,low,[(t,lo,hi),(x,xlo,xhi),(h,R(0),R(3,10))],s.Integer(1)))
  specs.append(('width_high_'+name,high,[(t,lo,hi),(x,xlo,xhi),(h,R(3,10),R(1,3))],s.Integer(1)))
 for name,X,hl,hu,tl,tu in [
  ('triangle_small',k(h)*(1-h-t),R(1,6),R(3,10),R(0),R(1,10)),
  ('triangle_medium_low',t+R(1,6),R(1,6),R(1,5),R(1,10),R(1,6)),
  ('triangle_medium_high',(3*k(h)*(1-h-t)+t+R(1,6))/4,R(1,5),R(3,10),R(1,10),R(1,6)),
  ('triangle_transition',(1+4*t)/5,R(1,6),R(3,10),R(1,6),R(1,5))]:
  y,z=s.cancel(X).as_numer_denom()
  if z.subs(h,R(1,5))<0:y,z=-y,-z
  bd=(1-t*t)**2;bn=s.cancel(Bt*bd)
  td=(z-y)*(z+y)*bd;tn=(z*z+y*y)*bd-2*y*z*bn
  nn=5*td+12*tn;mm=19*td-12*tn
  an=2*h-2*h*h-t+t*h*h
  vn=nn*(2*h*nn-an*mm);vd=(nn-h*mm)*(mm+h*nn)
  dn=2*h*h+t-t*h*h;qd=4*h-dn
  num=s.expand(((2*qd-dn)*td-tn*qd)*(vd-vn)-qd*td*vd)
  specs.append((name,num,[(h,hl,hu),(t,tl,tu)],s.Integer(1)))
 specs.extend([
  ('line1',Bt-b(t+R(1,6)),[(t,R(1,10),R(1,6))],-(1-t*t)**2*(6*t-5)*(6*t+7)),
  ('line2',Bt-b((1+4*t)/5),[(t,R(1,6),R(1,5))],4*(1-t*t)**2*(2*t+3)),
  ('horizontal',R(7,12)-q(x+R(2,35))-b(x)+R(5,4)*k(x),[(x,R(1,3),R(1,2))],12*(x-1)*(x+1)*(35*x-68))])
 total=0
 for rec,(name,expr,axes,den) in zip(recs,specs):
  assert rec['name']==name and rec['axes']==[[str(z),str(lo),str(hi)] for z,lo,hi in axes]
  assert s.expand(s.sympify(rec['rational_target_denominator'],locals={'h':h,'t':t,'x':x})-den)==0,name
  numerator=s.cancel(expr*den) if den!=1 else expr
  assert s.denom(numerator)==1,name
  uvw=[u,v,w][:len(axes)]
  p=s.Poly(s.expand(numerator.subs({z:lo+(hi-lo)*r for (z,lo,hi),r in zip(axes,uvw)})),*uvw)
  deg=rec['degrees'];assert list(p.degree_list())==deg,name
  indices=list(product(*(range(n+1) for n in deg)))
  cc=[R(vv) for vv in rec['coefficients']]
  assert len(indices)==len(cc) and all(val>0 for val in cc),name
  rebuilt=defaultdict(lambda:R(0))
  for index,val in zip(indices,cc):
   for powers in product(*(range(i,n+1) for i,n in zip(index,deg))):
    vv=val
    for i,jj0,n in zip(index,powers,deg):vv*=comb(n,i)*comb(n-i,jj0-i)*(-1)**(jj0-i)
    rebuilt[powers]+=vv
  assert {powers:val for powers,val in rebuilt.items() if val}==p.as_dict(),name
  total+=len(cc)
 assert len(recs)==len(specs)==13 and total==3371
 al=1-h-t/k(h);X=k(h)*(1-h-t)
 NN,MM,AL,VN,VD,DN,QD,TN,TD=s.symbols('NN MM AL VN VD DN QD TN TD')
 identities=[
  ('left-axis inverse',j(g(a))-(1-a)),
  ('negative normal circle',((1-h*h)/(1+h*h))**2+(2*h/(1+h*h))**2-1),
  ('K numerator',2*x*(1-t*t)-2*t*(1-x*x)-2*(x-t)*(1+x*t)),
  ('E1 V bound',(b(h)-1+t-k(h)*(1-a))/(1-k(h)/k(a))-2*h*a*(a-al)/((a-h)*(1+h*a))),
  ('alpha margin',k(h)*(1-2*h)-R(1,5)-(-19*h*h+10*h-1)/(5*(1-h*h))),
  ('X upper',(1-h*h)*(1-X)-((1-h)**2+2*h*t)),
  ('A ratio',g(R(7,12)-TN/TD)-(5*TD+12*TN)/(19*TD-12*TN)),
  ('V rational',2*h*(NN/MM)*(NN/MM-AL)/((NN/MM-h)*(1+h*NN/MM))-(2*h*NN*NN-2*h*AL*NN*MM)/((NN-h*MM)*(MM+h*NN))),
  ('triangle numerator',((2-DN/QD-TN/TD)*(1-VN/VD)-1)*QD*TD*VD-((2*QD*TD-DN*TD-TN*QD)*(VD-VN)-QD*TD*VD)),
  ('first increasing factor',s.diff(a/(1+h*a),a)-1/(1+h*a)**2),
  ('second increasing factor',s.diff((a-AL)/(a-h),a)-(AL-h)/(a-h)**2),
  ('horizontal q cap',g(1-R(2,35)-x)-q(x+R(2,35)))]
 for name,expr in identities:assert s.cancel(expr)==0,name
 constants={
  'end_x_cap':Bc.subs(t,R(3,10))-b(R(39,100)),
  'long_leg_5_over_4':Bt.subs(t,R(1,6))-R(5,4),
  'alpha_lower_endpoint':(-19*h*h+10*h-1).subs(h,R(1,6)),
  'alpha_upper_endpoint':(-19*h*h+10*h-1).subs(h,R(3,10)),
  'q_domain':1-R(1,2)-R(2,35),
  'X_positive':1-R(3,10)-R(1,5),
  'diameter_H':R(17,12)**2-2,
  'normal_c_minus_s':1-R(1,3)**2-2*R(1,3)}
 assert all(val>0 for val in constants.values())
 assert constants['end_x_cap']==R(293184,161262101)
 assert constants['long_leg_5_over_4']==R(79,4900)
 result={'result':'passed','new_polynomial_reconstructions':len(specs),'new_positive_coefficients':total,
  'algebraic_identities':len(identities),'positive_exact_constants':len(constants),'UNSAT':0,
  'new_theorem':'W contains QU, negative C: h >= 1/6 excluded; every remaining upper-W case has tau < 1/6',
  'remaining_upper_W':'negative 1/24 < h < 1/6 and 0 < tau < 1/6',
  'not_proved':'general double direct, right-W bridge, all G2 or S(6)=2'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
