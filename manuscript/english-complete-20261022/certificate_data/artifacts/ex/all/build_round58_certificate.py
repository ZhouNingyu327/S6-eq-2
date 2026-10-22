"""Round58: explicit full-domain polynomial certificates, no solver needed."""
from pathlib import Path
from itertools import product
from math import comb
import sympy as s,json
R=s.Rational;t,x,h,u,v,w=s.symbols('t x h u v w')
b=lambda a:(1+a*a)/(1-a*a);k=lambda a:2*a/(1-a*a)

def width_polynomials(B):
 bn,bd=s.cancel(B).as_numer_denom()
 if bd.subs(t,R(1,10))<0:bn,bd=-bn,-bd
 dx=1-x*x;dt=1-t*t;d=1+h*h;c=1-h*h;ss=2*h
 kn=(2*x*dt-2*t*dx)*bd;gn=((1+x*x)*bd-bn*dx)*dt
 sd=dx*bd;sn=(1+x*x)*bd-2*x*bn
 pn=7*sd-12*sn;jn=2*pn;jd=12*sd+pn
 yy=(bn-bd)*dt*kn-2*t*bd*gn;factor=bd*dt*kn
 eh=c*(jn+(1-x)*jd)-d*jd
 ej=ss*bd*dt*(jn*kn+jd*(kn-gn))+c*jd*yy-d*jd*factor
 axis=jn*d*d*factor-jd*(2*c*(d-c)+c*(c+ss)*t+c*(c-ss)*x)*factor
 joint=jn*d*d*factor+jd*(c*(c-ss)*(1-x)*factor+(c+ss)*(ss*bd*dt*(kn-gn)+c*yy)-2*c*d*factor)
 return (s.expand(c*factor*eh+h*ej),s.expand(3*d*factor*eh+2*axis+2*joint))

def triangle(X):
 Bt=1+k(t)*(1-(b(t)-1)-t);bn,bd=s.cancel(Bt).as_numer_denom()
 if bd.subs(t,R(1,10))<0:bn,bd=-bn,-bd
 y,z=s.cancel(X).as_numer_denom()
 if z.subs(h,R(1,5))<0:y,z=-y,-z
 td=(z*z-y*y)*bd;tn=(z*z+y*y)*bd-2*bn*y*z
 n=5*td+12*tn;m=19*td-12*tn;an=2*h*(1-h)-t*(1-h*h)
 vn=2*h*n*n-an*n*m;vd=(n-h*m)*(m+h*n)
 dn=2*h*h+t*(1-h*h);qd=4*h-dn
 return s.expand((2*qd*td-dn*td-tn*qd)*(vd-vn)-qd*td*vd)

def main():
 Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t)
 specs=[]
 for name,B,lo,hi,xlo,xhi in [
  ('middle',Bt,R(1,5),R(4,15),R(9,25),R(12,25)),
  ('late',Bc,R(4,15),R(3,10),R(3,8),R(5,11)),
  ('end',Bc,R(3,10),R(19,50),R(39,100),R(11,25))]:
  low,high=width_polynomials(B)
  specs.append(('width_low_'+name,low,[(t,lo,hi),(x,xlo,xhi),(h,R(0),R(3,10))],s.Integer(1)))
  specs.append(('width_high_'+name,high,[(t,lo,hi),(x,xlo,xhi),(h,R(3,10),R(1,3))],s.Integer(1)))
 for name,X,hl,hu,tl,tu in [
  ('triangle_small',k(h)*(1-h-t),R(1,6),R(3,10),R(0),R(1,10)),
  ('triangle_medium_low',t+R(1,6),R(1,6),R(1,5),R(1,10),R(1,6)),
  ('triangle_medium_high',(3*k(h)*(1-h-t)+t+R(1,6))/4,R(1,5),R(3,10),R(1,10),R(1,6)),
  ('triangle_transition',R(1,5)+R(4,5)*t,R(1,6),R(3,10),R(1,6),R(1,5))]:
  specs.append((name,triangle(X),[(h,hl,hu),(t,tl,tu)],s.Integer(1)))
 for name,expr,axis in [
  ('line1',Bt-b(t+R(1,6)),(t,R(1,10),R(1,6))),
  ('line2',Bt-b(R(1,5)+R(4,5)*t),(t,R(1,6),R(1,5))),
  ('horizontal',R(7,12)-(x+R(2,35))/(2-x-R(2,35))-b(x)+R(5,4)*k(x),(x,R(1,3),R(1,2)))]:
  num,den=s.cancel(expr).as_numer_denom();a,lo,hi=axis
  if den.subs(a,(lo+hi)/2)<0:num,den=-num,-den
  specs.append((name,num,[axis],s.factor(den)))
 records=[];count=0
 for name,num,axes,den in specs:
  uvw=[u,v,w][:len(axes)]
  p=s.Poly(s.expand(num.subs({a:lo+(hi-lo)*q for (a,lo,hi),q in zip(axes,uvw)})),*uvw)
  deg=p.degree_list();cc=[];terms=p.terms()
  for index in product(*(range(n+1) for n in deg)):
   value=R(0)
   for powers,coef in terms:
    if all(j<=i for j,i in zip(powers,index)):
     for j,i,n in zip(powers,index,deg):coef*=R(comb(i,j),comb(n,j))
     value+=coef
   assert value>0,(name,index,value);cc.append(str(value))
  records.append({'name':name,'axes':[[str(a),str(lo),str(hi)] for a,lo,hi in axes],
   'degrees':list(deg),'rational_target_denominator':str(den),
   'order':'lexicographic multi-index, last index fastest','coefficients':cc})
  count+=len(cc);print(json.dumps({'name':name,'degree':deg,'positive_coefficients':len(cc)}),flush=True)
 assert len(records)==13 and count==3371,(len(records),count)
 src=Path(__file__).resolve().parent
 (src/'round58_certificate.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
 print(json.dumps({'new_polynomials':len(records),'positive_coefficients':count}))
if __name__=='__main__':main()
