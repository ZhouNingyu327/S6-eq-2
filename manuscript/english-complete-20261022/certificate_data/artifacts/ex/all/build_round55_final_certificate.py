"""Round55 final: explicit full-domain certificates for positive upper-W exclusion."""
from pathlib import Path
from math import comb
import sympy as s,json
R=s.Rational;t,x,h,u,v=s.symbols("t x h u v")
k=lambda a:2*a/(1-a*a);b=lambda a:(1+a*a)/(1-a*a)
q=lambda a:a/(2-a);g=lambda a:(1-a)/(1+a)
Bt=1+k(t)*(1-(b(t)-1)-t);Bc=1+k(t)*(R(177,209)-t)
def endpoint(B,H,eta):
 S=b(x)-k(x)*B;K=k(x)-k(t)
 return s.cancel((1-eta*eta)*(2*(H-S)*K+(1+H-S)*(K-(b(x)-B)))
   +2*eta*(1+H-S)*((B-1)*K-k(t)*(b(x)-B))
   -(1+eta*eta)*K*(1+H-S))
def axis(B,H):
 S=b(x)-k(x)*B
 return 2*(H-S)*(k(x)-k(t))-(1+H-S)*(b(x)-B)
def diagonal(B,H):
 S=b(x)-k(x)*B;K=k(x)-k(t)
 return (B*(k(x)+1)-b(x)*(1+k(t))-R(71,50)*K)*(1+H-S)+2*(H-S)*K
def main():
 specs=[]
 charts=[
 ("first",Bt,R(3,20),R(1,6),R(33,100),R(101,200)),
 ("transition",Bt,R(1,6),R(1,5),R(1,3),R(1,2)),
 ("middle",Bt,R(1,5),R(4,15),R(9,25),R(12,25)),
 ("late",Bc,R(4,15),R(3,10),R(3,8),R(5,11)),
 ("end",Bc,R(3,10),R(2,5),R(3,8),R(11,25))]
 for name,B,lo,hi,xlo,xhi in charts:
  for kind,expr in [("axis",axis(B,R(7,12))),("diagonal",diagonal(B,R(7,12)))]:
   if name=="end" and kind=="diagonal":continue
   specs.append((name+"_"+kind,expr,[(t,lo,hi),(x,xlo,xhi)]))
 for name,H,eta,lo,hi,xlo,xhi in [
  ("cut_mid",R(16,23),R(1,5),R(1,20),R(3,20),R(1,5),R(2,3)),
  ("cut_small",R(12,13),R(1,10),R(1,100),R(1,20),R(1,11),R(5,6))]:
  for suffix,e in [("axis",R(0)),("angle",eta)]:
   specs.append((name+"_"+suffix,endpoint(Bt,H,e),[(t,lo,hi),(x,xlo,xhi)]))
 A=g(h)+k(h)*t;X=1-h-t/k(h);HF=2-1/(1-(b(h)-1)-t)
 for name,H,hlo,hhi,thi in [
  ("C_high",R(7,12),R(1,4),R(5,12),R(3,20)),
  ("C_middle_high",HF,R(1,5),R(1,4),R(3,20)),
  ("C_middle",HF,R(1,10),R(1,5),R(1,20)),
  ("C_small",HF,R(1,24),R(1,10),R(1,100))]:
  specs.append((name,H-q(A)-g(X)+k(X)*(Bt-1),[(h,hlo,hhi),(t,R(0),thi)]))
 saved=[]
 for name,expr,axes in specs:
  num,den=s.cancel(expr).as_numer_denom()
  mid={a:(lo+hi)/2 for a,lo,hi in axes}
  if den.subs(mid)<0:num,den=-num,-den
  p=s.Poly(s.expand(num.subs({a:lo+(hi-lo)*w for (a,lo,hi),w in zip(axes,[u,v])})),u,v)
  n,m=p.degree_list()
  cc=[[sum(c*R(comb(i,j),comb(n,j))*R(comb(r,l),comb(m,l))
       for (j,l),c in p.terms() if j<=i and l<=r) for r in range(m+1)] for i in range(n+1)]
  assert min(c for row in cc for c in row)>0,name
  saved.append({"name":name,"axes":[[str(a),str(lo),str(hi)] for a,lo,hi in axes],
   "degrees":[n,m],"positive_denominator":str(s.factor(den)),
   "coefficients":[[str(c) for c in row] for row in cc]})
 total=sum(sum(len(row) for row in r["coefficients"]) for r in saved)
 assert len(saved)==17 and total==824,(len(saved),total)
 folder=Path("work") if Path("work").is_dir() else Path(".")
 (folder/"round55_certificate.json").write_text(json.dumps(saved,indent=2),encoding="utf-8")
 print(json.dumps({"new_full_polynomials":17,"new_positive_coefficients":total,"inherited_end_joint_coefficients":25}))
if __name__=="__main__":main()

