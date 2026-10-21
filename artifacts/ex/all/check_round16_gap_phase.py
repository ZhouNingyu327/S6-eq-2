"""Phase-dependent residual-gap ownership; independent of F horizontal emptiness."""
from pathlib import Path
import itertools,json,time
import sympy as sp
import z3
import check_round14_junction as junction

rows=[]
mu,e,t,r,u,c,s=z3.Reals('mu e t r u c s')
for sign in [1,-1]:
    q=z3.SolverFor('QF_NRA');q.set(timeout=20000)
    q.add(mu>1,e>=0,r>=0,u>=0,r+u>=1,c>=s,s>=0,c*c+s*s==1)
    pts=[(r,0),(0,u),(-mu,-e)]
    for (a,b),(A,B) in itertools.combinations(pts,2):
        U=c*(a-A)+sign*s*(b-B);V=-sign*s*(a-A)+c*(b-B)
        q.add(U<=1,U>=-1,V<=1,V>=-1)
    start=time.time();ans=q.check();assert ans==z3.unsat,ans
    rows.append({'name':'C left-lower exterior point implies r+u<1; sign %d'%sign,
        'result':str(ans),'seconds':time.time()-start})
p=z3.Real('p');q=z3.SolverFor('QF_NRA')
q.add(mu>1,p>=-mu,t>0,mu*mu+t*(mu+p)<=1)
ans=q.check();assert ans==z3.unsat
rows.append({'name':'F bottom midpoint plus left exterior point forbids positive horizontal point',
    'result':str(ans)})
qr,qu=z3.Reals('qr qu');q=z3.SolverFor('QF_LRA')
q.add(r>=0,u>=qu,qr+qu>1,r+u<1,r>=qr)
ans=q.check();assert ans==z3.unsat
rows.append({'name':'positive phase: C owning left gap cannot contain right inner endpoint',
    'result':str(ans),'theory':'QF_LRA'})

# Freshly replay actual-junction inputs. Their statements never require F's
# horizontal trace to be empty; only the quadrant-exclusion step changes.
for fn in [junction.check_angle_order,junction.check_sum,
           junction.check_mu_geometry,junction.check_reduced_hull]:
    rows.append(fn())
junction_identities=junction.identities()

M,T,X,Y=sp.symbols('mu t X Y',positive=True)
den=1+X/T+Y/M
wQ=1/den;wH=(X/T)/den;wB=(Y/M)/den
assert sp.cancel(wQ+wH+wB-1)==0
assert sp.cancel(-T*wH+X*wQ)==0
assert sp.cancel(-M*wB+Y*wQ)==0
P=sp.symbols('p')
assert sp.expand(sp.det(sp.Matrix([[-M,P+M],[T,M]]))+M*M+T*(P+M))==0
result={'classification':'exact conditional geometric results, not a closure of the residual branch',
    'scope':'near G2 right/top meeting: horizontal sign determines left-gap ownership; Q0 remains forced into C in negative phase',
    'queries':rows,'UNSAT_count':8,'NRA_queries':7,'LRA_queries':1,'barycentric_identities':3,
    'triangle_determinant_identity':1,'junction_identities':junction_identities,
    'not_proved':'remaining positive/negative horizontal branches; entire G2; S(6)=2'}
print(json.dumps(result,ensure_ascii=False,indent=2))
Path(__file__).with_name('round16_gap_phase_checks.json').write_text(
    json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
