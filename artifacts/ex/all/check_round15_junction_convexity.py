"""Exact symbolic verification of the L3-free forced junction helper."""
from pathlib import Path
import json
import sympy as s
x,y,N=s.symbols('x y N')
den=(x-y)*(1+x*y)
Y=2*x*y*(N-x-y)/den
X=1-x+y*(1-x*x)*(N-x-y)/den
Y0=Y.subs(N,1);X0=X.subs(N,1)
lam=(1-x-y)/(N-x-y)
assert s.cancel(X0-((1-lam)*(1-x)+lam*X))==0
assert s.cancel(Y0-lam*Y)==0
assert s.cancel(1-lam-(N-1)/(N-x-y))==0
result={'classification':'exact symbolic identity audit',
        'proved_scope':'Q(1) lies on the segment from (1-t2,0) to Q(L3), hence in actual C',
        'premises':'0<y<x<1, x+y<1, N>=1, C convex, (1-x,0) and Q(N) in C',
        'X0':str(s.factor(X0)),'Y0':str(s.factor(Y0)),
        'lambda':str(lam),'identities_verified':3,'passed':True}
Path(__file__).with_name('round15_junction_convexity_checks.json').write_text(
    json.dumps(result,indent=2),encoding='utf-8')
print(result,flush=True)
