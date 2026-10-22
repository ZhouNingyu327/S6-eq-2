"""Unfrozen positive-rotation formulas only; no new exclusion."""
from pathlib import Path
import sympy as s,json
a,z,h,S,r=s.symbols('a z h S r')
b=lambda t:(1+t*t)/(1-t*t);k=lambda t:2*t/(1-t*t)
X=(b(a)+S-2)/(k(a)-k(z));e=1-S-k(z)*X
K=k(h);delta=b(h)-1
QT=S+(k(z)-1/K)*X
RP=delta+X+K*e
checks={
 'LT positive lower':1-a+K*(1-z)-b(h)-(-a+K*(1-h-z)),
 'RT positive upper':K*r+1-z-b(h)-K*(r-h-z/K),
 'P1T positive expression':((1-X)+K*(1-z-e)-b(h))/K-(QT-h-z),
 'P1T S derivative':s.diff(QT,S)-(k(a)-1/K)/(k(a)-k(z)),
 'P1R S derivative':s.diff(RP,S)-(1-K*k(a))/(k(a)-k(z))}
for label,expr in checks.items():assert s.cancel(expr)==0,label
assert 1-s.Rational(5,12)-s.Rational(4,15)==s.Rational(19,60)>0
result={'result':'passed','algebraic_identities':len(checks),'positive_constants':1,
 'new_exclusion':False,'scope':'positive-C necessary forms; independent geometric use remains to be checked'}
(Path(__file__).resolve().parent.parent/'outputs'/'S6_round61_forms_check.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result,indent=2))
