"""Unfrozen uniform q-domain lemma; no new case exclusion."""
from pathlib import Path
import sympy as s,json
R=s.Rational;h,z=s.symbols('h z')
k=lambda t:2*t/(1-t*t);b=lambda t:(1+t*t)/(1-t*t)
RT=h+z/k(h)
assert s.cancel(s.diff(RT,h,2)-z/h**3)==0
left=R(1,8)+R(1,5)/k(R(1,8))+b(R(1,5))-1
right=R(5,12)+R(1,5)/k(R(5,12))+b(R(1,5))-1
assert left==R(239,240) and right==R(419,600)
constants=[left-right,1-left,R(17,12)**2-2]
assert all(t>0 for t in constants)
assert left/(2-left)==R(239,241)
result={'result':'passed','previous_convexity_identity_rechecked':1,
 'new_exact_endpoint_values':2,'positive_rational_comparisons':3,
 'new_lemma':'all remaining r + Delta_z < 239/240 < 1',
 'requires':'both remaining mechanisms, direct QU, 0 < z < 1/5, 1/8 < h <= sqrt(2)-1',
 'new_case_exclusion':False,'does_not_imply':'Sigma < 1 or complete S(6)=2'}
(Path(__file__).resolve().parent.parent/'outputs'/'S6_round63_entry_check.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result,indent=2))
