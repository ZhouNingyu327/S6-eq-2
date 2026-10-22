"""Unfrozen arithmetic support for the wider negative-C monotonicity lemma."""
from pathlib import Path
import sympy as s,json
R=s.Rational;h=R(3,10)
c=(1-h*h)/(1+h*h);ss=2*h/(1+h*h)
assert c==R(91,109) and c-ss==R(31,109)
product=c*(c-ss)
assert product==R(2821,11881)
assert R(1,2)-2*product==R(597,23762)>0
assert 1-(R(1,2)+R(1,4)+product)==R(597,47524)>0
result={"result":"passed","scope":"Unfrozen arithmetic identities; geometric monotonicity proof is in round57 working notes",
 "domain":"negative C, eta_C >= 3/10, actual theta <= 45 degrees, tau <= 1/5",
 "derivative_upper_bound":"-597/23762","q_argument_upper_margin":"597/47524",
 "new_angle_exclusion":False,"whole_problem":"open"}
Path("outputs/S6_round57_monotonicity_check.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
print(json.dumps(result,indent=2))
