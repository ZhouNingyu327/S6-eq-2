"""Reproduce the saved relaxed SAT models and the physical conditions they violate."""
from pathlib import Path
import json
import sympy as sp
import z3


root=Path(__file__).resolve().parent
raw=json.loads((root/"round23_relaxed_query_diagnostics.json").read_text(encoding="utf-8"))
saved=[row for row in raw["queries"] if row["result"]=="sat"]
assert len(saved)==2
assert {row["name"] for row in saved}=={
    "qU in C, bottom-midpoint corner: double Delta below eta",
    "positive C rotation bounds actual left upper ray lambda<7/12"}

r,y,z,dy,dz,eta=z3.Reals("review_r review_y review_z review_dy review_dz review_eta")
one=z3.SolverFor("QF_NRA")
one.add(r==z3.RealVal("-1/2"),y==z3.RealVal("1/4"),z==z3.RealVal("3/4"),
    dy==z3.RealVal("1/24"),dz==z3.RealVal("9/8"),eta==z3.RealVal("1/2"),
    y>0,15*y<4,z>0,z==y-r,2*(1-y)*dy==y*y,2*(1-z)*dz==z*z,
    r<dy,r+dz>eta,6*eta>1)
assert one.check()==z3.sat
one.add(r>=0)
assert one.check()==z3.unsat

p,s,mu,ray,lam=z3.Reals("review_p review_s review_mu review_ray review_lam")
two=z3.SolverFor("QF_NRA")
two.add(p>0,16*p*p==15,s==z3.RealVal("1/4"),mu==z3.RealVal("17/16"),
    ray==z3.RealVal("1/2"),lam==z3.RealVal("5/8"),
    p>=s,p*p+s*s==1,mu>1,20*ray>3,s*(mu+ray)+p*lam<=1,12*lam>=7)
assert two.check()==z3.sat
two.add(p*(mu+ray)<=1)
assert two.check()==z3.unsat
P=sp.sqrt(15)/4
H=sp.Rational(25,16)
assert P*H>1
assert sp.Rational(1,4)*H+P*sp.Rational(5,8)<1
result={"status":"both relaxed countermodels reproduced and rejected by restored physical conditions",
    "relaxed_SAT_checks":2,"pinned_models_with_restored_condition_UNSAT":2,
    "included_in_formal_UNSAT_query_count":False,
    "negative_ray_countermodel":{"r":"-1/2","y":"1/4","z":"3/4","Delta(z)":"9/8",
        "violated_necessary_condition":"r>=0; r is a real ray length"},
    "missing_horizontal_cap_countermodel":{"p":"sqrt(15)/4","s":"1/4","mu":"17/16",
        "r":"1/2","lambda":"5/8","horizontal_chord":"25/16",
        "left_upper_projection":"25/64+5sqrt(15)/32 <1",
        "horizontal_projection":"25sqrt(15)/64 >1",
        "violated_necessary_condition":"p*(mu+r)<=1"},
    "not_actual_six_square_coverings":True,
    "strict_checks_file":"round23_g4_residual_checks.json"}
(root/"round23_relaxed_query_review.json").write_text(
    json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
print(json.dumps(result,ensure_ascii=False,indent=2))
