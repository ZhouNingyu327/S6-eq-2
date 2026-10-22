"""Exact positive/negative local checks for the five-point F fitting criterion."""
from fractions import Fraction as F
from pathlib import Path
import json
from forced_f_square_fit import square_fit
def main():
 fits=[("-21/40","0"),("29/40","0"),("0","9/20"),("-1/10","2/5"),("1/5","1/2")]
 rejects=[("-11/20","0"),("11/20","0"),("0","4/5"),("-11/20","4/5"),("11/20","4/5")]
 yes=square_fit(fits);no=square_fit(rejects)
 assert yes["fits_unit_square"] and not no["fits_unit_square"]
 # A supplied actual unit square independently verifies the feasible case.
 pts=[(F(x),F(y)) for x,y in fits];c=F(4,5);s=F(3,5)
 p1=[c*x+s*y for x,y in pts];p2=[-s*x+c*y for x,y in pts]
 assert max(p1)-min(p1)<=1 and max(p2)-min(p2)<=1
 assert F(no["maximum_vertex_norm_squared"])==F(100,121)
 # Every distance, triangle area and all three older scalar F budgets pass.
 width=F(11,10);height=F(4,5)
 assert width*width+height*height==F(37,20)<2
 assert width*height==F(22,25)<1
 assert width+height*height==F(87,50)<2
 assert width>1 and height<1
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 result={"result":"passed","feasible_five_points":fits,"feasible_result":yes,
  "infeasible_five_points":rejects,"infeasible_result":no,
  "infeasible_rectangle":{"width":str(width),"height":str(height),
   "diameter_squared":"37/20","area":"22/25","base_plus_height_squared":"87/50"},
  "scope":"Exact local one-square inclusion; the rejected set passes older diameter, triangle-area and base/height budgets",
  "not_proved":"That these points arise from a complete six-square covering; no new whole S6 family excluded"}
 (out/"S6_round47_forced_fit_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({"result":"passed","feasible_max_norm":yes["maximum_vertex_norm_squared"],
  "infeasible_max_norm":no["maximum_vertex_norm_squared"],"infeasible_rectangle":"11/10 by 4/5"},indent=2))
if __name__=="__main__":main()
