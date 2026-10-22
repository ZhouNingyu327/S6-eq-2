"""Round51 exact true-angle charts and historical source-byte entry."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for n,h in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/n).read_bytes())==h,n
 digest="5334f70b992685a9751a90ddd897692ca026737d398917994cde149eebbe9d37"
 old=out/"S6_round50_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as z:
  assert z.testzip() is None
  for n,h in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(n))==h
  for n in ["S6_attack_round50.md","S6_attack_round43.md"]:
   assert z.read(n)==(out/n).read_bytes(),n
 p=subprocess.run([sys.executable,str(src/"check_round51.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round51.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round51_local_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["full_polynomial_reconstructions"],
  local["positive_rational_coefficients"],local["constant_count"],local["UNSAT"])==(6,2,162,22,0)
 report=(out/"S6_attack_round51.md").read_text(encoding="utf-8")
 review=(out/"S6_round51_geometric_review.md").read_text(encoding="utf-8")
 assert "ηC∈[0,1/8]全部排除" in report and "没有新整机制关闭" in report
 assert "34. " in review
 result={"result":"passed","new_closed_subclass":local["new_closed_subclass"],
  "new_totals":{"UNSAT":0,"algebraic_identities":6,"full_polynomial_reconstructions":2,
   "strictly_positive_rational_coefficients":162,"whole_analytic_charts":2,
   "exact_constants":22,"geometric_review_items":34},
  "historical_round50":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited50_and43_proof_bytes":"matched","own_full_entry_replayed":False},
  "inherited_statistics":"43/49/50 are not counted as new results or implicitly replayed",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round51_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

