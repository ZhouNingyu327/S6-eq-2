"""Independent round47 long-bottom-chord and local F fitting entry."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 digest="069a77ec47e8883819577a7d5f7a7c9075b040950b24b5d5068bedfe54164113"
 old=out/"S6_round46_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as archive:
  assert archive.testzip() is None
  assert archive.read("S6_attack_round46.md")==(out/"S6_attack_round46.md").read_bytes()
  for name,h in json.loads(archive.read("manifest.json"))["files"].items():
   assert sha(archive.read(name))==h
 for script in ["check_round47.py","check_round47_forced_fit.py"]:
  p=subprocess.run([sys.executable,str(src/script)],cwd=cwd,capture_output=True,
   text=True,encoding="utf-8",errors="strict",
   env={**os.environ,"PYTHONIOENCODING":"utf-8"})
  (out/(script+".log")).write_text(p.stdout+p.stderr,encoding="utf-8")
  assert p.returncode==0,(script,p.stdout,p.stderr)
 local=json.loads((out/"S6_round47_local_verification.json").read_text(encoding="utf-8"))
 fit=json.loads((out/"S6_round47_forced_fit_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["full_polynomial_identities"],
  local["strictly_positive_rational_coefficients"],local["constant_count"],local["UNSAT"])==(6,4,76,3,0)
 assert fit["result"]=="passed" and fit["feasible_result"]["fits_unit_square"]
 assert not fit["infeasible_result"]["fits_unit_square"]
 assert fit["feasible_result"]["maximum_vertex_norm_squared"]=="32/25"
 assert fit["infeasible_result"]["maximum_vertex_norm_squared"]=="100/121"
 report=(out/"S6_attack_round47.md").read_text(encoding="utf-8")
 review=(out/"S6_round47_geometric_review.md").read_text(encoding="utf-8")
 assert "Σ=S1+S2严格小于1" in report and "没有新整接合机制关闭" in report
 assert "34. " in review and "不是S(6)=2的反例" in report
 result={"result":"passed","scope":local["scope"],
  "totals":{"UNSAT":0,"algebraic_identities":6,"full_polynomial_identities":4,
   "symbolic_identities":10,"constants":3,"whole_rational_charts":4,
   "strictly_positive_rational_coefficients":76,"exact_local_fit_examples":2,
   "geometric_review_items":34},
  "historical_round46":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_source_bytes":"matched","own_full_entry_replayed":False},
  "fit_scope":fit["scope"],"not_proved":local["not_proved"],
  "global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round47_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

