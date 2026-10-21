"""Round50 exact coupled surplus and inherited-proof byte audit."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for n,h in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/n).read_bytes())==h,n
 digest="f3edbdfc9425bf9631aaff37d48de32407ef8f646f55833b1b27869fe576d37e"
 old=out/"S6_round49_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as z:
  assert z.testzip() is None
  for n,h in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(n))==h
  for n in ["S6_attack_round49.md","S6_attack_round43.md"]:
   assert z.read(n)==(out/n).read_bytes(),n
 p=subprocess.run([sys.executable,str(src/"check_round50.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round50.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round50_local_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["full_polynomial_identities"],
  local["strictly_positive_rational_coefficients"],local["constant_count"],local["UNSAT"])==(3,1,24,20,0)
 report=(out/"S6_attack_round50.md").read_text(encoding="utf-8")
 review=(out/"S6_round50_geometric_review.md").read_text(encoding="utf-8")
 assert "ηC∈[0,1/16]全部关闭" in report and "没有新整个接合机制关闭" in report
 assert "30. " in review
 result={"result":"passed","new_closed_subclass":local["new_closed_subclass"],
  "new_totals":{"UNSAT":0,"algebraic_identities":3,"full_polynomial_reconstructions":1,
   "strictly_positive_rational_coefficients":24,"whole_bivariate_rectangles":1,
   "exact_constants":20,"geometric_review_items":30},
  "historical_round49":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited49_and43_proof_bytes":"matched","own_full_entry_replayed":False},
  "inherited_checks":"Round49 separately replayed the original round43 scalar checker; not repeated or counted anew here",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round50_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

