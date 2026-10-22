"""Round52 new global angle separation and historical source-byte entry."""
from pathlib import Path
from io import BytesIO
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for n,h in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/n).read_bytes())==h,n
 digest="008b7bad2ff1a180a0d601784fee35899367de29d0c5e1c3e83394415ccf52ee"
 blob=(out/"S6_round51_verification.zip").read_bytes();assert sha(blob)==digest
 with zipfile.ZipFile(BytesIO(blob)) as z:
  assert z.testzip() is None
  for n,h in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(n))==h
  assert z.read("S6_attack_round51.md")==(out/"S6_attack_round51.md").read_bytes()
 for n in range(51,46,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:blob=z.read(f"S6_round{n-1}_verification.zip")
 old46="069a77ec47e8883819577a7d5f7a7c9075b040950b24b5d5068bedfe54164113"
 assert sha(blob)==old46
 with zipfile.ZipFile(BytesIO(blob)) as z:
  assert z.testzip() is None
  assert z.read("S6_attack_round46.md")==(out/"S6_attack_round46.md").read_bytes()
 p=subprocess.run([sys.executable,str(src/"check_round52.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round52.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round52_local_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["full_polynomial_reconstructions"],
  local["positive_rational_coefficients"],local["constant_count"],local["UNSAT"])==(8,1,5,14,0)
 report=(out/"S6_attack_round52.md").read_text(encoding="utf-8")
 review=(out/"S6_round52_geometric_review.md").read_text(encoding="utf-8")
 assert "η≤1/24不可能" in report and "没有新整接合机制关闭" in report
 assert "36. " in review
 result={"result":"passed","new_closed_subclass":local["new_closed_subclass"],
  "global_consequence":local["global_consequence"],
  "new_totals":{"UNSAT":0,"algebraic_identities":8,"full_polynomial_reconstructions":1,
   "strictly_positive_rational_coefficients":5,"exact_constants":14,"geometric_review_items":36},
  "historical_round51":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_proof_bytes":"matched","own_full_entry_replayed":False},
  "historical_round46":{"sha256":old46,"nested_archive_crc":"passed","cited_proof_bytes":"matched",
   "own_full_entry_replayed":False},
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round52_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

