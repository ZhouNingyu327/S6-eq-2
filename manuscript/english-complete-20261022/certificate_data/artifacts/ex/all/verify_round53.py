"""Round53 actual LEFT-seam lemma and cited historical proof bytes."""
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
 digest="6a0659e49b384382ccb1fa0c4fa7af76f772b10c1955279320dcbb949689b7b5"
 blob=(out/"S6_round52_verification.zip").read_bytes();assert sha(blob)==digest
 with zipfile.ZipFile(BytesIO(blob)) as z:
  assert z.testzip() is None
  for n,h in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(n))==h
  for n in ["S6_attack_round52.md","S6_attack_round46.md"]:
   assert z.read(n)==(out/n).read_bytes(),n
 for n in range(52,42,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:blob=z.read(f"S6_round{n-1}_verification.zip")
 old42="30bcf492a2d35fff85de5ec5547302f2d758d883c85b5a1917bd60e0db2ac2f1"
 assert sha(blob)==old42
 with zipfile.ZipFile(BytesIO(blob)) as z:
  assert z.testzip() is None
  assert z.read("S6_attack_round42.md")==(out/"S6_attack_round42.md").read_bytes()
 p=subprocess.run([sys.executable,str(src/"check_round53.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round53.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round53_local_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["full_polynomial_reconstructions"],
  local["positive_rational_coefficients"],local["constant_count"],local["UNSAT"])==(8,2,57,6,0)
 report=(out/"S6_attack_round53.md").read_text(encoding="utf-8")
 review=(out/"S6_round53_geometric_review.md").read_text(encoding="utf-8")
 assert "S_1<q(Q)" in report and "没有排除新整角带或整接合机制" in report
 assert "32. " in review
 result={"result":"passed","new_lemma":local["new_lemma"],
  "near_diagonal_consequence":local["near_diagonal_consequence"],
  "new_totals":{"UNSAT":0,"algebraic_identities":8,"full_polynomial_reconstructions":2,
   "strictly_positive_rational_coefficients":57,"whole_analytic_charts":2,
   "exact_constants":6,"geometric_review_items":32},
  "historical_round52":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited52_and46_proof_bytes":"matched","own_full_entry_replayed":False},
  "historical_round42":{"sha256":old42,"nested_archive_crc":"passed",
   "cited_proof_bytes":"matched","own_full_entry_replayed":False},
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round53_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

