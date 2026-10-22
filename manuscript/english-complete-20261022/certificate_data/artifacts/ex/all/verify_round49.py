"""Independent new small-angle proof plus separate inherited43 scalar replay."""
from pathlib import Path
from io import BytesIO
import hashlib,json,os,shutil,subprocess,sys,tempfile,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for n,h in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/n).read_bytes())==h,n
 digest="b3356679170d983a0a4be373398d3413ffecfd4da0dde58cf16af13718ccbbce"
 blob=(out/"S6_round48_verification.zip").read_bytes();assert sha(blob)==digest
 with zipfile.ZipFile(BytesIO(blob)) as z:
  assert z.testzip() is None
  for n,h in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(n))==h
  assert z.read("S6_attack_round48.md")==(out/"S6_attack_round48.md").read_bytes()
 for n in range(48,43,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:blob=z.read(f"S6_round{n-1}_verification.zip")
 old43="9345f68c9797f4f10cf409249111bc38713f73afc5b0924d1223550b0c0ec0f1"
 assert sha(blob)==old43
 with zipfile.ZipFile(BytesIO(blob)) as z:
  assert z.testzip() is None
  assert z.read("S6_attack_round43.md")==(out/"S6_attack_round43.md").read_bytes()
  for n in ["check_round43.py","round43_certificate.json"]:
   assert z.read(n)==(src/n).read_bytes()
 env={**os.environ,"PYTHONIOENCODING":"utf-8"}
 p=subprocess.run([sys.executable,str(src/"check_round49.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",env=env)
 (out/"check_round49.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round49_local_verification.json").read_text(encoding="utf-8"))
 assert local["algebraic_identities"]==6 and local["constant_count"]==21 and local["UNSAT"]==0
 # This replay has its own cwd: never overwrites a historical workspace output.
 with tempfile.TemporaryDirectory(prefix="s6_round49_inherited43_") as folder:
  tmp=Path(folder);shutil.copy2(src/"round43_certificate.json",tmp/"round43_certificate.json")
  p=subprocess.run([sys.executable,str(src/"check_round43.py")],cwd=tmp,
   capture_output=True,text=True,encoding="utf-8",errors="strict",env=env)
  (out/"S6_round49_inherited43_check.log").write_text(p.stdout+p.stderr,encoding="utf-8")
  assert p.returncode==0,(p.stdout,p.stderr)
  inherited=json.loads((tmp/"S6_round43_local_verification.json").read_text(encoding="utf-8"))
 (out/"S6_round49_inherited43_scalar_verification.json").write_text(json.dumps(inherited,indent=2),encoding="utf-8")
 assert (inherited["algebraic_identities"],inherited["full_polynomial_identities"],
  inherited["strictly_positive_rational_coefficients"],inherited["constant_count"])==(8,2,20,13)
 report=(out/"S6_attack_round49.md").read_text(encoding="utf-8")
 review=(out/"S6_round49_geometric_review.md").read_text(encoding="utf-8")
 assert "η∈[0,1/64]完整关闭" in report and "S2<q(r+Δz)" in review
 assert "36. " in review and "一般" not in ""
 result={"result":"passed","new_closed_subclass":local["new_closed_subclass"],
  "new_totals":{"UNSAT":0,"algebraic_identities":6,"exact_positive_constants":21,"geometric_review_items":36},
  "historical_round48":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_source_bytes":"matched","own_full_entry_replayed":False},
  "inherited_round43":{"archive_sha256":old43,"cited_proof_and_scalar_source_bytes":"matched",
   "scalar_checker_replayed_separately":True,"scalar_algebraic_identities":8,
   "scalar_polynomial_reconstructions":2,"scalar_positive_coefficients":20,"scalar_constants":13,
   "entire_old_verification_entry_replayed":False,"counted_as_new_results":False},
  "global_axis_C":"Combining rounds43,46,49: C is non-axis-aligned in every remaining mechanism",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round49_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

