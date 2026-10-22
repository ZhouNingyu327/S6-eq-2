"""Round48 geometric reductions: exact algebra, chain check and source bytes."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for n,h in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/n).read_bytes())==h,n
 digest="6e55e66a5dbccdbfa33695bf213e598895e4b3abee2f6c4e3597686563fad1fc"
 old=out/"S6_round47_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as z:
  assert z.testzip() is None
  for n,h in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(n))==h
  assert z.read("S6_attack_round47.md")==(out/"S6_attack_round47.md").read_bytes()
 p=subprocess.run([sys.executable,str(src/"check_round48.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round48.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round48_local_verification.json").read_text(encoding="utf-8"))
 assert local["algebraic_identities"]==15 and local["four_face_availability_patterns_checked"]==16
 assert local["mod2_boundary_cycle_solutions"]==[[0,1,0,1],[1,0,1,0]]
 report=(out/"S6_attack_round48.md").read_text(encoding="utf-8")
 review=(out/"S6_round48_geometric_review.md").read_text(encoding="utf-8")
 assert "没有完整排除剩余三个机制中的任何一个" in report and "当且仅当" in report
 assert "40. " in review
 result={"result":"passed","scope":local["scope"],
  "totals":{"UNSAT":0,"algebraic_identities":15,"exact_mod2_solutions":2,
   "four_face_availability_patterns":16,"geometric_review_items":40},
  "geometric_proof_boundary":"CAS checks support formulas and finite mod-2 algebra; the report independently proves the fan, boundary contraction and triangulation-label lemmas",
  "historical_round47":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_source_bytes":"matched","own_full_entry_replayed":False},
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round48_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

