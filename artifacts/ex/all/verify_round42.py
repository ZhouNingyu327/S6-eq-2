"""Independent round42 entry; previous packet checked without its math replay."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 digest="d5272c7b668d70d674cb4746f181aa2dfea87f0d9249efc61accbc5b3761dec0"
 old=out/"S6_round41_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as archive:
  assert archive.testzip() is None
  for name in ("S6_attack_round40.md","S6_attack_round41.md"):
   assert archive.read(name)==(out/name).read_bytes()
  for name,h in json.loads(archive.read("manifest.json"))["files"].items():
   assert sha(archive.read(name))==h
 p=subprocess.run([sys.executable,str(src/"check_round42.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round42.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round42_local_verification.json").read_text(encoding="utf-8"))
 assert (local["UNSAT"],local["NRA"],local["LRA"])==(2,0,2)
 assert (local["algebraic_identities"],local["full_polynomial_identities"],
         local["nonnegative_rational_coefficients"],local["constant_count"])==(14,18,56,6)
 report=(out/"S6_attack_round42.md").read_text(encoding="utf-8")
 review=(out/"S6_round42_geometric_review.md").read_text(encoding="utf-8")
 assert "P1属于同一个原C" in report and "负旋转在这个新区间没有因此排除" in report
 assert "38. " in review and "整个G2和S(6)=2仍开放" in report
 result={"result":"passed",
  "scope":"Universal normalized seam P1 in original C; positive C double direct contact excluded for eta in [1/3,9/25]",
  "totals":{"UNSAT":2,"NRA":0,"LRA":2,"algebraic_identities":14,
   "full_polynomial_identities":18,"symbolic_identities":32,"constants":6,
   "whole_univariate_rational_expressions":9,"nonnegative_rational_coefficients":56,
   "geometric_review_items":38},
  "historical_round41":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_round40_round41_source_bytes":"matched","own_full_entry_replayed":False},
  "excluded_from_formal_replay":"Exploration scripts; no wide NRA, angle sampling, layout optimization or adaptive subdivision",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round42_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
