"""Independent round43 entry; historical round42 bytes preserved."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 digest="30bcf492a2d35fff85de5ec5547302f2d758d883c85b5a1917bd60e0db2ac2f1"
 old=out/"S6_round42_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as archive:
  assert archive.testzip() is None
  assert archive.read("S6_attack_round42.md")==(out/"S6_attack_round42.md").read_bytes()
  for name,h in json.loads(archive.read("manifest.json"))["files"].items():
   assert sha(archive.read(name))==h
 p=subprocess.run([sys.executable,str(src/"check_round43.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round43.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round43_local_verification.json").read_text(encoding="utf-8"))
 assert (local["UNSAT"],local["algebraic_identities"],local["full_polynomial_identities"],
         local["strictly_positive_rational_coefficients"],local["constant_count"])==(0,8,2,20,13)
 report=(out/"S6_attack_round43.md").read_text(encoding="utf-8")
 review=(out/"S6_round43_geometric_review.md").read_text(encoding="utf-8")
 assert "两种旋转方向都包括" in report and "0≤η≤1/8" in report
 assert "34. " in review and "整个G2和S(6)=2仍未证明" in report
 result={"result":"passed",
  "scope":local["scope"],
  "totals":{"UNSAT":0,"algebraic_identities":8,"full_polynomial_identities":2,
   "symbolic_identities":10,"constants":13,"whole_univariate_rational_expressions":1,
   "strictly_positive_rational_coefficients":20,"geometric_review_items":34},
  "historical_round42":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_source_bytes":"matched","own_full_entry_replayed":False},
  "formal_replay":"Exact algebra and polynomial identities; no solver queries, angle samples or subdivision",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round43_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
