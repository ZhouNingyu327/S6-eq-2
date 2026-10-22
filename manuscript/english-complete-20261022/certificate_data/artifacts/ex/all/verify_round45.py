"""Round45 independent entry for whole both-W-bridge exclusion."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 digest="e0866a351655832e707128d173c9fa9f0d1094afa56e9aa983b6fe85b9279c4b"
 old=out/"S6_round44_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as archive:
  assert archive.testzip() is None
  assert archive.read("S6_attack_round44.md")==(out/"S6_attack_round44.md").read_bytes()
  for name,h in json.loads(archive.read("manifest.json"))["files"].items():
   assert sha(archive.read(name))==h
 p=subprocess.run([sys.executable,str(src/"check_round45.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round45.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round45_local_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["constant_count"],local["UNSAT"])==(14,8,0)
 report=(out/"S6_attack_round45.md").read_text(encoding="utf-8")
 review=(out/"S6_round45_geometric_review.md").read_text(encoding="utf-8")
 assert "两个正轴都由原W桥接的整个机制不可能" in report
 assert "30. " in review and "整个G2及S(6)=2仍开放" in report
 result={"result":"passed","scope":local["scope"],
  "totals":{"UNSAT":0,"algebraic_identities":14,"constants":8,"geometric_review_items":30},
  "historical_round44":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_source_bytes":"matched","own_full_entry_replayed":False},
  "whole_mechanism_closed":"C contains neither Q2 nor QU; both positive axes bridged by W",
  "remaining_mechanisms":["C directly contains both Q2 and QU, remaining angles",
   "C directly contains Q2 but not QU","C directly contains QU but not Q2"],
  "method":"Actual W endpoints, strict rational span gap, concave quadratic endpoints, exact algebra",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round45_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
