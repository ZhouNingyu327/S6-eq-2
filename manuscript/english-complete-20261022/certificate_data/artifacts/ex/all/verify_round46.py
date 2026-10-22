"""Independent round46 exact certificate and historical-byte entry."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 digest="89b5200955389aa456640beaefd5755d25a993b8024ada108c3610d9d7e4981e"
 old=out/"S6_round45_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as archive:
  assert archive.testzip() is None
  assert archive.read("S6_attack_round45.md")==(out/"S6_attack_round45.md").read_bytes()
  for name,h in json.loads(archive.read("manifest.json"))["files"].items():
   assert sha(archive.read(name))==h
 p=subprocess.run([sys.executable,str(src/"check_round46.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round46.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round46_local_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["full_polynomial_identities"],
  local["strictly_positive_rational_coefficients"],local["constant_count"],local["UNSAT"])==(14,8,45,7,0)
 report=(out/"S6_attack_round46.md").read_text(encoding="utf-8")
 review=(out/"S6_round46_geometric_review.md").read_text(encoding="utf-8")
 assert "δC>τ/32" in report and "没有关闭第四十五轮留下的任何整个接合机制" in report
 assert "38. " in review and "不能把t1自动设成d" in report
 result={"result":"passed","scope":local["scope"],
  "totals":{"UNSAT":0,"algebraic_identities":14,"full_polynomial_identities":8,
   "symbolic_identities":22,"constants":7,"whole_rational_charts":4,
   "strictly_positive_rational_coefficients":45,"geometric_review_items":38},
  "historical_round45":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_source_bytes":"matched","own_full_entry_replayed":False},
  "excluded_from_formal_replay":"One 8-second UNKNOWN relaxed negative-C scalar probe; no layout search",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round46_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
