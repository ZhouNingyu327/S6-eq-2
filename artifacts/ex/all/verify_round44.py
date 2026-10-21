"""Round44 independent exact checks and cited immutable-source matching."""
from pathlib import Path
import hashlib,io,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 digest="9345f68c9797f4f10cf409249111bc38713f73afc5b0924d1223550b0c0ec0f1"
 old=out/"S6_round43_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as archive:
  assert archive.testzip() is None
  for name in ("S6_attack_round42.md","S6_attack_round43.md"):
   assert archive.read(name)==(out/name).read_bytes()
  for name,h in json.loads(archive.read("manifest.json"))["files"].items():
   assert sha(archive.read(name))==h
  nested=archive.read("S6_round42_verification.zip")
  assert sha(nested)=="30bcf492a2d35fff85de5ec5547302f2d758d883c85b5a1917bd60e0db2ac2f1"
  with zipfile.ZipFile(io.BytesIO(nested)) as a42:
   assert a42.testzip() is None
   for name in ("S6_attack_round40.md","S6_attack_round41.md"):
    assert a42.read(name)==(out/name).read_bytes()
 p=subprocess.run([sys.executable,str(src/"check_round44.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round44.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads((out/"S6_round44_local_verification.json").read_text(encoding="utf-8"))
 assert (local["algebraic_identities"],local["constant_count"],local["UNSAT"])==(17,7,0)
 report=(out/"S6_attack_round44.md").read_text(encoding="utf-8")
 review=(out/"S6_round44_geometric_review.md").read_text(encoding="utf-8")
 assert "没有完整关闭任何新的接合机制" in report and "保留Yμ=0" in report
 assert "32. " in review and "整个G2及S(6)=2开放" in report
 result={"result":"passed","scope":local["scope"],
  "totals":{"UNSAT":0,"algebraic_identities":17,"constants":7,"geometric_review_items":32},
  "historical_round43":{"sha256":digest,"crc":"passed","manifest":"passed",
   "cited_round40_round41_round42_round43_source_bytes":"matched",
   "own_full_entry_replayed":False,"nested_round42_full_entry_replayed":False},
  "method":"Actual supports, open wedge, closedness, convex interpolation and exact rational identities",
  "not_proved":local["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round44_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
