"""Independent round41 entry with unchanged round40 dependency."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 digest="8d86cca0b528fa3d61a01d4e6d74c5ef450ce475be26baef02b2444f7be20378"
 old=out/"S6_round40_verification.zip";assert sha(old.read_bytes())==digest
 with zipfile.ZipFile(old) as archive:
  assert archive.testzip() is None
  assert archive.read("S6_attack_round40.md")==(out/"S6_attack_round40.md").read_bytes()
  for name,h in json.loads(archive.read("manifest.json"))["files"].items():
   assert sha(archive.read(name))==h
 for name in ("check_round41_geometry.py","check_round41_certificates.py"):
  proc=subprocess.run([sys.executable,str(src/name)],cwd=cwd,capture_output=True,
   text=True,encoding="utf-8",errors="strict",env={**os.environ,"PYTHONIOENCODING":"utf-8"})
  (out/(name+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
  assert proc.returncode==0,(name,proc.stdout,proc.stderr)
 geometry=json.loads((out/"S6_round41_geometry_verification.json").read_text(encoding="utf-8"))
 cert=json.loads((out/"S6_round41_certificate_verification.json").read_text(encoding="utf-8"))
 assert geometry["query_count"]==8 and all(x["result"]=="unsat" for x in geometry["queries"])
 assert geometry["identity_count"]==10 and geometry["constant_count"]==12
 assert cert["nonnegative_rational_coefficients"]==219 and cert["polynomial_identities"]==9
 report=(out/"S6_attack_round41.md").read_text(encoding="utf-8")
 review=(out/"S6_round41_geometric_review.md").read_text(encoding="utf-8")
 assert "sinθ≥12/17" in report and "整个三相接及S(6)=2仍开放" in report
 assert "36. " in review
 result={
  "result":"passed",
  "scope":"Direct Q2/QU excluded for both C rotations with sin(theta)>=12/17; repeated-TOPmid top seam forced into C",
  "totals":{"UNSAT":8,"NRA":6,"LRA":2,"symbolic_identities":19,"constants":12,
            "whole_parameter_charts":9,"nonnegative_rational_coefficients":219,
            "geometric_review_items":36},
  "historical_round40":{"sha256":digest,"crc":"passed","manifest":"passed",
                        "cited_source_bytes":"matched","own_full_entry_replayed":False},
  "not_proved":"Smaller C angles in double direct contact, the other three contact cases, entire three meetings, G2 or S(6)=2",
  "excluded_from_formal_replay":"one UNKNOWN probe and slow broad NRA probes; main local proofs replay exact coefficients",
  "global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round41_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
