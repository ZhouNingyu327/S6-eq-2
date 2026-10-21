"""Round57 local mathematical entry plus precise historical byte dependencies."""
from pathlib import Path
from io import BytesIO
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for name,digest in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/name).read_bytes())==digest,name
 expected={
 56:"e0aa41e86beb9f172c255ab6969cf871fda9b2127ca633f77c2287387af2f659",
 55:"9b4698ac7ac3677c5c336b826f7e24cefd8dd2032b5e9b3f36ba83cd87b9ce87",
 53:"14b7289d257af9e122b4e7bed6974745af400dac5b1f9868c37cdc06ede7bc2a",
 52:"6a0659e49b384382ccb1fa0c4fa7af76f772b10c1955279320dcbb949689b7b5",
 47:"6e55e66a5dbccdbfa33695bf213e598895e4b3abee2f6c4e3597686563fad1fc",
 46:"069a77ec47e8883819577a7d5f7a7c9075b040950b24b5d5068bedfe54164113",
 42:"30bcf492a2d35fff85de5ec5547302f2d758d883c85b5a1917bd60e0db2ac2f1"}
 blob=(out/"S6_round56_verification.zip").read_bytes()
 for n in range(56,41,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:
   if n in expected:
    assert sha(blob)==expected[n] and z.testzip() is None,n
    for name,digest in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(name))==digest,(n,name)
    name=f"S6_attack_round{n}.md";assert z.read(name)==(out/name).read_bytes(),name
   if n>42:blob=z.read(f"S6_round{n-1}_verification.zip")
 p=subprocess.run([sys.executable,str(src/"check_round57.py")],cwd=cwd,capture_output=True,
  text=True,encoding="utf-8",errors="strict",env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round57.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads(p.stdout)
 assert (local["new_polynomial_reconstructions"],local["new_positive_coefficients"],
  local["algebraic_identities"],local["positive_exact_constants"],local["exact_failed_relaxation_checks"],local["UNSAT"])==(4,1017,12,7,3,0)
 (out/"S6_round57_local_verification.json").write_text(json.dumps(local,indent=2),encoding="utf-8")
 report=(out/"S6_attack_round57.md").read_text(encoding="utf-8")
 review=(out/"S6_round57_geometric_review.md").read_text(encoding="utf-8")
 assert "36.869898" in report and "整个G2和S(6)=2未解决" in report and "40. " in review
 result={**local,"geometric_review_items":40,"historical_dependencies":{
  "rounds_hash_crc_manifest_cited_bytes":list(expected),"own_full_mathematical_entries_replayed":False},
  "global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round57_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
