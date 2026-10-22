"""Round56 independent local mathematics and frozen source byte checks."""
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
 55:"9b4698ac7ac3677c5c336b826f7e24cefd8dd2032b5e9b3f36ba83cd87b9ce87",
 54:"e01601d2fff41cf32377b84df68c2f0194c52fdb7fd2a5de6b362b067fd060c8",
 53:"14b7289d257af9e122b4e7bed6974745af400dac5b1f9868c37cdc06ede7bc2a",
 52:"6a0659e49b384382ccb1fa0c4fa7af76f772b10c1955279320dcbb949689b7b5",
 48:"b3356679170d983a0a4be373398d3413ffecfd4da0dde58cf16af13718ccbbce",
 46:"069a77ec47e8883819577a7d5f7a7c9075b040950b24b5d5068bedfe54164113",
 45:"89b5200955389aa456640beaefd5755d25a993b8024ada108c3610d9d7e4981e"}
 blob=(out/"S6_round55_verification.zip").read_bytes()
 for n in range(55,44,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:
   if n in expected:
    assert sha(blob)==expected[n],n
    assert z.testzip() is None,n
    for name,digest in json.loads(z.read("manifest.json"))["files"].items():
     assert sha(z.read(name))==digest,(n,name)
    name=f"S6_attack_round{n}.md";assert z.read(name)==(out/name).read_bytes(),name
   if n>45:blob=z.read(f"S6_round{n-1}_verification.zip")
 p=subprocess.run([sys.executable,str(src/"check_round56.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round56.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads(p.stdout)
 assert (local["new_polynomial_reconstructions"],local["new_positive_coefficients"],
  local["algebraic_identities"],local["positive_exact_constants"],local["UNSAT"])==(5,1016,11,14,0)
 (out/"S6_round56_local_verification.json").write_text(json.dumps(local,indent=2),encoding="utf-8")
 report=(out/"S6_attack_round56.md").read_text(encoding="utf-8")
 review=(out/"S6_round56_geometric_review.md").read_text(encoding="utf-8")
 assert "41.11209043916693" in report and "整个G2和S(6)=2未解决" in report
 assert "42. " in review
 result={**local,"geometric_review_items":42,
  "historical_dependencies":{"rounds_hash_crc_manifest_cited_bytes":list(expected),
   "own_full_mathematical_entries_replayed":False},
  "global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round56_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()
