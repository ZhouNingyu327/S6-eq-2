"""Round54 local mathematics and exact historical dependency bytes."""
from pathlib import Path
from io import BytesIO
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
 if (cwd/"manifest.json").exists():
  for n,h in json.loads((cwd/"manifest.json").read_text(encoding="utf-8"))["files"].items():
   assert sha((cwd/n).read_bytes())==h,n
 expected={
 53:"14b7289d257af9e122b4e7bed6974745af400dac5b1f9868c37cdc06ede7bc2a",
 48:"b3356679170d983a0a4be373398d3413ffecfd4da0dde58cf16af13718ccbbce",
 46:"069a77ec47e8883819577a7d5f7a7c9075b040950b24b5d5068bedfe54164113",
 45:"89b5200955389aa456640beaefd5755d25a993b8024ada108c3610d9d7e4981e"}
 blob=(out/"S6_round53_verification.zip").read_bytes()
 for n in range(53,44,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:
   if n in expected:
    assert sha(blob)==expected[n],n
    assert z.testzip() is None,n
    for name,h in json.loads(z.read("manifest.json"))["files"].items():assert sha(z.read(name))==h,(n,name)
    name=f"S6_attack_round{n}.md";assert z.read(name)==(out/name).read_bytes(),name
   if n>45:blob=z.read(f"S6_round{n-1}_verification.zip")
 p=subprocess.run([sys.executable,str(src/"check_round54.py")],cwd=cwd,
  capture_output=True,text=True,encoding="utf-8",errors="strict",
  env={**os.environ,"PYTHONIOENCODING":"utf-8"})
 (out/"check_round54.py.log").write_text(p.stdout+p.stderr,encoding="utf-8")
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads(p.stdout)
 (out/"S6_round54_local_verification.json").write_text(json.dumps(local,indent=2),encoding="utf-8")
 assert (local["polynomial_reconstructions"],local["strictly_positive_rational_coefficients"],
         local["algebraic_identities"],local["positive_exact_constants"],local["UNSAT"])==(6,111,11,12,0)
 report=(out/"S6_attack_round54.md").read_text(encoding="utf-8")
 review=(out/"S6_round54_geometric_review.md").read_text(encoding="utf-8")
 assert "44.8529862458" in report and "44.7669953521" in report and "整个G2和S(6)=2开放" in report
 assert "36. " in review
 result={**local,"geometric_review_items":36,
  "historical_dependencies":{"rounds_hash_crc_manifest_cited_bytes":list(expected),
   "own_full_mathematical_entries_replayed":False},
  "global_bound":"2 <= S(6) < 2.03"}
 (out/"S6_round54_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps(result,indent=2))
if __name__=="__main__":main()

