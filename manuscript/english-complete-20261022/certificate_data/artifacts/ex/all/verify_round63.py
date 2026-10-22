"""Round63 mathematical entry, with exact historical byte dependencies."""
from pathlib import Path
from io import BytesIO
import hashlib,json,os,subprocess,sys,zipfile
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 cwd=Path.cwd();src=Path(__file__).resolve().parent
 out=cwd/'outputs' if (cwd/'outputs').is_dir() else cwd
 if (cwd/'manifest.json').exists():
  for name,digest in json.loads((cwd/'manifest.json').read_text(encoding='utf-8'))['files'].items():
   assert sha((cwd/name).read_bytes())==digest,name
 expected={
 62:'ab2f1ad9edc6dacc23e7965248eb191f0dcfe00736babd68151be9420f942004',
 48:'b3356679170d983a0a4be373398d3413ffecfd4da0dde58cf16af13718ccbbce',
 61:'35167c10c2a439730135ec51161c1261fe84236e21c1021583b0973a7b300e9c',
 60:'1f1e39e511b99195bc09c97d1b17b06a66c39df4c1ec3e8f0e8aa430357f1f47',
 49:'f3edbdfc9425bf9631aaff37d48de32407ef8f646f55833b1b27869fe576d37e',
 46:'069a77ec47e8883819577a7d5f7a7c9075b040950b24b5d5068bedfe54164113',
 42:'30bcf492a2d35fff85de5ec5547302f2d758d883c85b5a1917bd60e0db2ac2f1'}
 blob=(out/'S6_round62_verification.zip').read_bytes()
 for n in range(62,41,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:
   if n in expected:
    assert sha(blob)==expected[n] and z.testzip() is None,n
    for name,digest in json.loads(z.read('manifest.json'))['files'].items():assert sha(z.read(name))==digest,(n,name)
    name=f'S6_attack_round{n}.md';assert z.read(name)==(out/name).read_bytes(),name
   if n>42:blob=z.read(f'S6_round{n-1}_verification.zip')
 p=subprocess.run([sys.executable,str(src/'check_round63.py')],cwd=cwd,capture_output=True,
  text=True,encoding='utf-8',errors='strict',env={**os.environ,'PYTHONIOENCODING':'utf-8'})
 (out/'check_round63.py.log').write_text(p.stdout+p.stderr,encoding='utf-8')
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads(p.stdout)
 assert (local['new_algebraic_identities'],local['replayed_algebraic_identities'],
  local['positive_exact_comparisons'],local['new_polynomial_certificates'],local['UNSAT'])==(7,8,14,0,0)
 (out/'S6_round63_local_verification.json').write_text(json.dumps(local,indent=2),encoding='utf-8')
 report=(out/'S6_attack_round63.md').read_text(encoding='utf-8')
 review=(out/'S6_round63_geometric_review.md').read_text(encoding='utf-8')
 assert '整个右W桥接排除' in report and 'S(6)=2仍未解决' in report and '40. ' in review
 result={**local,'geometric_review_items':40,'historical_dependencies':{
  'rounds_hash_crc_manifest_cited_bytes':list(expected),'own_full_mathematical_entries_replayed':False},
  'global_bound':'2 <= S(6) < 2.03'}
 (out/'S6_round63_verification_result.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
