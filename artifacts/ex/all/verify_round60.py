"""Round60 mathematical entry and precise historical byte dependencies."""
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
 59:'1a59ba18e75e5b808b0252ec53373fbc302baf8344dc9bc02a6a7384e4f7e3e8',
 51:'008b7bad2ff1a180a0d601784fee35899367de29d0c5e1c3e83394415ccf52ee',
 49:'f3edbdfc9425bf9631aaff37d48de32407ef8f646f55833b1b27869fe576d37e',
 46:'069a77ec47e8883819577a7d5f7a7c9075b040950b24b5d5068bedfe54164113',
 43:'9345f68c9797f4f10cf409249111bc38713f73afc5b0924d1223550b0c0ec0f1',
 42:'30bcf492a2d35fff85de5ec5547302f2d758d883c85b5a1917bd60e0db2ac2f1',
 40:'8d86cca0b528fa3d61a01d4e6d74c5ef450ce475be26baef02b2444f7be20378'}
 blob=(out/'S6_round59_verification.zip').read_bytes()
 for n in range(59,39,-1):
  with zipfile.ZipFile(BytesIO(blob)) as z:
   if n in expected:
    assert sha(blob)==expected[n] and z.testzip() is None,n
    for name,digest in json.loads(z.read('manifest.json'))['files'].items():assert sha(z.read(name))==digest,(n,name)
    name=f'S6_attack_round{n}.md';assert z.read(name)==(out/name).read_bytes(),name
   if n>40:blob=z.read(f'S6_round{n-1}_verification.zip')
 p=subprocess.run([sys.executable,str(src/'check_round60.py')],cwd=cwd,capture_output=True,
  text=True,encoding='utf-8',errors='strict',env={**os.environ,'PYTHONIOENCODING':'utf-8'})
 (out/'check_round60.py.log').write_text(p.stdout+p.stderr,encoding='utf-8')
 assert p.returncode==0,(p.stdout,p.stderr)
 local=json.loads(p.stdout)
 assert (local['new_rational_inequalities'],local['new_polynomial_reconstructions'],local['new_positive_coefficients'],
  local['algebraic_identities'],local['positive_exact_constants'],local['UNSAT'])==(4,8,362,21,15,0)
 (out/'S6_round60_local_verification.json').write_text(json.dumps(local,indent=2),encoding='utf-8')
 report=(out/'S6_attack_round60.md').read_text(encoding='utf-8')
 review=(out/'S6_round60_geometric_review.md').read_text(encoding='utf-8')
 assert '全部负旋转情形不可能' in report and 'S(6)=2未解决' in report and '40. ' in review
 result={**local,'geometric_review_items':40,'historical_dependencies':{
  'rounds_hash_crc_manifest_cited_bytes':list(expected),'own_full_mathematical_entries_replayed':False},
  'global_bound':'2 <= S(6) < 2.03'}
 (out/'S6_round60_verification_result.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
