"""Fresh replay of the conditional residual-gap lemmas."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile

root=Path(__file__).resolve().parent
manifest=json.loads((root/'manifest.json').read_text(encoding='utf-8'))
for name,digest in manifest['files'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
with tempfile.TemporaryDirectory(prefix='S6_gap_phase_') as folder:
    folder=Path(folder)
    for name in ['check_round16_gap_phase.py','check_round14_junction.py']:
        shutil.copy2(root/name,folder/name)
    run=subprocess.run([sys.executable,str(folder/'check_round16_gap_phase.py')],
        cwd=folder,capture_output=True,text=True,encoding='utf-8',errors='replace')
    assert run.returncode==0,run.stdout+run.stderr
    data=json.loads((folder/'round16_gap_phase_checks.json').read_text(encoding='utf-8'))
    assert data['UNSAT_count']==8 and len(data['queries'])==8
    assert all(q['result']=='unsat' for q in data['queries'])
    assert data['NRA_queries']==7 and data['LRA_queries']==1
    assert data['barycentric_identities']==3 and data['triangle_determinant_identity']==1
data['verification']='PASS'
(root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({'verification':'PASS','queries_UNSAT':8,
    'scope':data['scope'],'not_proved':data['not_proved']},ensure_ascii=False,indent=2))
