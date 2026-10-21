"""Run all exact checks independently. No saved result is trusted as proof."""
from pathlib import Path
import json
import hashlib
import platform
import subprocess
import sys
import time
import z3
import sympy


def main():
    root=Path(__file__).resolve().parent
    manifest=root/'manifest.json'
    if manifest.exists():
        for name,digest in json.loads(manifest.read_text(encoding='utf-8'))['files'].items():
            assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest, name+' differs from manifest'
        print('Immutable file hashes PASS',flush=True)
    scripts=['check_g5.py','check_round3_linear.py','check_round3_triangle.py',
             'check_round3_onegap.py','check_round3_weighted.py','check_one_mid_counterexample.py',
             'check_g5_k1_structure.py']
    checks=[];start=time.time()
    for script in scripts:
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True,encoding='utf-8',errors='replace')
        log=run.stdout+run.stderr
        (root/(script+'.log')).write_text(log,encoding='utf-8')
        print(script,'PASS' if run.returncode==0 else 'FAIL',flush=True)
        checks.append({'script':script,'exit_code':run.returncode,'log':script+'.log'})
        if run.returncode:
            print(log,flush=True)
            raise SystemExit(run.returncode)
    records=[]
    for name in ['round3_linear_checks.json','round3_triangle_checks.json',
                 'round3_onegap_checks.json','round3_weighted_checks.json']:
        records.extend(json.loads((root/name).read_text()))
    unsat=[record for record in records if record['result']=='unsat']
    assert len(unsat)==14, len(unsat)
    assert json.loads((root/'star_nra_check.json').read_text())['result']=='unsat'
    assert json.loads((root/'one_mid_grid_counterexample.json').read_text())['verification']=='exact Fraction arithmetic passed'
    conditional=json.loads((root/'g5_k1_structure_checks.json').read_text())
    assert len([record for record in conditional if record['result']=='unsat'])==3
    data={'status':'all exact checks passed','round3_unsat_queries':len(unsat),
          'background_star_unsat_query':1,'local_k1_counterexample':'exact Fraction arithmetic passed',
          'conditional_k1_unsat_queries':3,'scripts':checks,'seconds':time.time()-start,
          'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sympy.__version__,
          'scope':'G5 k=0 continuous proof; not a proof of S(6)=2'}
    (root/'verification_result.json').write_text(json.dumps(data,indent=2),encoding='utf-8')
    print(json.dumps(data,indent=2),flush=True)


if __name__=='__main__':
    main()
