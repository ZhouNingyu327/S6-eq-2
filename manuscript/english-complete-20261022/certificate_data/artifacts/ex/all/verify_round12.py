"""Recompute exact checks for the theorem that the noncentral extra hosts a midpoint."""
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys
import time
import sympy as sp
import z3


CHECKS = {
    'check_round12_inputs.py': ('round12_input_checks.json',3),
    'check_round11_polys.py': ('round11_polynomial_checks.json',0),
    'check_round11_far.py': ('round11_far_checks.json',14),
    'check_round12_far.py': ('round12_far_checks.json',3),
    'check_round12_near.py': ('round12_near_checks.json',12),
    'check_round12_shared.py': ('round12_shared_checks.json',4),
}


def main():
    root = Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest() == digest,name
    print('Immutable file hashes PASS',flush=True)
    records = []
    scripts = []
    new_records = []
    certificates = None
    start = time.time()
    for script,(name,count) in CHECKS.items():
        run = subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,
                             text=True,encoding='utf-8',errors='replace')
        log = run.stdout+run.stderr
        (root/(script+'.log')).write_text(log,encoding='utf-8')
        print(script,'PASS' if run.returncode == 0 else 'FAIL',flush=True)
        if run.returncode:
            print(log,flush=True)
            raise SystemExit(run.returncode)
        data = json.loads((root/name).read_text(encoding='utf-8'))
        if isinstance(data,dict):
            queries = data.get('queries',[])
            if 'rational_certificates' in data:
                certificates = data['rational_certificates']
            if script == 'check_round12_inputs.py':
                assert data['identities_and_classification']['reflection_orbits'] == 2
                assert len(data['identities_and_classification']['valid_midpoint_injections']) == 4
        else:
            queries = data
        assert len(queries) == count,(script,len(queries))
        assert all(row['result'] == 'unsat' for row in queries)
        records.extend(queries)
        if 'round12' in script:
            new_records.extend(queries)
        scripts.append({'script':script,'queries':count,'log':script+'.log'})
    assert len(new_records) == 22
    assert sum('nonlinear' in row['arithmetic'] for row in new_records) == 5
    assert len(records) == 36
    assert sum('nonlinear' in row['arithmetic'] for row in records) == 10
    assert certificates is not None and len(certificates) == 2
    for cert in certificates:
        assert len(cert['exact_bernstein_coefficients']) == cert['degree']+1
        assert all(sp.Rational(value) > 0 for value in cert['exact_bernstein_coefficients'])
    result = {'status':'all exact checks passed','round12_new_unsat_queries':22,
              'new_nonlinear_real_queries':5,'new_linear_real_queries':17,
              'round11_recomputed_unsat_queries':14,'total_recomputed_unsat_queries':36,
              'round11_recomputed_rational_certificates':2,
              'classification':'four injections, two reflection orbits; C-midpoint/F-no-midpoint and shared-midpoint cases all covered',
              'scope':'all a>2: F must host an outer midpoint, and C/F cannot share a midpoint; all G2 C-midpoint cases excluded',
              'remaining':'G2 with only F hosting a midpoint, G3, G4',
              'global_bound_unchanged':'2 <= S(6) < 2.03; S(6)=2 remains unproved',
              'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sp.__version__,
              'seconds':time.time()-start,'scripts':scripts,'queries':records}
    (root/'verification_result.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['queries','scripts']},indent=2),flush=True)


if __name__ == '__main__':
    main()
