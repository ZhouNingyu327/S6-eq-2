"""Independent entry point: exact round-15 certificates and small queries."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy,z3

CHECKS={
    'check_round15_angle_certificate.py':'round15_angle_certificate_checks.json',
    'check_round15_rotation.py':'round15_rotation_checks.json',
    'check_round15_small_top_angle.py':'round15_small_top_checks.json',
    'check_round15_junction_convexity.py':'round15_junction_convexity_checks.json',
}

def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/'manifest.json').read_text(encoding='utf-8'))
    for name,digest in manifest['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    previous=root/'S6_round14_verification.zip'
    assert hashlib.sha256(previous.read_bytes()).hexdigest()==(
        '83825acd9aca7eafd806f503914198f93f4654b7a93ad86be82310c669f09789')
    start=time.time();results={};queries=[]
    for script,filename in CHECKS.items():
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,
                           text=True,encoding='utf-8',errors='replace')
        (root/(script+'.log')).write_text(run.stdout+run.stderr,encoding='utf-8')
        assert run.returncode==0,(script,run.stdout+run.stderr)
        data=json.loads((root/filename).read_text(encoding='utf-8'))
        assert data['passed'] is True
        results[script]=data
        for row in data.get('queries',[]):
            assert row['result']=='unsat',row
            queries.append(row)
        print(script,'PASS',flush=True)
    angles=results['check_round15_angle_certificate.py']
    top=results['check_round15_small_top_angle.py']
    assert angles['bernstein_coefficient_count']==65
    assert angles['quadratic_endpoint_count']==2
    assert top['coefficient_count']==12
    assert top['proved_scope'].endswith('t3>1/32')
    assert len(queries)==9
    assert results['check_round15_junction_convexity.py']['identities_verified']==3
    record={'status':'all exact checks passed','new_NRA_queries':9,
            'rational_Bernstein_coefficients':77,'positive_quadratic_endpoints':2,
            'junction_convex_combination_identities':3,
            'proved_scope':'near G2 three-meet / F horizontal empty: 3/14<t2<5/7, t3>1/32, rho_C>33/980; z+2rho_C>t2; Q(1) in C',
            'not_proved':'remaining near final configuration; entire G2; G3; G4; S(6)=2',
            'global_bound_unchanged':'2 <= S(6) < 2.03',
            'previous_archive_sha256':hashlib.sha256(previous.read_bytes()).hexdigest(),
            'previous_archive_policy':'integrity checked, preserved unchanged; nested historical queries not rerun',
            'python':platform.python_version(),'sympy':sympy.__version__,'z3':z3.get_version_string(),
            'seconds':time.time()-start,'queries':queries}
    (root/'verification_result.json').write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in record.items() if k!='queries'},ensure_ascii=False,indent=2),flush=True)

if __name__=='__main__':main()
