"""Independent entry point for the round-14 proof and selected input audits."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy as sp
import z3

CHECKS={
 'check_round14_junction.py':('round14_junction_checks.json',4),
 'check_round14_bridge.py':('round14_bridge_checks.json',6),
 'check_round14_margin.py':('round14_margin_checks.json',5),
 'check_round14_J_certificate.py':('round14_J_certificate_checks.json',0),
 'check_round14_relaxation_example.py':('round14_relaxation_example.json',0),
 'check_round3_linear.py':('round3_linear_checks.json',4),
 'check_round3_triangle.py':('round3_triangle_checks.json',2),
 'check_round3_weighted.py':('round3_weighted_checks.json',4),
 'check_round5_polynomial.py':('round5_polynomial_checks.json',4),
}

def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/'manifest.json').read_text(encoding='utf-8'))
    for name,digest in manifest['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    start=time.time();queries=[];new=[];certificate=None;example=None
    for script,(filename,count) in CHECKS.items():
        result=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,
                              text=True,encoding='utf-8',errors='replace')
        (root/(script+'.log')).write_text(result.stdout+result.stderr,encoding='utf-8')
        assert result.returncode==0,(script,result.stdout+result.stderr)
        data=json.loads((root/filename).read_text(encoding='utf-8'))
        if count:
            records=data['queries'] if isinstance(data,dict) else data
            assert isinstance(records,list)
            assert not any(r.get('result') in ['sat','unknown'] for r in records)
            rows=[r for r in records if r.get('result')=='unsat']
            assert len(rows)==count,(script,len(rows),count)
            queries.extend(rows)
            if 'round14' in script:new.extend(rows)
        elif 'certificate' in script:
            assert data['result']=='passed' and data['rectangles']==12 and data['rational_coefficients']==316
            certificate=data
        elif 'example' in script:example=data
        print(script,'PASS',flush=True)
    assert len(new)==15 and len(queries)==29
    assert certificate and example
    record={'status':'all exact checks passed','new_exact_queries':15,'new_NRA_queries':14,'new_LRA_queries':1,
            'input_audit_queries':14,'total_recomputed_queries':29,
            'J_certificate':certificate,'exact_relaxation_counterexample':example,
            'proved_scope':'near right/top meet and F horizontal empty: left gap excluded; W negative vertical trace empty; C contains interior junction',
            'not_proved':'remaining near three-meet junction configuration; entire G2; G3; G4; S(6)=2',
            'global_bound_unchanged':'2 <= S(6) < 2.03',
            'python':platform.python_version(),'sympy':sp.__version__,'z3':z3.get_version_string(),
            'seconds':time.time()-start,'queries':queries}
    (root/'verification_result.json').write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in record.items() if k!='queries'},ensure_ascii=False,indent=2),flush=True)

if __name__=='__main__':main()
