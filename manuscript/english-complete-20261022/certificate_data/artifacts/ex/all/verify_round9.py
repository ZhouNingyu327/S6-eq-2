"""Fresh verifier for G1 three meets, preserving the all-G5 background."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy as sp
import z3

CHECKS={
    'check_round9_excess.py':('round9_excess_checks.json',2),
    'check_round9_three_meet.py':('round9_three_meet_checks.json',7),
}

def main():
    root=Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    print('Immutable file hashes PASS',flush=True)
    records=[];runs=[];start=time.time();certs=None
    for script,(result_name,count) in CHECKS.items():
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True,
                           encoding='utf-8',errors='replace')
        log=run.stdout+run.stderr
        (root/(script+'.log')).write_text(log,encoding='utf-8')
        print(script,'PASS' if run.returncode==0 else 'FAIL',flush=True)
        if run.returncode:print(log,flush=True);raise SystemExit(run.returncode)
        data=json.loads((root/result_name).read_text(encoding='utf-8'))
        queries=data['queries'] if isinstance(data,dict) else data
        if isinstance(data,dict):certs=data['rational_certificates']
        assert len(queries)==count,(script,len(queries))
        assert all(q['result']=='unsat' for q in queries)
        records.extend(queries);runs.append({'script':script,'queries':count,'log':script+'.log'})
    assert len(records)==9 and sum('nonlinear' in q['arithmetic'] for q in records)==4
    assert len(certs)==5
    for cert in certs:
        assert all(sp.Rational(v)>=0 for v in cert['exact_bernstein_coefficients'])
        assert len(cert['exact_bernstein_coefficients'])==cert['degree']+1
    data={'status':'all exact checks passed','round9_unsat_queries':9,'nonlinear_real_queries':4,
          'linear_real_queries':5,'independent_rational_polynomial_certificates':5,
          'scripts':runs,'queries':records,'seconds':time.time()-start,
          'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sp.__version__,
          'scope':'G1 exactly-three-meet impossible for every a>2',
          'background':'round8 excludes all G5; exactly one center host; exclusive central core corollary',
          'remaining':'G1 two meets; G2-G4 outside G5',
          'global_bound_unchanged':'2 <= S(6) < 2.03; S(6)=2 remains unproved'}
    (root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ['queries','scripts']},indent=2),flush=True)

if __name__=='__main__':main()
