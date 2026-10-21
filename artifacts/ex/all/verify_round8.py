"""Fresh round-eight checks, with a separate exact rational certificate."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy as sp
import z3

CHECKS={
    'check_round8_two_corners.py':('round8_two_corner_checks.json',1),
    'check_round8_far_closure.py':('round8_far_closure_checks.json',7),
}

def main():
    root=Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    print('Immutable file hashes PASS',flush=True)
    records=[];runs=[];start=time.time();cert=None
    for script,(result_name,count) in CHECKS.items():
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True,
                           encoding='utf-8',errors='replace')
        log=run.stdout+run.stderr
        (root/(script+'.log')).write_text(log,encoding='utf-8')
        print(script,'PASS' if run.returncode==0 else 'FAIL',flush=True)
        if run.returncode:print(log,flush=True);raise SystemExit(run.returncode)
        data=json.loads((root/result_name).read_text(encoding='utf-8'))
        queries=data['queries'] if isinstance(data,dict) else data
        if isinstance(data,dict):cert=data['rational_certificate']
        assert len(queries)==count,(script,len(queries))
        assert all(q['result']=='unsat' for q in queries)
        records.extend(queries);runs.append({'script':script,'queries':count,'log':script+'.log'})
    assert len(records)==8
    assert sum('nonlinear' in q['arithmetic'] for q in records)==2
    assert cert['box_count']==45 and len(cert['records'])==45 and cert['max_depth']==10
    from fractions import Fraction
    assert all(Fraction(z['minimum_exact_bernstein_coefficient'])>=0 for z in cert['records'])
    data={'status':'all exact checks passed','round8_unsat_queries':8,'nonlinear_real_queries':2,
          'linear_real_queries':6,'independent_rational_boxes':45,'rational_certificate_max_depth':10,
          'scripts':runs,'queries':records,'seconds':time.time()-start,
          'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sp.__version__,
          'scope':'remaining far G5 k=1 impossible for every a>2; all G5 now excluded',
          'geometric_corollary':'exactly one unit square contains the target center',
          'global_bound_unchanged':'2 <= S(6) < 2.03; S(6)=2 remains unproved'}
    (root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ['queries','scripts']},indent=2),flush=True)

if __name__=='__main__':main()
