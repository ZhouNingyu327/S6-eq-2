"""Fresh round-five checks; saved query outputs are never trusted."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy,z3

CHECKS={
    'check_round5_noouter_linear.py':('round5_noouter_linear_checks.json',2),
    'check_round5_cascade.py':('round5_cascade_checks.json',5),
    'check_round5_polynomial.py':('round5_polynomial_checks.json',4),
}

def main():
    root=Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    print('Immutable file hashes PASS',flush=True)
    records=[]; runs=[]; start=time.time()
    for script,(result_name,count) in CHECKS.items():
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True,
                           encoding='utf-8',errors='replace')
        log=run.stdout+run.stderr
        (root/(script+'.log')).write_text(log,encoding='utf-8')
        print(script,'PASS' if run.returncode==0 else 'FAIL',flush=True)
        if run.returncode:print(log,flush=True);raise SystemExit(run.returncode)
        data=json.loads((root/result_name).read_text(encoding='utf-8'))
        queries=data['queries'] if isinstance(data,dict) else data
        assert len(queries)==count,(script,len(queries))
        assert all(q['result']=='unsat' for q in queries),script
        records.extend(queries);runs.append({'script':script,'queries':count,'log':script+'.log'})
    assert len(records)==11
    nonlinear=sum('nonlinear' in q['arithmetic'] for q in records)
    assert nonlinear==9
    data={'status':'all exact checks passed','round5_unsat_queries':11,
          'nonlinear_real_queries':9,'linear_real_queries':2,'scripts':runs,'queries':records,
          'seconds':time.time()-start,'python':platform.python_version(),
          'z3':z3.get_version_string(),'sympy':sympy.__version__,
          'scope':'near W, G5 k=1, all three non-bottom outer sides meet: excluded for all a>2',
          'global_bound_unchanged':'2 <= S(6) < 2.03; S(6)=2 remains unproved'}
    (root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ['queries','scripts']},indent=2),flush=True)

if __name__=='__main__':main()
