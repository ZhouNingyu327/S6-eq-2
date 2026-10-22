"""Re-run new near-G5 exclusion checks from immutable sources."""
from pathlib import Path
import hashlib,itertools,json,platform,subprocess,sys,time
import sympy,z3

CHECKS={
    'check_round6_right_trace.py':('round6_right_trace_checks.json',2),
    'check_round6_near_gap.py':('round6_near_gap_checks.json',4),
}

def main():
    root=Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    print('Immutable file hashes PASS',flush=True)
    choices=[p for p in itertools.product((2,3),(3,4),(4,1)) if len(set(p))==3]
    assert choices==[(2,3,4),(2,3,1),(2,4,1),(3,4,1)],choices
    remaining=[p for p in choices if p not in [(2,3,4),(3,4,1)]]
    assert all(p[0]==2 and p[2]==1 for p in remaining)
    print('All selected corner-midpoint matchings PASS',flush=True)
    records=[];runs=[];start=time.time()
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
        assert all(q['result']=='unsat' for q in queries)
        records.extend(queries);runs.append({'script':script,'queries':count,'log':script+'.log'})
    assert len(records)==6
    nonlinear=sum('nonlinear' in q['arithmetic'] for q in records)
    assert nonlinear==2
    data={'status':'all exact checks passed','round6_unsat_queries':6,'nonlinear_real_queries':2,
          'linear_real_queries':4,'scripts':runs,'queries':records,'seconds':time.time()-start,
          'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sympy.__version__,
          'matchings':choices,'remaining_far_matchings':remaining,
          'scope':'near G5 k=1 fully excluded for all a>2 together with round 5',
          'global_bound_unchanged':'2 <= S(6) < 2.03; S(6)=2 remains unproved'}
    (root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ['queries','scripts']},indent=2),flush=True)

if __name__=='__main__':main()
