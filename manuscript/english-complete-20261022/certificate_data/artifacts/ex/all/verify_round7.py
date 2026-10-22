"""Fresh independent round-seven verifier with unchanged historical background."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy as sp
import z3

CHECKS={
    'check_round7_upper_traces.py':('round7_upper_trace_checks.json',4),
    'check_round7_far.py':('round7_far_checks.json',5),
}

def main():
    root=Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    print('Immutable file hashes PASS',flush=True)
    K=8+3/sp.sqrt(2);mu_star=(10*K-sp.sqrt(K*K-99))/99
    assert sp.simplify((K-10*mu_star)**2-mu_star**2+1)==0
    print('Exact conditional root identity PASS',flush=True)
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
    assert len(records)==9
    assert sum('nonlinear' in q['arithmetic'] for q in records)==4
    data={'status':'all exact checks passed','round7_unsat_queries':9,'nonlinear_real_queries':4,
          'linear_real_queries':5,'scripts':runs,'queries':records,'seconds':time.time()-start,
          'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sp.__version__,
          'scope':'far G5 k=1: F strictly interior, nonbottom corners meet, C horizontal/up redundant',
          'all_G5_conditional_a_bound':str(sp.N(2*mu_star,35)),
          'global_bound_unchanged':'2 <= S(6) < 2.03; S(6)=2 remains unproved'}
    (root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ['queries','scripts']},indent=2),flush=True)

if __name__=='__main__':main()
