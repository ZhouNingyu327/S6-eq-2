"""Re-run all round-four exact queries, trusting no saved query result."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy,z3

CHECKS={
    'check_round4_overlap.py':('round4_overlap_checks.json',2),
    'check_round4_sameedge.py':('round4_sameedge_checks.json',4),
    'check_round4_nearleft.py':('round4_nearleft_checks.json',2),
    'check_round4_topcontact.py':('round4_topcontact_checks.json',2),
    'check_round4_corner_product.py':('round4_corner_product_checks.json',3),
    'check_round4_star_parabola.py':('round4_star_parabola_checks.json',3),
    'check_round4_noouter.py':('round4_noouter_checks.json',3),
    'check_round4_far.py':('round4_far_checks.json',1),
}


def main():
    root=Path(__file__).resolve().parent
    manifest=root/'manifest.json'
    assert manifest.exists(),'manifest.json is required'
    for name,digest in json.loads(manifest.read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name+' differs from manifest'
    print('Immutable file hashes PASS',flush=True)
    records=[];runs=[];start=time.time()
    for script,(result_name,count) in CHECKS.items():
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True,
                           encoding='utf-8',errors='replace')
        log=run.stdout+run.stderr
        (root/(script+'.log')).write_text(log,encoding='utf-8')
        print(script,'PASS' if run.returncode==0 else 'FAIL',flush=True)
        if run.returncode:
            print(log,flush=True);raise SystemExit(run.returncode)
        queries=json.loads((root/result_name).read_text(encoding='utf-8'))
        assert len(queries)==count,(script,len(queries))
        assert all(q['result']=='unsat' for q in queries),script
        records.extend(queries);runs.append({'script':script,'queries':count,'log':script+'.log'})
    assert len(records)==20,len(records)
    nonlinear=sum('nonlinear' in q['arithmetic'] for q in records)
    assert nonlinear==13,nonlinear
    data={'status':'all exact checks passed','round4_unsat_queries':20,'nonlinear_real_queries':nonlinear,
          'linear_real_queries':20-nonlinear,'scripts':runs,'queries':records,'seconds':time.time()-start,
          'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sympy.__version__,
          'scope':'G5 k=1 partial continuous exclusions and strengthened lemmas; S(6)=2 remains unproved',
          'global_bound_unchanged':'2 <= S(6) < 2.03'}
    (root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ['queries','scripts']},indent=2),flush=True)


if __name__=='__main__':main()
