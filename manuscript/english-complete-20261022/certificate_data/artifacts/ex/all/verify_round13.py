"""Recompute the new G2 subcase proofs and their exact input certificate."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy as sp
import z3


CHECKS={
    'check_round13_pair.py':('round13_pair_checks.json',1),
    'check_round13_closures.py':('round13_closure_checks.json',8),
    'check_round5_polynomial.py':('round5_polynomial_checks.json',4),
}


def main():
    root=Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    print('Immutable file hashes PASS',flush=True)
    start=time.time();queries=[];new=[];cert=None
    for script,(name,count) in CHECKS.items():
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True,encoding='utf-8',errors='replace')
        (root/(script+'.log')).write_text(run.stdout+run.stderr,encoding='utf-8')
        assert run.returncode==0,(script,run.stdout+run.stderr)
        data=json.loads((root/name).read_text(encoding='utf-8'))
        rows=data['queries'] if isinstance(data,dict) else data
        assert len(rows)==count and all(r['result']=='unsat' for r in rows)
        queries.extend(rows)
        if 'round13' in script:new.extend(rows)
        if script=='check_round13_pair.py':cert=data['certificate']
        print(script,'PASS',flush=True)
    assert len(new)==9 and sum('nonlinear' in r['arithmetic'] for r in new)==3
    assert len(queries)==13 and sum('nonlinear' in r['arithmetic'] for r in queries)==7
    assert cert['parameter_rectangles']==2 and cert['polynomial_identities']==4
    assert sum(r['coefficients'] for r in cert['records'])==266
    assert all(r['whole_rectangle_verified'] for r in cert['records'])
    result={'status':'all exact checks passed','new_queries':9,'new_nonlinear_real_queries':3,'new_linear_real_queries':6,
            'round5_recomputed_queries':4,'total_recomputed_queries':13,'pair_certificate':cert,
            'scope':'adjacent-corner inequality and G2 subcases only; near three meets with F horizontal nonempty excluded; near right/top meet with F horizontal empty forces H>S2 and F bottom gap>1; far top gap with F horizontal nonempty excluded; far three meets/F horizontal nonempty/J=0 excluded',
            'not_proved':'entire G2; G3; G4; S(6)=2','global_bound_unchanged':'2 <= S(6) < 2.03',
            'rejected_argument':'K<=5/6 and unconditional vanishing of a weak-corner middle trace are not used',
            'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sp.__version__,
            'seconds':time.time()-start,'queries':queries}
    (root/'verification_result.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='queries'},ensure_ascii=False,indent=2),flush=True)


if __name__=='__main__':main()
