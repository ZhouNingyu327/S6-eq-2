"""Fresh verifier for the G2 far-corner partial theorem."""
from pathlib import Path
import hashlib,json,platform,subprocess,sys,time
import sympy as sp
import z3

CHECKS={
    'check_round11_polys.py':('round11_polynomial_checks.json',0),
    'check_round11_far.py':('round11_far_checks.json',14),
}


def main():
    root=Path(__file__).resolve().parent
    for name,digest in json.loads((root/'manifest.json').read_text(encoding='utf-8'))['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    print('Immutable file hashes PASS',flush=True)
    records=[];runs=[];certs=None;start=time.time()
    for script,(name,count) in CHECKS.items():
        run=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,text=True,
                           encoding='utf-8',errors='replace')
        log=run.stdout+run.stderr
        (root/(script+'.log')).write_text(log,encoding='utf-8')
        print(script,'PASS' if run.returncode==0 else 'FAIL',flush=True)
        if run.returncode:
            print(log,flush=True)
            raise SystemExit(run.returncode)
        data=json.loads((root/name).read_text(encoding='utf-8'))
        if isinstance(data,dict):
            certs=data['rational_certificates'];queries=data.get('queries',[])
        else:
            queries=data
        assert len(queries)==count,(script,len(queries))
        assert all(row['result']=='unsat' for row in queries)
        records.extend(queries)
        runs.append({'script':script,'queries':count,'log':script+'.log'})
    assert len(records)==14 and sum('nonlinear' in row['arithmetic'] for row in records)==5
    assert len(certs)==2
    for cert in certs:
        assert len(cert['exact_bernstein_coefficients'])==cert['degree']+1
        assert all(sp.Rational(v)>0 for v in cert['exact_bernstein_coefficients'])
    data={'status':'all exact checks passed','round11_unsat_queries':14,
          'nonlinear_real_queries':5,'linear_real_queries':9,
          'independent_rational_polynomial_certificates':2,
          'scripts':runs,'queries':records,'seconds':time.time()-start,
          'python':platform.python_version(),'z3':z3.get_version_string(),'sympy':sp.__version__,
          'scope':'G2 C-bottom far-weak-corner representative: F bottom and left-meet branches excluded; weak half-angle <=7/8 excluded',
          'remaining_in_this_representative':'left-upper gap F, right/top meets, weak half-angle >7/8, weak corner hosts no midpoint',
          'background':'all G1 and all G5 excluded by round10/round8',
          'other_remaining':'other G2 representatives and G3-G4 remain incomplete',
          'global_bound_unchanged':'2 <= S(6) < 2.03; S(6)=2 remains unproved'}
    (root/'verification_result.json').write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in data.items() if k not in ['queries','scripts']},indent=2),flush=True)


if __name__=='__main__':
    main()
