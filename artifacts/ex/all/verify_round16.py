"""Reviewable continuous-geometry certificate, with fresh input replays."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time,zipfile

def run(script,cwd):
    proc=subprocess.run([sys.executable,str(script)],cwd=cwd,capture_output=True,
        text=True,encoding='utf-8',errors='replace')
    assert proc.returncode==0,proc.stdout+proc.stderr
    return proc.stdout

def main(core_only):
    start=time.time();root=Path(__file__).resolve().parent
    manifest=json.loads((root/'manifest.json').read_text(encoding='utf-8'))
    for name,digest in manifest['files'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    result={'status':'PASS','scope':'G2 near: all three non-bottom edges meet is impossible for every mu>1',
        'not_proved':['entire G2','G3','G4','S(6)=2'],
        'proof_method':'complete continuous-domain rational interval certificate',
        'fixed_point_cover_search_used':False}
    with tempfile.TemporaryDirectory(prefix='S6_round16_') as scratch:
        scratch=Path(scratch)
        # Independent Fraction verifier and an integer-only regeneration both
        # run in disposable copies. No frozen input files are modified.
        for name in ['verify_round16_fraction_certificate.py','check_round16_interval_cover.py']:
            shutil.copy2(root/name,scratch/name)
        shutil.copytree(root/'round16_interval_certificate',scratch/'round16_interval_certificate')
        run(scratch/'verify_round16_fraction_certificate.py',scratch)
        rows=json.loads((scratch/'round16_fraction_verification.json').read_text())
        assert [r['leaves'] for r in rows]==[249,924]
        assert all(r['result']=='INDEPENDENT_FRACTION_PASS' for r in rows)
        result['independent_fraction']=[{k:v for k,v in r.items() if k!='strict_minimum_margins'} for r in rows]
        result['continuous_leaf_boxes']=sum(r['leaves'] for r in rows)
        print('Independent exact-fraction certificate PASS: 1173 boxes',flush=True)
        for sign in [1,-1]:
            proc=subprocess.run([sys.executable,str(scratch/'check_round16_interval_cover.py'),
                '--sign',str(sign)],cwd=scratch,capture_output=True,text=True)
            assert proc.returncode==0,proc.stdout+proc.stderr
            name='round16_interval_certificate/C%d.tree'%sign
            assert (scratch/name).read_bytes()==(root/name).read_bytes(),name
        result['integer_only_tree_regeneration']='byte-for-byte PASS'
        if not core_only:
            shutil.copy2(root/'check_round16_geometric_reduction.py',scratch/'check_round16_geometric_reduction.py')
            run(scratch/'check_round16_geometric_reduction.py',scratch)
            geom=json.loads((scratch/'round16_geometric_reduction_checks.json').read_text())
            assert len(geom['queries'])==5 and all(r['result']=='unsat' for r in geom['queries'])
            result['geometric_reduction']=geom
            print('Geometric reduction PASS: 5 UNSAT, 6 symbolic identities',flush=True)
            previous=root/'S6_round15_verification.zip'
            assert hashlib.sha256(previous.read_bytes()).hexdigest()==(
                'cfbbb0622ac0468df7d7a6d518aa68c60e752117d0e88593a24b13c738ef7987')
            inputs=scratch/'inputs_round15';inputs.mkdir()
            with zipfile.ZipFile(previous) as archive:
                for name in archive.namelist():
                    p=PurePosixPath(name)
                    assert not p.is_absolute() and '..' not in p.parts
                archive.extractall(inputs)
            run(inputs/'verify_round15.py',inputs)
            inp=json.loads((inputs/'verification_result.json').read_text(encoding='utf-8'))
            assert inp['new_NRA_queries']==9 and inp['rational_Bernstein_coefficients']==77
            result['input_round15']={'queries_UNSAT':9,'rational_Bernstein_coefficients':77,
                'positive_quadratic_endpoints':2,'junction_convex_combination_identities':3,
                'source_zip_sha256':hashlib.sha256(previous.read_bytes()).hexdigest()}
            shutil.copy2(root/'check_round15_separation_addendum.py',scratch/'check_round15_separation_addendum.py')
            run(scratch/'check_round15_separation_addendum.py',scratch)
            add=json.loads((scratch/'round15_separation_addendum_checks.json').read_text())
            assert add['unsat_count']==4 and all(q['result']=='unsat' for q in add['queries'])
            result['input_round15_addendum_UNSAT']=4
            result['total_replayed_NRA_queries']=18
            result['older_inputs_policy']='round-15 replay plus frozen round-14 ZIP integrity; deeper history not rerun'
            print('Fresh round-15 input replay PASS: 77 coefficients, 9+4 UNSAT',flush=True)
        else:
            result['supplementary_geometry_and_input_replays']='not run (--core-only)'
    result['seconds']=time.time()-start
    (root/'verification_result.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['independent_fraction','geometric_reduction']},
        ensure_ascii=False,indent=2),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--core-only',action='store_true')
    main(ap.parse_args().core_only)
