"""Rebuild exact all-angle geometry and exhaust all branches from scratch.
Saved root results and optimization logs are never trusted as a proof.
"""
import argparse
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import sys
import time
import numpy as np
import critical_fps
import parallel2_verify as pv

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--geometry-only',action='store_true')
    ap.add_argument('--workers',type=int,default=2)
    args=ap.parse_args()
    assert args.workers>0 and sys.byteorder=='little'
    root=Path(__file__).resolve().parent
    d=json.loads((root/'points_2.03.json').read_text())
    assert isinstance(d['q'],int) and d['q']>0
    assert all(isinstance(v,int) for p in d['points_integer'] for v in p)
    P=np.array(d['points_integer'],np.int64)
    assert P.shape==(d['npoints'],2) and np.min(P)>=0
    assert int(P.max())*d['a_den']<=d['a_num']*d['q']
    t=time.time();S,nb,nf=critical_fps.family(P,d['q'],d['M'])
    assert nb==d['event_bins'] and nf==d['frames'] and len(S)==d['nsets']
    digest=hashlib.sha256(S.astype('<u8').tobytes()).hexdigest()
    assert digest==d['family_sha256']
    assert np.array_equal(S,np.load(root/'family_2.03.npy'))
    print('PASS: regenerated integer geometry equals all stored sets and SHA-256',flush=True)
    print('Geometry seconds:',round(time.time()-t,3),flush=True)
    if args.geometry_only:
        print('Geometry only: this run has not recomputed the set-cover exclusion.',flush=True)
        return
    fresh=root/'fresh_2.03'
    np.save(str(fresh)+'.npy',S)
    Path(str(fresh)+'.json').write_text(json.dumps(dict(npoints=len(P))))
    pv.init(str(fresh));p=int(pv.G['order'][0])
    cands=list(map(int,pv.G['idx'][pv.G['indptr'][p]:pv.G['indptr'][p+1]]))
    results=[];t=time.time()
    print('ROOT POINT',p,'ALL BRANCHES',len(cands),flush=True)
    with mp.Pool(args.workers,initializer=pv.init,initargs=(str(fresh),)) as pool:
        for r in pool.imap_unordered(pv.solve,cands,chunksize=1):
            results.append(r)
            if len(results)%20==0 or r['cover_found']:
                print('Completed',len(results),'/',len(cands),flush=True)
    assert sorted(r['set_index'] for r in results)==sorted(cands)
    found=any(r['cover_found'] for r in results)
    report=dict(certificate='2.03',family_sha256=digest,root_point=p,
                branches=len(cands),no_six_cover=not found,
                nodes=sum(r['nodes'] for r in results),
                prunes=sum(r['prunes'] for r in results),
                seconds=round(time.time()-t,3),completed=results)
    (root/'fresh_2.03.results.json').write_text(json.dumps(report,indent=2))
    print('COMPLETE:',{k:v for k,v in report.items() if k!='completed'},flush=True)
    assert not found,'Candidate family admitted a six-set cover: certificate failed.'

if __name__=='__main__':
    mp.freeze_support();main()
