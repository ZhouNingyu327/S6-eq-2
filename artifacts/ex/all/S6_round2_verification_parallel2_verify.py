"""Complete root split of the exact DFS, portable to Windows spawn."""
import argparse
import json
import multiprocessing as mp
from pathlib import Path
import time

import numpy as np
import fastdfs2 as fastdfs

G={}

def init(path):
    S=np.load(path+'.npy')
    d=json.loads(Path(path+'.json').read_text())
    n=d['npoints'];W=S.shape[1]
    bits=np.unpackbits(S.view(np.uint8),axis=1,bitorder='little')[:,:n].astype(bool)
    cnt=bits.sum(0)
    assert np.min(cnt)>0 and len(S)<2**31
    indptr=np.zeros(n+1,np.int64);indptr[1:]=np.cumsum(cnt)
    idx=np.concatenate([np.nonzero(bits[:,p])[0] for p in range(n)]).astype(np.int64)
    B=bits.astype(np.int32);compat=(B.T@B)>0
    order=np.argsort(cnt,kind='stable').astype(np.int64)
    valid=np.full(W,np.uint64(0xffffffffffffffff),np.uint64)
    if n%64:valid[-1]=(np.uint64(1)<<np.uint64(n%64))-np.uint64(1)
    G.update(S=S,n=n,W=W,indptr=indptr,idx=idx,compat=compat,order=order,valid=valid)

def solve(j):
    t=time.time();st=np.zeros(2,np.int64)
    r=fastdfs._dfs(G['S'],G['indptr'],G['idx'],G['compat'],G['order'],
                  G['S'][j].copy(),1,6,G['n'],G['W'],st,G['valid'])
    return dict(set_index=int(j),cover_found=bool(r),nodes=int(st[0]),
                prunes=int(st[1]),seconds=round(time.time()-t,3))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('path');ap.add_argument('--workers',type=int,default=8)
    args=ap.parse_args();init(args.path)
    p=int(G['order'][0]);cands=list(map(int,G['idx'][G['indptr'][p]:G['indptr'][p+1]]))
    print('ROOT',p,len(cands),'branches',flush=True)
    t=time.time();results=[]
    checkpoint=Path(args.path+'.roots.json')
    if checkpoint.exists():
        prev=json.loads(checkpoint.read_text())
        assert prev['root_point']==p and prev['total_branches']==len(cands)
        results=prev['completed']
        done={x['set_index'] for x in results}
        assert len(done)==len(results) and done.issubset(cands)
    else:
        done=set()
    pending=[j for j in cands if j not in done]
    print('RESUME',len(results),'complete;',len(pending),'pending',flush=True)
    with mp.Pool(args.workers,initializer=init,initargs=(args.path,)) as pool:
        for r in pool.imap_unordered(solve,pending,chunksize=1):
            results.append(r)
            print(f"{len(results)}/{len(cands)}",r,flush=True)
            Path(args.path+'.roots.json').write_text(json.dumps(dict(root_point=p,
                total_branches=len(cands),completed=results),indent=2))
    assert sorted(x['set_index'] for x in results)==sorted(cands)
    result=dict(no_six_cover=not any(x['cover_found'] for x in results),
                nodes=sum(x['nodes'] for x in results),prunes=sum(x['prunes'] for x in results),
                roots=len(cands),seconds=round(time.time()-t,3))
    print('COMPLETE EXACT VERIFICATION',result,flush=True)
    d=json.loads(Path(args.path+'.json').read_text());d['parallel_exact_dfs']=result
    Path(args.path+'.json').write_text(json.dumps(d,indent=2))

if __name__=='__main__':main()
