import itertools
import time
import numpy as np
import fastdfs2 as fastdfs

rng=np.random.default_rng(719)
for case in range(600):
    n=int(rng.integers(2,12)); k=int(rng.integers(2,15))
    m=int(rng.integers(1,7))
    raw=rng.random((k,n))<rng.uniform(.1,.8)
    S=np.array([[sum(1<<p for p in range(n) if row[p])] for row in raw],np.uint64)
    brute=any(np.any(raw[list(ii)],axis=0).all() for r in range(1,min(k,m)+1)
              for ii in itertools.combinations(range(k),r))
    ok,_=fastdfs.no_cover(S,n,m)
    assert ok==(not brute),(case,n,k,m)
print('PASS: 600 random families versus exhaustive combinations',flush=True)
for n in [63,64,65,127,128,129,253]:
    W=(n+63)//64
    S=np.zeros((2,W),np.uint64)
    for p in range(n):
        S[p%2,p//64] |= np.uint64(1)<<np.uint64(p%64)
    assert fastdfs.no_cover(S,n,1)[0]
    assert not fastdfs.no_cover(S,n,2)[0]
print('PASS: multiword bitsets and padding boundaries',flush=True)
