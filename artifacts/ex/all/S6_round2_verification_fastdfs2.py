"""Exact, solver-independent check that no m sets of a family cover all points (bitset DFS).
Complete branching: the chosen uncovered point p must lie in some chosen set; among sets containing p only those
maximal on the uncovered points are tried (a dominated choice can be swapped for its dominator). Pruning:
greedy set of pairwise-incompatible uncovered points (no family member contains two of them) needs that many
more sets."""
import numpy as np
from numba import njit

@njit(cache=True)
def _popc(x):
    c = 0
    while x:
        x &= x - np.uint64(1); c += 1
    return c

@njit(cache=True)
def _has(mask, p):
    return (mask[p >> 6] >> np.uint64(p & 63)) & np.uint64(1)


@njit(cache=True)
def _forced_two(S, indptr, idx, compat, U, nu, W):
    """Necessary bipartition constraints when only two sets remain.
    Returns (-1, p, mask) on an odd cycle or an impossible part;
    (0,p,mask) if no nontrivial component; (1,p,mask) otherwise.
    A nontrivial connected incompatibility component must put its entire
    bipartition classes into the two sets, up to swapping their labels.
    """
    col=np.full(nu,-1,np.int64)
    queue=np.empty(nu,np.int64)
    bestL=np.zeros(W,np.uint64);bestR=np.zeros(W,np.uint64)
    bestsize=0;bestp=-1;bestr=-1
    for start in range(nu):
        if col[start]>=0:continue
        col[start]=0;queue[0]=start;head=0;tail=1
        L=np.zeros(W,np.uint64);R=np.zeros(W,np.uint64)
        nl=0;nr=0;pl=-1;pr=-1;cl=1<<60;cr=1<<60
        while head<tail:
            v=queue[head];head+=1;p=U[v]
            count=indptr[p+1]-indptr[p]
            if col[v]==0:
                L[p>>6]|=np.uint64(1)<<np.uint64(p&63);nl+=1
                if count<cl:cl=count;pl=p
            else:
                R[p>>6]|=np.uint64(1)<<np.uint64(p&63);nr+=1
                if count<cr:cr=count;pr=p
            for z in range(nu):
                if compat[p,U[z]]:continue
                if col[z]<0:
                    col[z]=1-col[v];queue[tail]=z;tail+=1
                elif col[z]==col[v]:
                    return -1,-1,L
        if nr and max(nl,nr)>bestsize:
            bestsize=max(nl,nr)
            if nl>=nr:
                bestL=L;bestR=R;bestp=pl;bestr=pr
            else:
                bestL=R;bestR=L;bestp=pr;bestr=pl
    if bestp<0:return 0,-1,bestL
    # Both forced classes must independently fit in a member of S.
    for side in range(2):
        mask=bestL if side==0 else bestR
        p=bestp if side==0 else bestr
        found=False
        for j in range(indptr[p],indptr[p+1]):
            sid=idx[j];fits=True
            for w in range(W):
                if (mask[w] & ~S[sid,w])!=0:fits=False;break
            if fits:found=True;break
        if not found:return -1,-1,bestL
    return 1,bestp,bestL

@njit(cache=True)
def _dfs(S, indptr, idx, compat, order, covered, depth, m, n, W, stats, valid):
    stats[0] += 1
    # uncovered list
    U = np.empty(n, np.int64); nu = 0
    for t in range(n):
        p = order[t]
        if not _has(covered, p):
            U[nu] = p; nu += 1
    if nu == 0:
        return True
    if depth == m:
        return False
    if depth == m - 1:
        # At most one set remains. Test exact subset inclusion directly.
        p = U[0]
        for tt in range(1,nu):
            if not compat[p,U[tt]]:
                stats[1] += 1
                return False
        for jj in range(indptr[p], indptr[p+1]):
            sid = idx[jj]
            fits = True
            for w in range(W):
                if ((~covered[w]) & valid[w] & ~S[sid,w]) != 0:
                    fits = False
                    break
            if fits:
                return True
        return False
    # incompatibility lower bound (greedy)
    I = np.empty(nu, np.int64); ni = 0
    for t in range(nu):
        p = U[t]; ok = True
        for r in range(ni):
            if compat[p, I[r]]:
                ok = False; break
        if ok:
            I[ni] = p; ni += 1
            if ni > m - depth:
                stats[1] += 1
                return False
    # choose point with fewest candidate sets
    best = -1; bc = 1 << 60
    for t in range(nu):
        p = U[t]; c = indptr[p+1] - indptr[p]
        if c < bc:
            bc = c; best = p
    p = best
    forced=np.zeros(W,np.uint64)
    if depth==m-2:
        status,fp,forced=_forced_two(S,indptr,idx,compat,U,nu,W)
        if status<0:
            stats[1]+=1
            return False
        if status>0:p=fp
    ncmax = indptr[p+1] - indptr[p]
    R = np.empty((ncmax, W), np.uint64); pc = np.empty(ncmax, np.int64)
    nc=0
    for j in range(ncmax):
        sid = idx[indptr[p] + j];fits=True
        for w in range(W):
            if (forced[w] & ~S[sid,w])!=0:fits=False;break
        if not fits:continue
        c=0
        for w in range(W):
            R[nc, w] = S[sid, w] & ~covered[w]; c += _popc(R[nc, w])
        pc[nc] = c;nc+=1
    pc=pc[:nc]
    ordc = np.argsort(-pc)
    keep = np.zeros(nc, np.bool_)
    kept = np.empty(nc, np.int64); nk = 0
    for jj in range(nc):
        j = ordc[jj]; dom = False
        for r in range(nk):
            q = kept[r]; sub = True
            for w in range(W):
                if (R[j, w] & ~R[q, w]) != 0:
                    sub = False; break
            if sub:
                dom = True; break
        if not dom:
            kept[nk] = j; nk += 1
    newc = np.empty(W, np.uint64)
    for r in range(nk):
        j = kept[r]
        for w in range(W):
            newc[w] = covered[w] | R[j, w]
        if _dfs(S, indptr, idx, compat, order, newc.copy(), depth + 1, m, n, W, stats, valid):
            return True
    return False

def no_cover(S, n, m=6):
    """True iff no m members of S (bitset rows) cover points 0..n-1. Exact."""
    W = S.shape[1]
    bits = np.unpackbits(S.view(np.uint8), axis=1, bitorder='little')[:, :n].astype(bool)
    cnt = bits.sum(0)
    if (cnt == 0).any():
        return True, np.zeros(2, np.int64)
    indptr = np.zeros(n + 1, np.int64); indptr[1:] = np.cumsum(cnt)
    idx = np.concatenate([np.nonzero(bits[:, p])[0] for p in range(n)]).astype(np.int64)
    B = bits.astype(np.int32)
    compat = (B.T @ B) > 0
    order = np.argsort(cnt, kind='stable').astype(np.int64)   # rare points first in LB greedy
    stats = np.zeros(2, np.int64)
    valid = np.full(W, np.uint64(0xffffffffffffffff), np.uint64)
    if n % 64:
        valid[-1] = (np.uint64(1) << np.uint64(n%64))-np.uint64(1)
    found = _dfs(S, indptr, idx, compat, order, np.zeros(W, np.uint64), 0, m, n, W, stats, valid)
    return (not found), stats
