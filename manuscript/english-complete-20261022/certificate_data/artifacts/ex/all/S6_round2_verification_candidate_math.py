"""Integer candidate-set utilities; MIP helper is optional and not a proof step."""

import numpy as np
from numba import njit

def popcount64(a):
    a = a.astype(np.uint64)
    c = np.zeros(a.shape, np.int64)
    for sh in range(0, 64, 8):
        c += np.array([bin(i).count('1') for i in range(256)])[((a >> np.uint64(sh)) & np.uint64(255)).astype(np.int64)]
    return c

@njit(cache=True)
def _dom(S, order):
    m, W = S.shape
    keep = np.ones(m, np.bool_)
    kept = np.empty(m, np.int64); nk = 0
    for oi in range(m):
        i = order[oi]
        dom = False
        for t in range(nk):
            j = kept[t]
            sub = True
            for w in range(W):
                if (S[i, w] & ~S[j, w]) != 0:
                    sub = False; break
            if sub:
                dom = True; break
        if dom:
            keep[i] = False
        else:
            kept[nk] = i; nk += 1
    return keep

def remove_dominated(S):
    pc = popcount64(S).sum(axis=1)
    order = np.argsort(-pc, kind='stable')
    keep = _dom(S, order)
    return S[keep]

def members(S, n):
    """list of point-index arrays for each set"""
    bits = np.unpackbits(S.view(np.uint8), axis=1, bitorder='little')[:, :n]
    return bits.astype(bool)

def solve_highs(M, m=6, tl=600, threads=4):
    """min set cover via HiGHS. Returns (status, opt, dualbound, chosen_indices)."""
    import highspy
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('time_limit', float(tl))
    h.setOptionValue('threads', threads)
    ns, n = M.shape
    inf = highspy.kHighsInf
    h.addVars(ns, np.zeros(ns), np.ones(ns))
    h.changeColsIntegrality(ns, np.arange(ns, dtype=np.int32), np.array([highspy.HighsVarType.kInteger]*ns))
    h.changeColsCost(ns, np.arange(ns, dtype=np.int32), np.ones(ns))
    for p in range(n):
        idx = np.nonzero(M[:, p])[0].astype(np.int32)
        h.addRow(1, inf, len(idx), idx, np.ones(len(idx)))
    h.run()
    info = h.getInfo()
    st = str(h.getModelStatus())
    chosen = None
    try:
        x = np.array(h.getSolution().col_value)
        if len(x) == ns:
            chosen = [int(i) for i in np.nonzero(x > 0.5)[0]]
    except Exception:
        pass
    return st, info.objective_function_value, info.mip_dual_bound, chosen
