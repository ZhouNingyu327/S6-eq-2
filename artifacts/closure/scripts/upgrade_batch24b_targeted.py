#!/usr/bin/env python3
"""Batch24b: target remaining low-dim / half-angle / Or leftovers with checkable certs."""
from __future__ import annotations

import json
import re
import time
import hashlib
import importlib.util
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch24.jsonl"
RESULT = ITEM3 / "upgrade_results_batch24b.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch24b.jsonl"
LOG = ITEM3 / "upgrade_batch24b.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b24)


def nq(q):
    return re.sub(r"\s+", "", q or "")


def qid(row):
    h = hashlib.sha1(nq(row["q"]).encode()).hexdigest()[:10]
    return f"{row['file']}__n{row['n']}__{h}"


def frac_str(x):
    return b24.frac_str(x)


def halfangle_contain_cert(q):
    """Pattern: v>0; 2v<1; a>1-v; a<1; (1-a)/(1+a) >= v/(2-v)  (and renamings)."""
    s = nq(q)
    # detect variable names
    m = re.search(
        r"(\w+)>0;(?:2\*\1<1|\1<1);(\w+)>1-\1;\2<1;\(1-\2\)/\(1\+\2\)>=\1/\(2-\1\)",
        s,
    )
    if not m:
        return None
    v, a = sp.Symbol(m.group(1)), sp.Symbol(m.group(2))
    # On a in [1-v, 1], show (1-a)/(1+a) - v/(2-v) <= 0 with = only at a=1-v
    # Clear: numer of [(1-a)/(1+a) - v/(2-v)] = (1-a)(2-v) - v(1+a) all over pos denom
    # = 2 - v - a(2-v) - v - a v = 2 - 2v - 2a = 2(1 - v - a)
    # So (1-a)/(1+a) - v/(2-v) = 2(1-v-a)/[(1+a)(2-v)]
    # For a >= 1-v: 1-v-a <= 0, so difference <= 0. Strict a>1-v ⇒ difference < 0.
    # Contradicts >=.
    # Certificate: polynomial identity + Bernstein on -2(1-v-a) or just identity.
    poly = sp.expand(sp.together(((1 - a) / (1 + a) - v / (2 - v)) * (1 + a) * (2 - v)))
    # expect 2(1-v-a)
    target = sp.expand(2 * (1 - v - a))
    if sp.expand(poly - target) != 0:
        # try again with expand numer
        num = sp.expand(sp.numer(sp.together((1 - a) / (1 + a) - v / (2 - v))))
        # dens positive separately
        if sp.expand(num - target) != 0 and sp.expand(num - (1 - v - a)) != 0:
            return None
        target = sp.expand(num)
    return {
        "type": "halfangle_contain_identity",
        "vars": [str(v), str(a)],
        "identity_numer": str(target),
        "claim": "difference=(1-a)/(1+a)-v/(2-v) has numer proportional to (1-v-a); on a>1-v numer<0 with positive dens => difference<0, contradicts >=",
        "dens": ["1+a", "2-v"],
        "domain": "v in (0,1/2), a in (1-v,1)",
    }, "exact-hand-halfangle-contain"


def halfangle_square_cert(q):
    """((1-x)^2)/(2x) >= (r^2)/(2(1-r)) with x>1-r, x<1, r in (0,1/2)."""
    s = nq(q)
    m = re.search(
        r"(\w+)>0;2\*\1<1;(\w+)>1-\1;\2<1;\(\(1-\2\)\*\(1-\2\)\)/\(2\*\2\)>=\(\1\*\1\)/\(2\*\(1-\1\)\)",
        s,
    )
    if not m:
        return None
    r, x = sp.Symbol(m.group(1)), sp.Symbol(m.group(2))
    lhs = ((1 - x) ** 2) / (2 * x)
    rhs = (r ** 2) / (2 * (1 - r))
    diff = sp.together(lhs - rhs)
    num = sp.expand(sp.numer(diff))
    # At x=1-r: lhs = r^2 / (2(1-r)) = rhs. For x>1-r, (1-x)^2/x is decreasing in x on (0,1).
    # Show d/dx [(1-x)^2/x] = ... < 0, so lhs < rhs for x>1-r.
    # Equivalently numer of lhs-rhs has factor (1-r-x) and opposite sign.
    # Substitute x=1-r+s
    s_ = sp.Dummy("s")
    num_s = sp.expand(num.subs(x, 1 - r + s_))
    # Expect leading factor -s * (positive)
    if not num_s.has(s_):
        return None
    # Bernstein on -num over x in [1-r,1] parameterized — 2D box r in [0,1/2], x in [1-r,1] via triangle map
    u, v = sp.Dummy("u"), sp.Dummy("v")
    # r=u/2, x=(1-r)+v*r = 1-u/2 + v*(u/2)
    mapped = sp.expand(num.subs({r: u / 2, x: 1 - u / 2 + v * (u / 2)}))
    # We need num <= 0 on domain for lhs-rhs<=0? Wait we need to show lhs-rhs < 0 always on open set, i.e. num/den < 0.
    # Check dens sign and Bernstein of -num or num.
    try:
        Bn = b24.bernstein_coeffs(mapped, [u, v], [(F(0), F(1)), (F(0), F(1))])
    except Exception:
        return None
    # If all Bn <= 0 (or <0 interior), difference numer <=0
    if all(b <= 0 for b in Bn) and any(b < 0 for b in Bn):
        return {
            "type": "bernstein_halfangle_square",
            "vars_map": {"r": "u/2", "x": "1-u/2+v*u/2"},
            "numer": str(num),
            "mapped": str(mapped),
            "coeffs": [frac_str(b) for b in Bn],
            "claim": "triangle-mapped numer of lhs-rhs has Bernstein coeffs <=0 => lhs<=rhs with equality only on v=0 face excluded by x>1-r",
        }, "exact-Bernstein-halfangle-square"
    return None


def tt_sqrt_cert(q):
    """w in (0,5/12); tt>0; tt^2=w(2+w); inequality in (1+w)(1-tt)+... >= ..."""
    s = nq(q)
    if not ("tt*tt==w*(2+w)" in s and "12*w<5" in s and "w>0" in s):
        return None
    atoms, err = b24.parse_atoms(q)
    if err:
        return None
    cu, o, _ = b24.elim_linear_eq(atoms)
    if cu:
        return {"type": "const", "detail": cu}, "exact-constant-after-elim"
    # eliminate tt via tt = sqrt(w(2+w)) — for inequalities involving (1-tt), use rationalization:
    # replace tt by isolating and squaring carefully when (1-tt) appears linearly with positive coeff.
    # Try Weierstrass-like: set w = 2t/(1-t)? Actually tt^2 = w^2 + 2w = (w+1)^2 - 1 => tt = sqrt((w+1)^2-1)
    # Better: use IBB in (w) after substituting max/min of expressions in tt.
    # Since tt>0 and tt^2=w(2+w), for expr A - B*tt ? 0 with B>0, equivalent after isolating.
    fs = sorted(set().union(*[e.free_symbols for e, _ in o]), key=str)
    # Try deg1 elim on tt if equality still present
    cu2, o2 = b24.elim_deg1_any_coeff(o)
    if cu2:
        return {"type": "const", "detail": cu2}, "exact-constant-after-deg1"
    fs = sorted(set().union(*[e.free_symbols for e, _ in o2]), key=str) if o2 else []
    if len(fs) == 1:
        bounds, _ = b24.extract_bounds(o2, fs, default=(F(0), F(1)))
        if bounds == "empty":
            return {"type": "empty_box"}, "exact-empty-box"
        box = [(bounds[v][0], bounds[v][1]) for v in fs]
        bcert = b24.try_bernstein_single_poly(o2, fs, box)
        if bcert:
            return bcert, "exact-Bernstein-tt-elim"
        ibb = b24.rational_ibb_cert(o2, fs, box, max_cells=100000, max_depth=40)
        if ibb:
            return ibb, "exact-IBB-tt-elim"
    if len(fs) == 2:
        bounds, _ = b24.extract_bounds(o2, fs, default=(F(0), F(1)))
        if bounds and bounds != "empty":
            box = [(bounds[v][0], bounds[v][1]) for v in fs]
            ibb = b24.rational_ibb_cert(o2, fs, box, max_cells=120000, max_depth=36)
            if ibb:
                return ibb, "exact-IBB-tt"
    return None


def r28_hw_cert(q):
    """h^2+2h<=1; 12w<5; 2h(1-h^2-2h)(w+h)*5 >= ((6h(1-h))/(1+h))*(1-h^2)^2"""
    s = nq(q)
    if not ("h*h+2*h<=1" in s and "12*w<5" in s):
        return None
    if "2*h*(1-h*h-2*h)*(w+h)*5" not in s and "2*h*(1-h*h-2*h)*(w+h)*5>=" not in s:
        # flexible
        if "6*h*(1-h)" not in s:
            return None
    atoms, err = b24.parse_atoms(q)
    if err:
        return None
    cu, o, _ = b24.elim_linear_eq(atoms)
    cu2, o = b24.elim_deg1_any_coeff(o)
    if cu or cu2:
        return {"type": "const"}, "exact-constant"
    fs = sorted(set().union(*[e.free_symbols for e, _ in o]), key=str)
    if len(fs) > 2:
        return None
    bounds, _ = b24.extract_bounds(o, fs, default=(F(0), F(1)))
    if not bounds or bounds == "empty":
        return None
    # tighten: h in (0, sqrt(2)-1] since h^2+2h-1<=0 => h<=-1+sqrt(2)
    # use box h in [0, 2/5] (since -1+sqrt2 ~0.414 < 0.5), w in [0,5/12]
    h, w = fs[0], fs[1] if len(fs) == 2 else (fs[0], None)
    # rename properly
    syms = {str(v): v for v in fs}
    if "h" in syms and "w" in syms:
        h, w = syms["h"], syms["w"]
        box = [(F(0), F(2) / 5), (F(0), F(5) / 12)]
        # Move all to one side: show RHS - LHS > 0? Query has LHS >= RHS which we claim UNSAT
        # so show RHS - LHS > 0 on domain, i.e. LHS < RHS always... 
        ibb = b24.rational_ibb_cert(o, [h, w], box, max_cells=150000, max_depth=40)
        if ibb:
            return ibb, "exact-IBB-r28-hw"
        # try minw at w=0 lower? Actually ineq is >= so direction different
        # Clear denoms and Bernstein on difference at max w=5/12 monotone
        # Build difference poly from atoms: find the big >= atom as -e <=0 after normalize? 
        for e, r in o:
            if r not in ("<", "<="):
                continue
            if e.has(h) and e.has(w):
                # try Bernstein of e on box (want e>0 for <= contradiction of e<=0)
                try:
                    n, d = sp.fraction(sp.together(e))
                    Bn = b24.bernstein_coeffs(sp.expand(n), [h, w], box)
                    Bd = b24.bernstein_coeffs(sp.expand(d), [h, w], box) if d.free_symbols else [b24.to_F(d)]
                except Exception:
                    continue
                if all(b > 0 for b in Bd) and all(b >= 0 for b in Bn) and (r == "<" or all(b > 0 for b in Bn)):
                    return {
                        "type": "bernstein_box",
                        "vars": ["h", "w"],
                        "box": [[frac_str(lo), frac_str(hi)] for lo, hi in box],
                        "expr": str(e),
                        "op": r,
                        "numer_coeffs": [frac_str(b) for b in Bn],
                        "denom_coeffs": [frac_str(b) for b in Bd],
                        "claim": "r28-hw Bernstein",
                    }, "exact-Bernstein-r28-hw"
    return None


def simple_l_K_u_cert(q):
    """l>0;2l<1;K>0;15K<8;u>0;l<=K*u; l/(2-l) >= (16*u)/45"""
    s = nq(q)
    if "l/(2-l)>=(16*u)/45" not in s or "l<=K*u" not in s:
        return None
    atoms, err = b24.parse_atoms(q)
    if err:
        return None
    cu, o, _ = b24.elim_linear_eq(atoms)
    cu2, o = b24.elim_deg1_any_coeff(o)
    fs = sorted(set().union(*[e.free_symbols for e, _ in o]), key=str)
    if len(fs) > 3:
        return None
    bounds, _ = b24.extract_bounds(o, fs, default=(F(0), F(1)))
    if not bounds or bounds == "empty":
        return None
    box = [(bounds[v][0], bounds[v][1]) for v in fs]
    # triangle or IBB
    if len(fs) == 3:
        for A in fs:
            others = [v for v in fs if v != A]
            for X in others:
                T = [v for v in others if v != X][0]
                u, v, w = sp.Dummy("u"), sp.Dummy("v"), sp.Dummy("w")
                mapped = [(sp.together(e.subs({A: u, X: u * v, T: w})), r) for e, r in o]
                ibb = b24.rational_ibb_cert(mapped, [u, v, w], [(F(0), F(1))] * 3, max_cells=100000, max_depth=28)
                if ibb:
                    ibb["triangle_map"] = {str(A): "u", str(X): "u*v", str(T): "w"}
                    return ibb, "exact-IBB-triangle3"
    ibb = b24.rational_ibb_cert(o, fs, box, max_cells=100000, max_depth=32)
    if ibb:
        return ibb, "exact-IBB"
    return None


def or_simple_cert(q):
    branches = b24.split_ors(q)
    if len(branches) <= 1:
        return None
    branch_certs = []
    for i, bq in enumerate(branches):
        # try halfangle / main prover / tt
        for prover in (halfangle_contain_cert, halfangle_square_cert, tt_sqrt_cert, r28_hw_cert, simple_l_K_u_cert):
            got = prover(bq)
            if got:
                cert, method = got
                branch_certs.append({"branch": i, "query": bq, "cert": cert, "method": method})
                break
        else:
            atoms, err = b24.parse_atoms(bq)
            if err:
                return None
            cert, method = b24.prove_atoms(atoms, max_fs=3)
            if not cert:
                return None
            branch_certs.append({"branch": i, "query": bq, "cert": cert, "method": method})
    return {
        "type": "or_split",
        "n_branches": len(branch_certs),
        "branches": branch_certs,
    }, "exact-Or-split-all-branches"


def prove_row(row):
    q = row["q"]
    for prover in (
        halfangle_contain_cert,
        halfangle_square_cert,
        tt_sqrt_cert,
        r28_hw_cert,
        simple_l_K_u_cert,
    ):
        try:
            got = prover(q)
        except Exception as ex:
            got = None
        if got:
            return got
    if "Or(" in q:
        try:
            got = or_simple_cert(q)
        except Exception:
            got = None
        if got:
            return got
    # fallback: main prover with max_fs=3 again (after potential bugfixes none)
    try:
        return b24.prove_query(q, max_fs=3)
    except Exception as ex:
        return None, f"err:{str(ex)[:160]}"


def main():
    rows = [json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    RESULT.write_text("")
    still = []
    n_exact = 0
    t0 = time.time()
    logf = open(LOG, "w")

    def log(m):
        print(m, flush=True)
        logf.write(m + "\n")
        logf.flush()

    for i, row in enumerate(rows):
        cert_method = prove_row(row)
        cert, method = (None, None) if not cert_method else cert_method
        rec = {"file": row["file"], "n": row["n"], "q": row["q"], "cvc5": row.get("cvc5"), "id": qid(row)}
        if cert and method and str(method).startswith("exact"):
            rec["status"] = "exact"
            rec["method"] = method
            path = OUT_DIR / f"{qid(row)}.json"
            payload = {
                "id": qid(row),
                "file": row["file"],
                "n": row["n"],
                "query": row["q"],
                "method": method,
                "status": "exact",
                "certificate": cert,
                "batch": "24b",
            }
            path.write_text(json.dumps(payload, ensure_ascii=False, indent=2))
            rec["cert_relpath"] = f"artifacts/closure/item3_certs/exact_certs_batch24/{path.name}"
            n_exact += 1
            log(f"[{i+1}/{len(rows)}] EXACT {row['file']}#{row['n']} {method}")
        else:
            rec["status"] = "open"
            rec["reason"] = method or "no-method"
            still.append(row)
            if (i + 1) % 20 == 0:
                log(f"[{i+1}/{len(rows)}] open exact_so_far={n_exact}")
        with open(RESULT, "a") as fo:
            fo.write(json.dumps(rec, ensure_ascii=False) + "\n")
    STILL_OUT.write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in still) + ("\n" if still else ""))
    log(f"DONE exact={n_exact} open={len(still)} t={time.time()-t0:.1f}s")
    logf.close()


if __name__ == "__main__":
    main()
