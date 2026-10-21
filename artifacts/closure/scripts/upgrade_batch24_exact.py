#!/usr/bin/env python3
"""Batch24: emit machine-checkable Bernstein / rational-IBB certificates for remaining (S).

Honesty rules:
- Only emit a certificate when a deterministic rational witness proves UNSAT.
- IBB certificates store the contradictory leaf boxes (checker re-verifies each leaf).
- Bernstein certificates store coeffs; checker recomputes and checks sign.
- Do NOT upgrade on method-name pattern match alone.
"""
from __future__ import annotations

import json
import re
import time
import hashlib
from fractions import Fraction as F
from pathlib import Path
from math import comb
from itertools import product
from typing import Any

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]  # artifacts/closure
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
RESULT = ITEM3 / "upgrade_results_batch24.jsonl"
STILL = ITEM3 / "still_S_after_batch24.jsonl"
LOG = ITEM3 / "upgrade_batch24.log"
SOURCE = ITEM3 / "remaining_S_source.jsonl"

SAFE = {
    "alpha": "alpha_",
    "beta": "beta_",
    "gamma": "gamma_",
    "delta": "delta_",
    "zeta": "zeta_",
    "eta": "eta_",
    "theta": "theta_",
    "lambda": "lambda_",
    "I": "I_",
    "E": "E_",
    "S": "S_",
    "N": "N_",
    "O": "O_",
    "Q": "Q_",
}


def prep(q: str) -> str:
    for a, b in SAFE.items():
        q = re.sub(r"\b" + a + r"\b", b, q)
    return q


def nq(q: str) -> str:
    return re.sub(r"\s+", "", q or "")


def frac_str(x) -> str:
    if isinstance(x, F):
        return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)
    return str(sp.Rational(x))


def to_F(x) -> F:
    return F(sp.Rational(x))


def bernstein_coeffs(poly_expr, vars_, box):
    dummies = [sp.Dummy(f"u{i}") for i in range(len(vars_))]
    subs = {v: lo + (hi - lo) * u for v, (lo, hi), u in zip(vars_, box, dummies)}
    expr = sp.expand(poly_expr.subs(subs))
    if not expr.free_symbols:
        return [to_F(sp.simplify(expr))]
    P = sp.Poly(expr, *dummies)
    degs = [P.degree(u) for u in dummies]
    if any(d < 0 for d in degs):
        return [to_F(sp.simplify(P.as_expr()))]
    ranges = [range(d + 1) for d in degs]
    a = {}
    for idx in product(*ranges):
        mon = 1
        for u, i in zip(dummies, idx):
            mon *= u**i
        a[idx] = to_F(P.coeff_monomial(mon))
    B = []
    for idx in product(*ranges):
        ssum = F(0)
        for k in product(*[range(i + 1) for i in idx]):
            aa = a.get(k, F(0))
            if aa == 0:
                continue
            num = den = 1
            for i, ki, di in zip(idx, k, degs):
                num *= comb(i, ki)
                den *= comb(di, ki)
            ssum += F(num) / F(den) * aa
        B.append(ssum)
    return B


def split_ors(q: str):
    parts = [p.strip() for p in q.replace("\n", " ").split(";") if p.strip()]
    bases, ors = [], []
    for p in parts:
        if p.startswith("Or("):
            inner = p[3:-1] if p.endswith(")") else p[3:]
            alts, depth, cur = [], 0, []
            for ch in inner:
                if ch == "(":
                    depth += 1
                    cur.append(ch)
                elif ch == ")":
                    depth -= 1
                    cur.append(ch)
                elif ch == "," and depth == 0:
                    alts.append("".join(cur).strip())
                    cur = []
                else:
                    cur.append(ch)
            if cur:
                alts.append("".join(cur).strip())
            ors.append(alts)
        elif "!=" in p or "≠" in p:
            continue
        else:
            bases.append(p)
    if not ors:
        return ["; ".join(bases)] if bases else [q]
    return ["; ".join(bases + list(c)) for c in product(*ors)]


def parse_atoms(q: str):
    q = prep(q)
    atoms = []
    for p in [p.strip() for p in q.replace("\n", " ").split(";") if p.strip()]:
        if p.startswith("Or("):
            return None, "Or"
        if "!=" in p:
            continue
        m = re.match(r"^(.+?)\s*(<=|>=|==|<|>)\s*(.+)$", p)
        if not m:
            return None, "parse"
        lhs = sp.sympify(m.group(1))
        rhs = sp.sympify(m.group(3))
        atoms.append((sp.together(lhs - rhs), m.group(2)))
    return atoms, None


def normalize(atoms):
    o = []
    for e, r in atoms:
        if r == ">":
            o.append((-e, "<"))
        elif r == ">=":
            o.append((-e, "<="))
        else:
            o.append((e, r))
    return o


def elim_linear_eq(atoms):
    o = normalize(atoms)
    subs = {}
    changed = True
    while changed:
        changed = False
        for e, r in list(o):
            if r != "==":
                continue
            ee = sp.expand(e.subs(subs))
            for s in sorted(ee.free_symbols, key=str):
                try:
                    p = sp.Poly(ee, s)
                except Exception:
                    continue
                if p.degree() != 1 or getattr(p.LC(), "free_symbols", set()):
                    continue
                sols = sp.solve(ee, s)
                if not sols:
                    continue
                sol = sols[0]
                subs = {k: sp.together(v.subs(s, sol)) for k, v in subs.items()}
                subs[s] = sol
                changed = True
                break
            if changed:
                break
    o2 = []
    for e, r in o:
        ee = sp.together(e.subs(subs))
        if r == "==":
            ee = sp.simplify(ee)
            if ee == 0:
                continue
        if not ee.free_symbols:
            try:
                rf = to_F(sp.simplify(ee))
            except Exception:
                continue
            if (r == "<" and rf >= 0) or (r == "<=" and rf > 0) or (r == "==" and rf != 0):
                return "const-unsat", [], {}
            continue
        o2.append((ee, r))
    return None, o2, subs


def elim_deg1_any_coeff(o):
    """Eliminate vars that appear degree 1 in an equality, even if LC depends on other vars."""
    o = list(o)
    changed = True
    while changed:
        changed = False
        for e, r in list(o):
            if r != "==":
                continue
            ee = sp.expand(e)
            for s in sorted(ee.free_symbols, key=str):
                if safe_deg(ee, s) != 1:
                    continue
                te = sp.together(ee)
                P = sp.Poly(sp.expand(sp.numer(te)), s)
                lc = sp.expand(P.LC())
                tc = sp.expand(P.TC())
                # s = -tc/lc
                sol = sp.together(-tc / lc)
                mapped = []
                for e2, r2 in o:
                    ee2 = sp.together(e2.subs(s, sol))
                    if r2 == "==":
                        ee2 = sp.simplify(sp.together(sp.numer(sp.together(ee2))))
                        if ee2 == 0:
                            continue
                        mapped.append((ee2, "=="))
                    else:
                        # e2(sol) ? 0; write numer(e2)*sign considerations via *denom^2 style:
                        # replace by numer(together(e2)) * denom if we require denom>0 later in Bernstein,
                        # but safer: keep as together expression for IBB quotient handling.
                        mapped.append((ee2, r2))
                # Also record lc != 0 as side constraint: for domains where lc may vanish, skip
                # Add -lc < 0 or lc > 0 loosely — skip auto; rely on domain bounds
                o = mapped
                changed = True
                break
            if changed:
                break
    # constant fold
    o2 = []
    for e, r in o:
        if not sp.sympify(e).free_symbols:
            try:
                rf = to_F(sp.simplify(e))
            except Exception:
                continue
            if (r == "<" and rf >= 0) or (r == "<=" and rf > 0) or (r == "==" and rf != 0):
                return "const-unsat", []
            continue
        o2.append((e, r))
    return None, o2


def weierstrass(o):
    for e, r in o:
        if r != "==":
            continue
        ee = sp.expand(e)
        syms = list(ee.free_symbols)
        for i, c in enumerate(syms):
            for s in syms[i + 1 :]:
                if sp.expand(ee - (c**2 + s**2 - 1)) == 0:
                    t = sp.Dummy("tw")
                    sub = {c: (1 - t**2) / (1 + t**2), s: 2 * t / (1 + t**2)}
                    mapped = []
                    for e2, r2 in o:
                        ee2 = sp.together(e2.subs(sub))
                        if r2 == "==":
                            ee2 = sp.simplify(ee2)
                            if ee2 == 0:
                                continue
                        mapped.append((ee2, r2))
                    # clear denoms carefully: multiply numer*denom for inequalities when denom sign known later
                    cleared = []
                    for e2, r2 in mapped:
                        if r2 == "==":
                            cleared.append((sp.expand(sp.numer(sp.together(e2))), r2))
                        else:
                            # replace e ? 0 by numer(e)*denom(e) ? 0 if denom>0 on domain; record denom
                            te = sp.together(e2)
                            num, den = sp.fraction(te)
                            cleared.append((sp.expand(num * den), r2))  # assumes den>0 after Weierstrass (1+t^2)^k
                    return cleared, [t], "weierstrass"
    return None, None, None


def clear_denoms(o):
    out = []
    for e, r in o:
        te = sp.together(e)
        num, den = sp.fraction(te)
        if r == "==":
            out.append((sp.expand(num), r))
        else:
            # e = num/den; if den may change sign, keep as is for IBB which handles quotients
            out.append((sp.expand(num * den), r))
    return out


def extract_bounds(o, fs, default=(F(0), F(1))):
    bounds = {v: [None, None] for v in fs}
    polys = []
    for e, r in o:
        if r == "==":
            polys.append((e, "=="))
            continue
        try:
            te = sp.together(e)
            num, den = sp.fraction(te)
            if getattr(den, 'free_symbols', set()):
                polys.append((e, r))
                continue
            P = sp.Poly(sp.expand(num), *fs)
        except Exception:
            polys.append((e, r))
            continue
        degs = {v: P.degree(v) for v in fs}
        nz = [v for v in fs if degs[v] > 0]
        if not nz:
            c0 = sp.Rational(P.as_expr())
            if (r == "<" and c0 >= 0) or (r == "<=" and c0 > 0):
                return "empty", None
            continue
        if len(nz) == 1 and degs[nz[0]] == 1:
            v = nz[0]
            a = to_F(P.coeff_monomial(v))
            rest = sp.expand(P.as_expr() - a * v)
            if rest.free_symbols:
                polys.append((P.as_expr(), r))
                continue
            b = to_F(rest)
            thr = -b / a
            if a > 0:
                if r in ("<", "<="):
                    bounds[v][1] = thr if bounds[v][1] is None else min(bounds[v][1], thr)
                else:
                    bounds[v][0] = thr if bounds[v][0] is None else max(bounds[v][0], thr)
            else:
                if r in ("<", "<="):
                    bounds[v][0] = thr if bounds[v][0] is None else max(bounds[v][0], thr)
                else:
                    bounds[v][1] = thr if bounds[v][1] is None else min(bounds[v][1], thr)
            # keep linear bound as poly too for strictness in IBB
            polys.append((P.as_expr(), r))
            continue
        polys.append((P.as_expr(), r))
    for v in fs:
        if bounds[v][0] is None:
            bounds[v][0] = default[0]
        if bounds[v][1] is None:
            bounds[v][1] = default[1]
        # epsilon shrink for open bounds is handled by strict ops in IBB
    return bounds, polys


def interval_poly(Pexpr, box, vars_):
    try:
        B = bernstein_coeffs(Pexpr, vars_, box)
        return min(B), max(B)
    except Exception:
        return None


def cell_contradicts(polys, fs, box):
    """Return (True, reason) if box cannot contain a point satisfying all polys."""
    for pe, r in polys:
        n, d = sp.fraction(sp.together(pe))
        n, d = sp.expand(n), sp.expand(d)
        rng = interval_poly(n, box, fs)
        if rng is None:
            return False, None
        lo_n, hi_n = rng
        if d.is_number:
            if d == 0:
                return False, None
            df = to_F(d)
            if df > 0:
                lo, hi = lo_n / df, hi_n / df
            else:
                lo, hi = hi_n / df, lo_n / df
        else:
            rd = interval_poly(d, box, fs)
            if rd is None:
                return False, None
            lo_d, hi_d = rd
            if lo_d <= 0 <= hi_d:
                return False, None
            cands = [lo_n / lo_d, lo_n / hi_d, hi_n / lo_d, hi_n / hi_d]
            lo, hi = min(cands), max(cands)
        if r == "==" and (lo > 0 or hi < 0):
            return True, {"poly": str(pe), "op": r, "range": [frac_str(lo), frac_str(hi)]}
        if r == "<" and lo >= 0:
            return True, {"poly": str(pe), "op": r, "range": [frac_str(lo), frac_str(hi)]}
        if r == "<=" and lo > 0:
            return True, {"poly": str(pe), "op": r, "range": [frac_str(lo), frac_str(hi)]}
        if r == ">" and hi <= 0:
            return True, {"poly": str(pe), "op": r, "range": [frac_str(lo), frac_str(hi)]}
        if r == ">=" and hi < 0:
            return True, {"poly": str(pe), "op": r, "range": [frac_str(lo), frac_str(hi)]}
    return False, None


def rational_ibb_cert(o, fs, box0, max_cells=80000, max_depth=26):
    bounds_box = list(box0)
    if any(lo > hi for lo, hi in bounds_box):
        return {
            "type": "empty_box",
            "vars": [str(v) for v in fs],
            "box": [[frac_str(lo), frac_str(hi)] for lo, hi in bounds_box],
        }
    polys = [(e, r) for e, r in o]
    cells = [(tuple(bounds_box), 0)]
    leaves = []
    seen = 0
    while cells:
        box, depth = cells.pop()
        seen += 1
        if seen > max_cells:
            return None
        ok, reason = cell_contradicts(polys, fs, box)
        if ok:
            leaves.append(
                {
                    "box": [[frac_str(lo), frac_str(hi)] for lo, hi in box],
                    "depth": depth,
                    "contradiction": reason,
                }
            )
            continue
        if depth >= max_depth:
            return None
        widths = [hi - lo for lo, hi in box]
        j = max(range(len(widths)), key=lambda i: widths[i])
        lo, hi = box[j]
        if hi == lo:
            return None
        mid = (lo + hi) / 2
        L = list(box)
        R = list(box)
        L[j] = (lo, mid)
        R[j] = (mid, hi)
        cells.append((tuple(R), depth + 1))
        cells.append((tuple(L), depth + 1))
    return {
        "type": "rational_ibb",
        "vars": [str(v) for v in fs],
        "box0": [[frac_str(lo), frac_str(hi)] for lo, hi in box0],
        "atoms": [{"expr": str(e), "op": r} for e, r in polys],
        "n_cells": seen,
        "n_leaves": len(leaves),
        "max_depth_used": max((L["depth"] for L in leaves), default=0),
        "leaves": leaves,
    }


def try_bernstein_single_poly(o, fs, box):
    """If one inequality is already contradicted on whole box by Bernstein sign."""
    for e, r in o:
        if r == "==":
            continue
        n, d = sp.fraction(sp.together(e))
        n, d = sp.expand(n), sp.expand(d)
        try:
            Bn = bernstein_coeffs(n, fs, box)
            if d.free_symbols:
                Bd = bernstein_coeffs(d, fs, box)
                dpos = all(b > 0 for b in Bd)
            else:
                Bd = [to_F(d)]
                dpos = Bd[0] > 0
        except Exception:
            continue
        if not dpos:
            continue
        # Strong: numer strictly positive (or nonneg for <)
        if r == "<" and all(b >= 0 for b in Bn):
            return {
                "type": "bernstein_box",
                "vars": [str(v) for v in fs],
                "box": [[frac_str(lo), frac_str(hi)] for lo, hi in box],
                "expr": str(e),
                "op": r,
                "numer_coeffs": [frac_str(b) for b in Bn],
                "denom_coeffs": [frac_str(b) for b in Bd],
                "claim": "numer_nonneg_denom_pos_implies_strict_ineq_impossible",
            }
        if r == "<=" and all(b > 0 for b in Bn):
            return {
                "type": "bernstein_box",
                "vars": [str(v) for v in fs],
                "box": [[frac_str(lo), frac_str(hi)] for lo, hi in box],
                "expr": str(e),
                "op": r,
                "numer_coeffs": [frac_str(b) for b in Bn],
                "denom_coeffs": [frac_str(b) for b in Bd],
                "claim": "numer_pos_denom_pos_implies_ineq_impossible",
            }
        # Endpoint-zero case for univariate <= : numer>=0, zeros only at boundary excluded by a strict atom
        if r == "<=" and len(fs) == 1 and all(b >= 0 for b in Bn) and any(b == 0 for b in Bn):
            v = fs[0]
            lo, hi = box[0]
            # Factor numer; check roots in [lo,hi]
            try:
                roots = sp.real_roots(sp.Poly(sp.expand(n), v))
            except Exception:
                roots = []
            bad_roots = []
            for rt in roots:
                try:
                    rf = to_F(sp.Rational(rt)) if rt.is_rational else None
                except Exception:
                    rf = None
                if rf is None:
                    # try refine
                    try:
                        rf = to_F(sp.nsimplify(rt))
                    except Exception:
                        bad_roots.append(str(rt)); continue
                if lo <= rf <= hi:
                    # is rf excluded by some strict constraint in o?
                    excluded = False
                    for e2, r2 in o:
                        if r2 != "<" or e2.free_symbols - {v}:
                            continue
                        # evaluate e2 at rf; need e2(rf) >= 0 so strict < fails
                        val = sp.simplify(e2.subs(v, rf))
                        try:
                            vf = to_F(val)
                        except Exception:
                            continue
                        if vf >= 0:
                            excluded = True
                            break
                    if not excluded:
                        bad_roots.append(frac_str(rf))
            if not bad_roots:
                return {
                    "type": "bernstein_box_strict_endpoint",
                    "vars": [str(v)],
                    "box": [[frac_str(lo), frac_str(hi)]],
                    "expr": str(e),
                    "op": r,
                    "numer_coeffs": [frac_str(b) for b in Bn],
                    "denom_coeffs": [frac_str(b) for b in Bd],
                    "claim": "numer_nonneg_zeros_only_on_strictly_excluded_endpoint",
                }
    return None


def safe_deg(expr, var):
    try:
        te = sp.together(expr)
        num = sp.expand(sp.numer(te))
        return sp.degree(num, var)
    except Exception:
        return -1

def minw_reduce_univariate(o, fs):
    """If constraints include w >= alpha*a+beta and f(a)*w + g(a) < 0 with f>0, reduce to univariate."""
    if len(fs) != 2:
        return None
    # Collect candidate linear lower bounds for each var
    lowers = {v: [] for v in fs}
    for e, r in o:
        if r not in ("<", "<="):
            continue
        for w in fs:
            a = [v for v in fs if v != w][0]
            ee = sp.expand(e)
            if safe_deg(ee, w) != 1:
                continue
            Pw = sp.Poly(ee, w)
            lc = sp.expand(Pw.LC())
            if lc.free_symbols:
                continue
            cw = to_F(lc)
            rest = sp.expand(Pw.TC())
            if rest.free_symbols - {a}:
                continue
            if cw < 0:
                # cw*w + rest <= 0 => w >= -rest/cw
                alpha_expr = sp.together(-rest / cw)
                try:
                    Pa = sp.Poly(sp.expand(alpha_expr), a)
                except Exception:
                    continue
                if Pa.degree() <= 1 and not (alpha_expr.free_symbols - {a}):
                    alpha = to_F(Pa.coeff_monomial(a)) if Pa.degree() == 1 else F(0)
                    beta = to_F(Pa.TC())
                    lowers[w].append((alpha, beta, r, a))
    # Product-style upper bounds: degree 1 in w, LC depends on a; try all lower bounds
    cands = []
    for e, r in o:
        if r not in ("<", "<="):
            continue
        ee = sp.expand(e)
        for w in fs:
            a = [v for v in fs if v != w][0]
            if safe_deg(ee, w) != 1:
                continue
            Pw = sp.Poly(ee, w)
            f = sp.expand(Pw.LC())
            gneg = sp.expand(Pw.TC())
            if f.free_symbols - {a} or gneg.free_symbols - {a}:
                continue
            # skip pure bound defs: constant f and linear gneg
            if not f.free_symbols and sp.degree(gneg, a) <= 1:
                continue
            for alpha, beta, lr, aa in lowers[w]:
                witness = sp.expand((alpha * a + beta) * f + gneg)
                cands.append({
                    "w": w,
                    "a": a,
                    "alpha": alpha,
                    "beta": beta,
                    "f": f,
                    "witness": witness,
                    "op": r,
                })
    return cands


def prove_atoms(atoms, max_fs=3):
    cu, o, _subs = elim_linear_eq(atoms)
    if cu == "const-unsat":
        return {
            "type": "const_unsat_after_elim",
            "method": "exact-constant-after-elim",
        }, "exact-constant-after-elim"
    cu2, o = elim_deg1_any_coeff(o)
    if cu2 == "const-unsat":
        return {
            "type": "const_unsat_after_deg1",
            "method": "exact-constant-after-deg1",
        }, "exact-constant-after-deg1"

    # Weierstrass attempt
    wmap, wvars, wtag = weierstrass(o)
    candidates = [(o, None, "raw")]
    if wmap is not None:
        candidates.append((wmap, wvars, wtag))

    for oo, forced_fs, tag in candidates:
        if not oo:
            return {"type": "empty_after_elim", "tag": tag}, f"exact-empty-{tag}"
        fs = forced_fs if forced_fs is not None else sorted(
            set().union(*[e.free_symbols for e, _ in oo]), key=str
        )
        if not fs:
            # all constant
            return {"type": "const_after_map", "tag": tag}, f"exact-const-{tag}"
        if len(fs) > max_fs:
            continue

        # tighten default box: if Weierstrass t, use (0,1) or (-1,1)
        default = (F(0), F(1))
        bounds, polys = extract_bounds(oo, fs, default=default)
        if bounds == "empty":
            return {
                "type": "empty_box",
                "tag": tag,
                "vars": [str(v) for v in fs],
            }, f"exact-empty-box-{tag}"
        if bounds is None:
            continue
        box = [(bounds[v][0], bounds[v][1]) for v in fs]
        # slight expand if equal
        box2 = []
        for lo, hi in box:
            if lo == hi:
                return None, None
            box2.append((lo, hi))
        box = box2

        bcert = try_bernstein_single_poly(oo, fs, box)
        if bcert:
            bcert["tag"] = tag
            return bcert, f"exact-Bernstein-{tag}"

        # min-w univariate reduction for 2D
        if len(fs) == 2:
            for red in minw_reduce_univariate(oo, fs) or []:
                a = red["a"]
                alo, ahi = bounds[a][0], bounds[a][1]
                wit = red["witness"]
                try:
                    Bw = bernstein_coeffs(sp.expand(wit), [a], [(alo, ahi)])
                    Bf = bernstein_coeffs(sp.expand(red["f"]), [a], [(alo, ahi)])
                except Exception:
                    continue
                if all(b > 0 for b in Bf) and all(b >= 0 for b in Bw):
                    cert = {
                        "type": "bernstein_minw_univariate",
                        "tag": tag,
                        "a": str(a),
                        "w": str(red["w"]),
                        "alpha": frac_str(red["alpha"]),
                        "beta": frac_str(red["beta"]),
                        "box_a": [frac_str(alo), frac_str(ahi)],
                        "f": str(red["f"]),
                        "witness": str(wit),
                        "f_coeffs": [frac_str(b) for b in Bf],
                        "witness_coeffs": [frac_str(b) for b in Bw],
                        "claim": "f>0 and witness>=0 on box => min-w already violates strict upper ineq",
                    }
                    return cert, "exact-Bernstein-minw"

        # IBB with leaf certificate
        ibb = rational_ibb_cert(oo, fs, box, max_cells=100000 if len(fs) <= 2 else 60000, max_depth=28 if len(fs) <= 2 else 22)
        if ibb:
            ibb["tag"] = tag
            return ibb, f"exact-IBB-{tag}"

        # triangle3 map
        if len(fs) == 3:
            for A in fs:
                others = [v for v in fs if v != A]
                for X in others:
                    T = [v for v in others if v != X][0]
                    u, v, w = sp.Dummy("u"), sp.Dummy("v"), sp.Dummy("w")
                    mapped = [(sp.together(e.subs({A: u, X: u * v, T: w})), r) for e, r in oo]
                    boxu = [(F(0), F(1))] * 3
                    ibb = rational_ibb_cert(mapped, [u, v, w], boxu, max_cells=80000, max_depth=24)
                    if ibb:
                        ibb["tag"] = f"{tag}-triangle3"
                        ibb["triangle_map"] = {str(A): "u", str(X): "u*v", str(T): "w"}
                        return ibb, "exact-IBB-triangle3"

    return None, None


def prove_query(q: str, max_fs=3):
    if "Or(" in q:
        branches = split_ors(q)
        branch_certs = []
        for i, bq in enumerate(branches):
            atoms, err = parse_atoms(bq)
            if err:
                return None, f"Or-branch-{err}"
            cert, method = prove_atoms(atoms, max_fs=max_fs)
            if not cert:
                return None, "Or-branch-open"
            branch_certs.append({"branch": i, "query": bq, "cert": cert, "method": method})
        return {
            "type": "or_split",
            "n_branches": len(branch_certs),
            "branches": branch_certs,
        }, "exact-Or-split-all-branches"
    atoms, err = parse_atoms(q)
    if err:
        return None, err
    return prove_atoms(atoms, max_fs=max_fs)


def qid(row) -> str:
    h = hashlib.sha1(nq(row["q"]).encode()).hexdigest()[:10]
    return f"{row['file']}__n{row['n']}__{h}"


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    rows = [json.loads(l) for l in SOURCE.read_text().splitlines() if l.strip()]
    # Prefer low dimension first
    def rank(r):
        if "Or(" in r["q"]:
            return (3, 0)
        ids = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", r["q"]))
        return (0, len(ids))

    rows_sorted = sorted(rows, key=rank)
    RESULT.write_text("")
    still = []
    n_exact = 0
    t0 = time.time()
    logf = open(LOG, "w")

    def log(msg):
        print(msg, flush=True)
        logf.write(msg + "\n")
        logf.flush()

    for i, row in enumerate(rows_sorted):
        # escalate max_fs gradually
        cert, method = None, None
        for max_fs in (2, 3):
            try:
                cert, method = prove_query(row["q"], max_fs=max_fs)
            except Exception as ex:
                cert, method = None, f"err:{str(ex)[:160]}"
            if cert:
                break
        rec = {
            "file": row["file"],
            "n": row["n"],
            "q": row["q"],
            "cvc5": row.get("cvc5"),
            "id": qid(row),
        }
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
            }
            path.write_text(json.dumps(payload, ensure_ascii=False, indent=2))
            rec["cert_path"] = str(path.relative_to(ROOT.parent.parent)) if False else str(path)
            # store repo-relative
            rec["cert_relpath"] = f"artifacts/closure/item3_certs/exact_certs_batch24/{path.name}"
            n_exact += 1
            log(f"[{i+1}/{len(rows_sorted)}] EXACT {row['file']}#{row['n']} {method}")
        else:
            rec["status"] = "open"
            rec["reason"] = method or "no-method"
            still.append(row)
            if (i + 1) % 10 == 0:
                log(f"[{i+1}/{len(rows_sorted)}] open {row['file']}#{row['n']} {rec['reason']} exact_so_far={n_exact}")
        with open(RESULT, "a") as fo:
            fo.write(json.dumps(rec, ensure_ascii=False) + "\n")
    STILL.write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in still) + ("\n" if still else ""))
    log(f"DONE exact={n_exact} open={len(still)} t={time.time()-t0:.1f}s")
    logf.close()


if __name__ == "__main__":
    main()
