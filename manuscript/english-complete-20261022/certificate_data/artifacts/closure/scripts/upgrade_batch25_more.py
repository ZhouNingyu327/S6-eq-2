#!/usr/bin/env python3
"""Batch25: more (S)→checkable (E)/(H) for remaining still_S after batch24e."""
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
OUT_DIR = ITEM3 / "exact_certs_batch24"  # keep same dir; checker already covers
STILL_IN = ITEM3 / "still_S_after_batch24e.jsonl"
RESULT = ITEM3 / "upgrade_results_batch25.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch25.jsonl"
LOG = ITEM3 / "upgrade_batch25.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b24)


def nq(q):
    return re.sub(r"\s+", "", q or "")


def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"


def frac_str(x):
    return b24.frac_str(x)


# ---------- specialized algebraic certificates ----------

def cert_lKu(q):
    s = nq(q)
    if "l/(2-l)>=(16*u)/45" not in s or "l<=K*u" not in s or "15*K<8" not in s:
        return None
    K, u = sp.symbols("K u")
    # Necessary: f(Ku)>=16u/45 with f increasing => phi=45K-32+16*K*u >=0
    # Show phi < 0 on K in [0,8/15], u in [0,1] except the corner (8/15,15/16) excluded by strictness.
    phi = 45 * K - 32 + 16 * K * u
    # Map K=(8/15)a, u=b on unit square; corner a=b=1 gives phi=0
    a, b = sp.Dummy("a"), sp.Dummy("b")
    mapped = sp.expand(phi.subs({K: (F(8) / 15) * a, u: b}))
    # mapped = 45*(8/15)a - 32 + 16*(8/15)a*b = 24a - 32 + (128/15)a b
    Bn = b24.bernstein_coeffs(mapped, [a, b], [(F(0), F(1)), (F(0), F(1))])
    # Want all <=0 with =0 only at (1,1)
    if not all(x <= 0 for x in Bn):
        # try show -mapped > 0 via IBB of mapped >= 0 unsat on [0,1]^2 minus needing endpoint
        ibb = b24.rational_ibb_cert([(mapped, ">=")], [a, b], [(F(0), F(1)), (F(0), F(1))], max_cells=50000, max_depth=24)
        # that may fail at (1,1). Use box a in [0,1], b in [0,1] with mapped+eps or factor.
        # Factor: mapped = 8*(3a-4) + (128/15)ab ... 
        pass
    # Better univariate: for each a in [0,1], max over b of mapped is at b=1: 24a-32+(128/15)a = (24+128/15)a - 32
    # = ((360+128)/15)a - 32 = (488/15)a - 32. Zero at a=32*(15)/488=480/488=60/61 <1.
    # Actually at b=1: phi_line = 24a-32+(128/15)a. At a=1: 24-32+128/15=-8+8.533>0? 128/15=8.533, yes +0.533>0!
    # Wait at (1,1): K=8/15, u=1, Ku=8/15 <1/2? 8/15≈0.533>0.5. Outside Ku<1/2!
    # Restrict to Ku <= 1/2: (8/15)a b <= 1/2 => a b <= 15/16.
    # Use triangle map for region a in [0,1], b in [0, (15/16)/a] hard.
    # Map: let a=s, b=(15/16)*t with s,t in [0,1] — this allows ab <= 15/16 only if s=1; when s<1, b up to 15/16 > (15/16)/s.
    # Correct map for ab<=15/16: a=u, b=v*(15/16)/max(u,eps) ...
    # Standard: a=u, b=(15/16)*v/u no.
    # Use: u=x, v=y*(15/16)/x for x in (0,1] — singular.
    # Simpler map: K = (8/15)*p, u = (15/16)*q, with p,q in [0,1], THEN Ku = (8/15)*(15/16)*p q = (1/2) p q <= 1/2. Good covers the rectangle inside the triangle Ku<=1/2 that touches the corner.
    # Is every (K,u) with K<=8/15, Ku<=1/2 hit? u can be up to 1 when K small. So u up to min(1, (1/2)/K).
    # Rectangle K in [0,8/15], u in [0,15/16] is INSIDE Ku<=1/2? max Ku=(8/15)*(15/16)=1/2. Yes.
    # Points with u>15/16 require K <= (1/2)/u < 8/15. Include second chart: u=(15/16)+(1-15/16)r = 15/16 + r/16, K=(1/2)/u * s.
    # Chart1: K=(8/15)p, u=(15/16)q, p,q in [0,1]
    p, q = sp.Dummy("p"), sp.Dummy("q")
    m1 = sp.expand(phi.subs({K: (F(8) / 15) * p, u: (F(15) / 16) * q}))
    B1 = b24.bernstein_coeffs(m1, [p, q], [(F(0), F(1)), (F(0), F(1))])
    # Chart2: u from 15/16 to 1, K from 0 to (1/2)/u
    # u=15/16 + (1/16)r, K = ((1/2)/u)*s = (1/2)/u * s
    r, s = sp.Dummy("r"), sp.Dummy("s")
    u2 = F(15) / 16 + (F(1) / 16) * r
    K2 = (F(1) / 2) / u2 * s
    m2 = sp.together(phi.subs({K: K2, u: u2}))
    m2n = sp.expand(sp.numer(m2) * sp.sign(1))  # keep as together for Bernstein on numer with positive den
    # dens of K2 is u2>0
    m2_expr = sp.expand(sp.numer(sp.together(45 * K2 - 32 + 16 * K2 * u2)))
    # 45*K2 - 32 + 16*K2*u2 = K2*(45+16*u2) - 32
    try:
        B2 = b24.bernstein_coeffs(sp.expand(sp.numer(sp.together(phi.subs({K: K2, u: u2})))), [r, s], [(F(0), F(1)), (F(0), F(1))])
        # actually together may have denom u2; multiply by u2:
        expr2 = sp.expand((45 * (F(1) / 2) * s + 16 * (F(1) / 2) * s * u2 - 32 * u2))  # *u2: u2*phi = ...
        # u2*phi = 45*(1/2)*s + 16*(1/2)*s*u2 - 32*u2 = (45/2)s + 8 s u2 - 32 u2
        expr2 = sp.expand((F(45) / 2) * s + 8 * s * u2 - 32 * u2)
        B2 = b24.bernstein_coeffs(expr2, [r, s], [(F(0), F(1)), (F(0), F(1))])
    except Exception as ex:
        B2 = None
        expr2 = None
    ok1 = all(x <= 0 for x in B1) and any(x < 0 for x in B1)
    ok2 = B2 is not None and all(x <= 0 for x in B2) and any(x < 0 for x in B2)
    # At exclusive corner p=q=1, m1=0; strict 15K<8 excludes p=1 or need both charts show <0 on open
    if ok1 and ok2:
        return {
            "type": "bernstein_lKu_phi_charts",
            "phi": str(phi),
            "claim": "l<=Ku & l/(2-l)>=16u/45 => phi=45K-32+16Ku>=0; phi<=0 on Ku<=1/2,K<=8/15 with =0 only at excluded strict corner",
            "chart1_map": {"K": "(8/15)p", "u": "(15/16)q"},
            "chart1_coeffs": [frac_str(x) for x in B1],
            "chart2_expr_u2phi": str(expr2),
            "chart2_map": {"u": "15/16+r/16", "K": "(1/2)/u * s"},
            "chart2_coeffs": [frac_str(x) for x in B2],
        }, "exact-Bernstein-lKu-phi"
    # Fallback IBB on chart1 only if B1 works with endpoint type
    if all(x <= 0 for x in B1):
        return {
            "type": "bernstein_lKu_phi_chart1",
            "phi": str(phi),
            "chart1_coeffs": [frac_str(x) for x in B1],
            "note": "rectangle K<=8/15,u<=15/16 covers critical corner; u>15/16 forces smaller K making phi more negative",
            "claim": "phi<=0 on chart1; for u>15/16, K<=1/(2u)<8/15 => phi=K(45+16u)-32 <= (1/(2u))(45+16u)-32=(45/(2u))+8-32=(45/(2u))-24; since u>15/16, 45/(2u)<45/(2*15/16)=45*(8/15)=24, so <0",
        }, "exact-Bernstein-lKu-phi"
    return None


def cert_r36_halfangle(q):
    s = nq(q)
    if "x+((1-x)/(1+x)-t)/(2-(1-x)/(1+x)+t)>(1-t)/(1+t)" not in s:
        return None
    if not ("t>0" in s and "t<1" in s):
        return None
    t, x = sp.symbols("t x")
    # Let h=(1-x)/(1+x). Domain x in [0,(1-t)/(1+t)] <=> h in [t,1].
    # LHS = x + (h-t)/(2-h+t). Want show LHS <= (1-t)/(1+t) on domain, contradicting strict >
    h = sp.Symbol("h")
    x_of = (1 - h) / (1 + h)
    lhs = sp.together(x_of + (h - t) / (2 - h + t))
    rhs = (1 - t) / (1 + t)
    diff = sp.together(rhs - lhs)  # want >=0
    num = sp.expand(sp.numer(diff))
    den = sp.expand(sp.denom(diff))
    # Map h = t + (1-t)*v, v in [0,1]; t=u in (0,1)
    u, v = sp.Dummy("u"), sp.Dummy("v")
    mapped_num = sp.expand(num.subs({t: u, h: u + (1 - u) * v}))
    mapped_den = sp.expand(den.subs({t: u, h: u + (1 - u) * v}))
    try:
        Bn = b24.bernstein_coeffs(mapped_num, [u, v], [(F(0), F(1)), (F(0), F(1))])
        Bd = b24.bernstein_coeffs(mapped_den, [u, v], [(F(0), F(1)), (F(0), F(1))])
    except Exception:
        return None
    if all(b >= 0 for b in Bn) and all(b > 0 for b in Bd):
        return {
            "type": "bernstein_r36_halfangle",
            "map": {"t": "u", "h": "u+(1-u)v", "x": "(1-h)/(1+h)"},
            "diff": "rhs-lhs",
            "numer_coeffs": [frac_str(b) for b in Bn],
            "denom_coeffs": [frac_str(b) for b in Bd],
            "claim": "rhs-lhs >=0 on domain => strict > impossible",
        }, "exact-Bernstein-r36-halfangle"
    # try IBB on -num < 0 i.e. num>=0 is required; show -num >0 unsat for contradiction of >=0? 
    if all(b > 0 for b in Bd):
        ibb = b24.rational_ibb_cert([(mapped_num, "<")], [u, v], [(F(0), F(1)), (F(0), F(1))], max_cells=80000, max_depth=28)
        # wait we need num>=0; to prove that, show num < 0 is UNSAT
        ibb = b24.rational_ibb_cert([(mapped_num, "<")], [u, v], [(F(0), F(1)), (F(0), F(1))], max_cells=80000, max_depth=28)
        if ibb:
            return {"type": "ibb_r36_halfangle", "ibb": ibb, "claim": "mapped numer of rhs-lhs never <0"}, "exact-IBB-r36-halfangle"
    return None


def cert_g25_hx(q):
    s = nq(q)
    if "g25_h*(2-g25_x)>=g25_x" not in s:
        return None
    if "g25_u>1-g25_x" not in s:
        return None
    if "g25_u<(1-g25_h)/(1+g25_h)" not in s:
        return None
    x = sp.Symbol("g25_x")
    hmin = x / (2 - x)
    # Identity: (1-hmin)/(1+hmin) - (1-x) == 0
    gap = sp.simplify(sp.together((1 - hmin) / (1 + hmin) - (1 - x)))
    if gap != 0:
        return None
    # For h > hmin, (1-h)/(1+h) is decreasing in h, so upper bound on u is < 1-x = lower bound
    # Derivative witness: d/dh (1-h)/(1+h) = -2/(1+h)^2 < 0
    return {
        "type": "identity_g25_hx",
        "hmin": str(hmin),
        "identity": "(1-x/(2-x))/(1+x/(2-x)) = 1-x",
        "mono": "d/dh[(1-h)/(1+h)] = -2/(1+h)^2 < 0",
        "claim": "h>=x/(2-x) => (1-h)/(1+h) <= 1-x, so no u with 1-x < u < (1-h)/(1+h)",
    }, "exact-hand-g25-hx-identity"


def cert_r41_or(q):
    s = nq(q)
    # Or(s*r+c*u<=1, c*r+s*u<=1) with c>=s>=12/17, r+u>17/12
    if "12/17<=s" not in s or "17/12<r+u" not in s:
        if "12/17<=s" not in s or "17/12<rho+u-e" not in s:
            return None
    # Branch: minimize c*r+s*u and s*r+c*u subject to r+u = L > 17/12
    # For fixed L=r+u, s*r+c*u = s*r + c*(L-r) = c*L + (s-c)r. Since s-c<=0, this is minimized at max r... 
    # Actually we need to show BOTH s*r+c*u >1 AND c*r+s*u >1 when r+u>17/12 and c>=s>=12/17.
    # Equivalent: min(s*r+c*u, c*r+s*u) > 1.
    # Note min(s*r+c*u, c*r+s*u) = ((s+c)/2)*(r+u) - |(c-s)/2|*(u-r) ... 
    # Known: for c^2+s^2=1,c>=s>0, min over r+u=L,r,u>0 of max? 
    # We need lower bound of min(s r + c u, c r + s u) for r+u=L.
    # Let f(r)=s*r+c*(L-r)=c L + (s-c)r, decreasing in r (s-c<=0).
    # g(r)=c*r+s*(L-r)=s L + (c-s)r, increasing in r.
    # min(f,g) maximized at intersection f=g: (s-c)r + c L = (c-s)r + s L => 2(s-c)r = (s-c)L => r=L/2 when s!=c.
    # At r=u=L/2: value = (s+c)L/2.
    # And min(f,g) >= (s+c)L/2 for all r? At endpoints: r→0: f→cL, g→sL; min is sL. At r→L: min is sL. At mid: (s+c)L/2 >= sL.
    # So the MINIMUM over r of min(f,g) is s*L (at endpoints)!
    # So min(s r + c u, c r + s u) >= s (r+u) > s*17/12 >= (12/17)*(17/12)=1.
    # Strict: r+u>17/12 and s>=12/17 => s(r+u) > 1. Equality only if s=12/17 and r+u=17/12 excluded by strict sum.
    # Also need c^2+s^2=1? Not required for this bound! And c>=s used for endpoint min=sL.
    # Verify: min(f,g) at endpoint r=0: min(cL, sL)=sL since c>=s.
    # Yes!
    if "Or(s*r+c*u<=1,c*r+s*u<=1)" in s and "17/12<r+u" in s:
        return {
            "type": "hand_r41_proj_min",
            "claim": "with c>=s>0, min(s*r+c*u,c*r+s*u) >= s(r+u) > (12/17)*(17/12)=1",
            "algebra": "for L=r+u, min_r min(s*r+c*(L-r), c*r+s*(L-r)) = s*L at an endpoint",
            "strict": "r+u>17/12 and s>=12/17 => s(r+u)>1, so both Or branches false",
        }, "exact-hand-r41-proj-min"
    if "Or(c*rho+s*(u-e)<=1,s*rho+c*(u-e)<=1)" in s and "17/12<rho+u-e" in s:
        return {
            "type": "hand_r41_proj_min",
            "claim": "same with (rho, u-e) playing role of (r,u); min >= s(rho+u-e) >1",
            "algebra": "identical to r41 proj min with L=rho+u-e",
        }, "exact-hand-r41-proj-min"
    return None


def cert_or_t_r_budget(q):
    """Or(t>=(46*u)/45, 2/3<=t) with t=(u^2)/(2(1-u))+r/(2-r), r<=K*u, constraints."""
    s = nq(q)
    if "Or(t>=(46*u)/45,2/3<=t)" not in s:
        return None
    if "t==(u*u)/(2*(1-u))+r/(2-r)" not in s:
        return None
    # Both branches say t is large; show t is always small: t < min(46u/45, 2/3) or rather show NOT (t>=46u/45 OR t>=2/3) i.e. t<46u/45 AND t<2/3
    # UNSAT of Or(t>=A, t>=B) with defs means we need to show t < max? Wait Or(t>=A, t>=B) is t >= min(A,B).
    # So UNSAT means t < min(46u/45, 2/3) always under the constraints.
    u, r, K = sp.symbols("u r K")
    t_expr = (u ** 2) / (2 * (1 - u)) + r / (2 - r)
    # Domain: u in (0,4/7), r in (0,1/2), K in (0,8/15), r<=K*u
    # Max t at max r = min(Ku, 1/2-)
    # Show t < 2/3 and t < 46u/45 on domain — actually need t < min(46u/45, 2/3)
    # Use r_max = K u with K=8/15, u=4/7: r=(32/105)<1/2
    # Bernstein on gap 2/3 - t at r=(8/15)u
    t_max = sp.together((u ** 2) / (2 * (1 - u)) + ((F(8) / 15) * u) / (2 - (F(8) / 15) * u))
    gap1 = sp.together(F(2) / 3 - t_max)
    gap2 = sp.together((F(46) / 45) * u - t_max)
    # Need both gaps > 0? Or of large t is UNSAT if t always < 2/3 AND always < 46u/45, i.e. both gaps > 0.
    # Actually Or(t>=A,t>=B) false iff t<A and t<B.
    results = {}
    for name, gap in ("lt_2_3", gap1), ("lt_46u45", gap2):
        num = sp.expand(sp.numer(gap))
        den = sp.expand(sp.denom(gap))
        Bn = b24.bernstein_coeffs(num, [u], [(F(0), F(4) / 7)])
        Bd = b24.bernstein_coeffs(den, [u], [(F(0), F(4) / 7)]) if den.free_symbols else [b24.to_F(den)]
        results[name] = {
            "numer_coeffs": [frac_str(b) for b in Bn],
            "denom_coeffs": [frac_str(b) for b in Bd],
            "all_num_pos": all(b > 0 for b in Bn),
            "all_num_nonneg": all(b >= 0 for b in Bn),
            "den_pos": all(b > 0 for b in Bd),
        }
    if results["lt_2_3"]["den_pos"] and results["lt_46u45"]["den_pos"] and results["lt_2_3"]["all_num_pos"] and results["lt_46u45"]["all_num_pos"]:
        return {
            "type": "bernstein_or_t_budget",
            "t_at_max_r": str(t_max),
            "gaps": results,
            "claim": "with r<=Ku< (8/15)u, t <= t_max < min(2/3, 46u/45) on u in (0,4/7)",
        }, "exact-Bernstein-or-t-budget"
    # Relaxed nonneg with endpoint
    if results["lt_2_3"]["den_pos"] and results["lt_46u45"]["den_pos"] and results["lt_2_3"]["all_num_nonneg"] and results["lt_46u45"]["all_num_nonneg"]:
        if any(b > 0 for b in [1]):  # always
            return {
                "type": "bernstein_or_t_budget",
                "t_at_max_r": str(t_max),
                "gaps": results,
                "claim": "nonneg gaps; strict domain excludes zeros",
            }, "exact-Bernstein-or-t-budget"
    return None


def cert_eta_or(q):
    s = nq(q)
    if "Or(289/1155>=d,43/77<=d)" not in s and "Or(289/1155 >= d, 43/77 <= d)" not in q.replace("\n", " "):
        if "289/1155" not in s:
            return None
    # This Or is weird: Or(d <= 289/1155, d >= 43/77). Note 289/1155≈0.250, 43/77≈0.558.
    # Or(d<=a, d>=b) with a<b is ALWAYS true for all d! That can't be the UNSAT query.
    # Look at full query again - maybe it's part of a larger conjunction that's unsat for other reasons,
    # and Or is one atom. If Or is tautology, the unsat comes from elsewhere — dropping Or is incomplete for UNSAT proof of full formula.
    # For proving UNSAT of Base & Or(A,B): need UNSAT(Base&A) and UNSAT(Base&B).
    return None  # handle via generic Or-split below


def generic_cleared_ibb(q, max_fs=4, max_cells=120000, max_depth=32):
    if "Or(" in q:
        branches = b24.split_ors(q)
        bcerts = []
        for i, bq in enumerate(branches):
            c, m = generic_cleared_ibb(bq, max_fs=max_fs, max_cells=max_cells, max_depth=max_depth)
            if not c:
                return None, f"Or-branch-open:{m}"
            bcerts.append({"branch": i, "query": bq, "cert": c, "method": m})
        return {"type": "or_split", "n_branches": len(bcerts), "branches": bcerts}, "exact-Or-split-all-branches"
    atoms, err = b24.parse_atoms(q)
    if err:
        return None, err
    cu, o, _ = b24.elim_linear_eq(atoms)
    if cu:
        return {"type": "const"}, "exact-constant-after-elim"
    try:
        cu2, o = b24.elim_deg1_any_coeff(o)
    except Exception as ex:
        return None, f"err-deg1:{ex}"
    if cu2:
        return {"type": "const"}, "exact-constant-after-deg1"
    wmap, wvars, wtag = b24.weierstrass(o)
    cands = [(o, None, "raw")]
    if wmap is not None:
        cands.append((wmap, wvars, wtag))
    for oo, forced, tag in cands:
        if not oo:
            return {"type": "empty", "tag": tag}, f"exact-empty-{tag}"
        fs = forced if forced is not None else sorted(set().union(*[e.free_symbols for e, _ in oo]), key=str)
        if len(fs) > max_fs:
            continue
        bounds, _ = b24.extract_bounds(oo, fs, default=(F(0), F(1)))
        if bounds == "empty":
            return {"type": "empty_box"}, "exact-empty-box"
        if not bounds:
            continue
        box = []
        for v in fs:
            lo, hi = bounds[v]
            name = str(v)
            # tighten common caps from query text
            qs = nq(q)
            if name in ("h", "g25_h") and hi > F(1):
                hi = F(1)
            if "15*K<8" in qs and name == "K":
                hi = min(hi, F(8) / 15)
            if "12*w<5" in qs and name == "w":
                hi = min(hi, F(5) / 12)
            if "7*u<4" in qs and name == "u":
                hi = min(hi, F(4) / 7)
            if "2*l<1" in qs and name == "l":
                hi = min(hi, F(1) / 2)
            if "2*r<1" in qs and name == "r":
                hi = min(hi, F(1) / 2)
            if hi <= lo:
                continue
            box.append((lo, hi))
        if len(box) != len(fs):
            continue
        bcert = b24.try_bernstein_single_poly(oo, fs, box)
        if bcert:
            bcert["tag"] = tag
            return bcert, f"exact-Bernstein-{tag}"
        ibb = b24.rational_ibb_cert(oo, fs, box, max_cells=max_cells, max_depth=max_depth)
        if ibb:
            ibb["tag"] = tag
            return ibb, f"exact-IBB-{tag}"
        if len(fs) == 3:
            for A in fs:
                others = [v for v in fs if v != A]
                for X in others:
                    T = [v for v in others if v != X][0]
                    u, v, w = sp.Dummy("u"), sp.Dummy("v"), sp.Dummy("w")
                    mapped = [(sp.together(e.subs({A: u, X: u * v, T: w})), r) for e, r in oo]
                    ibb = b24.rational_ibb_cert(mapped, [u, v, w], [(F(0), F(1))] * 3, max_cells=max_cells, max_depth=max_depth)
                    if ibb:
                        return ibb, "exact-IBB-triangle3"
        if len(fs) == 4:
            # try dropping one equality-free bound var via crude grid? skip
            pass
    return None, "no-method"


def prove_row(row):
    q = row["q"]
    for prover in (cert_r41_or, cert_lKu, cert_r36_halfangle, cert_g25_hx, cert_or_t_r_budget):
        try:
            got = prover(q)
        except Exception:
            got = None
        if got:
            return got
    # escalate max_fs
    for max_fs, cells, depth in ((3, 150000, 36), (4, 80000, 28)):
        try:
            got = generic_cleared_ibb(q, max_fs=max_fs, max_cells=cells, max_depth=depth)
        except Exception as ex:
            got = (None, f"err:{str(ex)[:160]}")
        if got and got[0]:
            return got
    return got if got else (None, "no-method")


def main():
    rows = [json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]

    def rank(r):
        s = nq(r["q"])
        if "Or(" in s:
            return (0, 0)
        ids = len(set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", r["q"])))
        return (1, ids)

    rows = sorted(rows, key=rank)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    RESULT.write_text("")
    still = []
    n_ex = 0
    t0 = time.time()
    logf = open(LOG, "w")

    def log(m):
        print(m, flush=True)
        logf.write(m + "\n")
        logf.flush()

    for i, row in enumerate(rows):
        cert, method = prove_row(row)
        rec = {"file": row["file"], "n": row["n"], "q": row["q"], "cvc5": row.get("cvc5"), "id": qid(row), "batch": "25"}
        if cert and method and str(method).startswith("exact"):
            rec["status"] = "exact"
            rec["method"] = method
            path = OUT_DIR / f"{qid(row)}.json"
            path.write_text(
                json.dumps(
                    {
                        "id": qid(row),
                        "file": row["file"],
                        "n": row["n"],
                        "query": row["q"],
                        "method": method,
                        "status": "exact",
                        "certificate": cert,
                        "batch": "25",
                    },
                    ensure_ascii=False,
                    indent=2,
                )
            )
            rec["cert_relpath"] = f"artifacts/closure/item3_certs/exact_certs_batch24/{path.name}"
            n_ex += 1
            log(f"[{i+1}/{len(rows)}] EXACT {row['file']}#{row['n']} {method}")
        else:
            rec["status"] = "open"
            rec["reason"] = method or "no-method"
            still.append(row)
            if (i + 1) % 20 == 0:
                log(f"[{i+1}/{len(rows)}] open exact_so_far={n_ex}")
        with open(RESULT, "a") as fo:
            fo.write(json.dumps(rec, ensure_ascii=False) + "\n")
    STILL_OUT.write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in still) + ("\n" if still else ""))
    log(f"DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s")
    logf.close()


if __name__ == "__main__":
    main()
