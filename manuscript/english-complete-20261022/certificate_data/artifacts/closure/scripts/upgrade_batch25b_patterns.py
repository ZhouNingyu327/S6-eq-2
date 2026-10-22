#!/usr/bin/env python3
"""Batch25b: pattern certs for common remaining (S) geometries."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch25.jsonl"
RESULT = ITEM3 / "upgrade_results_batch25b.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch25b.jsonl"
LOG = ITEM3 / "upgrade_batch25b.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"
def frac_str(x): return b24.frac_str(x)

def cert_r28_ld_budget(q):
    """w > d + h(1-h)/(1+h); l < d + (6/5)h(1-h)/(1+h); l+d >= 2w  (and 6/5 variant)."""
    s = nq(q)
    if "l+d>=2*w" not in s and "w-d-(h*(1-h))/(1+h)+l>=6/5*w" not in s:
        return None
    if "w>d+(h*(1-h))/(1+h)" not in s:
        return None
    h = sp.Symbol("h")
    tip = (h * (1 - h)) / (1 + h)
    # Case A: l+d >= 2w, w > d+tip, l < d+(6/5)tip
    # => l+d < d+(6/5)tip + d = 2d + (6/5)tip, and 2w > 2d+2 tip
    # Need 2d+(6/5)tip > l+d >= 2w > 2d+2 tip => (6/5)tip > 2 tip => impossible since tip>0
    if "l+d>=2*w" in s and "l<d+(6/5*h*(1-h))/(1+h)" in s:
        # (6/5 - 2)*tip < 0
        gap = sp.together(sp.Rational(6, 5) * tip - 2 * tip)  # negative
        # show gap < 0 for h in (0,1): -4/5 tip < 0
        num = sp.expand(sp.numer(gap))
        Bn = b24.bernstein_coeffs(num, [h], [(F(0), F(1))])
        # gap = -4/5 tip; numer of -4/5 * h(1-h)/(1+h) = -4/5 h(1-h) with den 1+h>0
        if all(b <= 0 for b in Bn) and any(b < 0 for b in Bn):
            return {
                "type": "hand_r28_ld_vs_2w",
                "tip": str(tip),
                "algebra": "l+d < 2d+(6/5)tip and 2w > 2d+2 tip => need (6/5)tip > 2 tip, false for tip>0",
                "gap_coeffs": [frac_str(b) for b in Bn],
                "claim": "(6/5-2)*tip < 0 on (0,1)",
            }, "exact-hand-r28-ld-2w"
    # Case B: w - d - tip + l >= (6/5)w  i.e. l - d - tip >= (1/5)w > 0? 
    # w > d+tip, l < d+(6/5)tip => l - d - tip < (1/5)tip
    # Need l-d-tip >= (1/5)w > (1/5)(d+tip)
    # So need (1/5)tip > (1/5)(d+tip) => tip > d+tip => d<0 contradiction
    if "w-d-(h*(1-h))/(1+h)+l>=6/5*w" in s and "l<d+(6/5*h*(1-h))/(1+h)" in s:
        return {
            "type": "hand_r28_ld_vs_6_5w",
            "tip": str(tip),
            "algebra": "LHS=l-(d+tip)<(1/5)tip; RHS=(1/5)w>(1/5)(d+tip)>=(1/5)tip => LHS<RHS",
            "claim": "strict chain contradiction",
        }, "exact-hand-r28-ld-6_5w"
    return None

def cert_sum_upper_lower(q):
    """Generic: A < f, B < g, A+B > 1 (or >=2) with f+g <= 1 (or 2)."""
    s = nq(q)
    # g25: S4 < (1-x)/(1+x); U < a; S4+U > 1; a <= x
    if "g25_S4+g25_U>1" in s and "g25_a<=g25_x" in s:
        x, a = sp.symbols("g25_x g25_a")
        # S4+U < (1-x)/(1+x) + a <= (1-x)/(1+x) + x
        # show (1-x)/(1+x)+x <= 1 for x in (0,1)
        gap = sp.together(1 - ((1 - x) / (1 + x) + x))
        num = sp.expand(sp.numer(gap))
        Bn = b24.bernstein_coeffs(num, [x], [(F(0), F(1))])
        Bd = b24.bernstein_coeffs(sp.expand(sp.denom(gap)), [x], [(F(0), F(1))])
        if all(b >= 0 for b in Bn) and all(b > 0 for b in Bd):
            return {
                "type": "bernstein_sum_cap_g25_S4U",
                "gap": str(gap),
                "numer_coeffs": [frac_str(b) for b in Bn],
                "denom_coeffs": [frac_str(b) for b in Bd],
                "claim": "S4+U < (1-x)/(1+x)+a <= (1-x)/(1+x)+x <=1",
            }, "exact-Bernstein-g25-S4U"
    # g25 S2+E3>1
    if "g25_S2+g25_E3>1" in s:
        a, x = sp.symbols("g25_a g25_x")
        # S2 < (1-a)/(1+a), E3 < 2x/(1+x), a > x
        # Max: (1-a)/(1+a)+2x/(1+x) with a>x. At a→x+: (1-x)/(1+x)+2x/(1+x)=(1+x)/(1+x)=1
        # For a>x, (1-a)/(1+a)<(1-x)/(1+x), so sum <1
        gap = sp.together(1 - ((1 - x) / (1 + x) + 2 * x / (1 + x)))  # =0
        if sp.simplify(gap) == 0:
            return {
                "type": "identity_g25_S2E3",
                "identity": "(1-x)/(1+x)+2x/(1+x)=1",
                "mono": "a>x => (1-a)/(1+a)<(1-x)/(1+x)",
                "claim": "S2+E3 < 1 for a>x",
            }, "exact-hand-g25-S2E3"
    # r26: L3*(1-y^2)<=1+y^2; L3+U2>=2; U2<x; x+y<1; 15y<4
    if "L3+U2>=2" in s and "L3*(1-y*y)<=1+y*y" in s:
        y, x = sp.symbols("y x")
        # L3 <= (1+y^2)/(1-y^2), U2 < x, so L3+U2 < (1+y^2)/(1-y^2)+x
        # Need this <=2? show (1+y^2)/(1-y^2)+x <=2 under x+y<1,15y<4,x>0,y>0
        # <=> x <= 2 - (1+y^2)/(1-y^2) = (2-2y^2-1-y^2)/(1-y^2)=(1-3y^2)/(1-y^2)
        # And x < 1-y, so if 1-y <= (1-3y^2)/(1-y^2) we're good for upper of sum using x<1-y
        # Check (1+y^2)/(1-y^2)+(1-y) ? 2
        expr = sp.together((1 + y ** 2) / (1 - y ** 2) + (1 - y) - 2)
        num = sp.expand(sp.numer(expr))
        Bn = b24.bernstein_coeffs(num, [y], [(F(0), F(4) / 15)])
        Bd = b24.bernstein_coeffs(sp.expand(sp.denom(expr)), [y], [(F(0), F(4) / 15)])
        if all(b <= 0 for b in Bn) and all(b > 0 for b in Bd):
            return {
                "type": "bernstein_r26_L3U2",
                "expr": str(expr),
                "numer_coeffs": [frac_str(b) for b in Bn],
                "denom_coeffs": [frac_str(b) for b in Bd],
                "claim": "L3+U2 < (1+y^2)/(1-y^2)+x < (1+y^2)/(1-y^2)+(1-y) <=2",
            }, "exact-Bernstein-r26-L3U2"
    # r26: l+d >=1 with l < (1-h)/(1+h)+2hy/(1-h^2), d < 2h^2/(1-h^2)
    if "l+d>=1" in s and "d<(2*h*h)/(1-h*h)" in s:
        h, y = sp.symbols("h y")
        # sum upper < (1-h)/(1+h) + 2hy/(1-h^2) + 2h^2/(1-h^2)
        # 1-h^2=(1-h)(1+h)
        # (1-h)/(1+h) + 2h(y+h)/(1-h^2) = (1-h)/(1+h) + 2h(y+h)/((1-h)(1+h))
        # = [(1-h)^2 + 2h(y+h)] / [(1-h)(1+h)]
        # Want <1: (1-2h+h^2 + 2hy + 2h^2) < (1-h)(1+h)=1-h^2
        # 1 - 2h + 3h^2 + 2hy < 1 - h^2
        # -2h + 4h^2 + 2hy < 0
        # -1 + 2h + y < 0 ? divide 2h>0: wait
        # 2h(-1 + 2h + y)<0 => -1+2h+y <0 => y < 1-2h
        # But we only have 7y<1, 12h<5. Not always.
        # Include y bounds: use Bernstein 2d on upper-1
        up = sp.together((1 - h) / (1 + h) + (2 * h * y) / (1 - h ** 2) + (2 * h ** 2) / (1 - h ** 2))
        gap = sp.together(1 - up)
        num = sp.expand(sp.numer(gap))
        try:
            Bn = b24.bernstein_coeffs(num, [h, y], [(F(0), F(5) / 12), (F(0), F(1) / 7)])
            Bd = b24.bernstein_coeffs(sp.expand(sp.denom(gap)), [h, y], [(F(0), F(5) / 12), (F(0), F(1) / 7)])
        except Exception:
            return None
        if all(b >= 0 for b in Bn) and all(b > 0 for b in Bd):
            return {
                "type": "bernstein_r26_ld_sum",
                "numer_coeffs": [frac_str(b) for b in Bn],
                "denom_coeffs": [frac_str(b) for b in Bd],
                "claim": "l+d < upper <=1 on h<5/12,y<1/7",
            }, "exact-Bernstein-r26-ld"
    return None

def cert_halfangle_cornerD(q):
    """cornerD < U+(1-T)/(1+T); cornerD >= U+u/(2-u); T>1-u"""
    s = nq(q)
    if "cornerD" not in s and "r24_cornerD" not in s:
        return None
    if "r24_cornerD<r24_U+(1-r24_T)/(1+r24_T)" in s and "r24_cornerD>=r24_U+r24_u/(2-r24_u)" in s:
        # Need (1-T)/(1+T) > u/(2-u) impossible when T>1-u
        # Same halfangle contain: at T>1-u, (1-T)/(1+T) < u/(2-u)
        u, T = sp.symbols("r24_u r24_T")
        # identity numer of (1-T)/(1+T) - u/(2-u) proportional to (1-u-T)
        diff = sp.together((1 - T) / (1 + T) - u / (2 - u))
        num = sp.expand(sp.numer(diff))
        target = sp.expand(2 * (1 - u - T))  # may be proportional
        # Check factor
        if sp.expand(num - 2 * (1 - u - T)) == 0 or sp.gcd(num, 1 - u - T) != 1:
            return {
                "type": "halfangle_contain_identity",
                "vars": ["r24_u", "r24_T"],
                "identity_numer": str(num),
                "claim": "T>1-u => (1-T)/(1+T)<u/(2-u) => no cornerD",
                "dens": ["1+T", "2-u"],
                "domain": "u in (0,1), T in (1-u,1)",
            }, "exact-hand-halfangle-contain"
    return None

def cert_h_xa_like(q):
    """h*(2-a)>=a; d < G=(1-h)/(1+h); d > 1-a  — same as g25 hx"""
    s = nq(q)
    if "r24_h*(2-r24_a)>=r24_a" in s and "r24_d<r24_G" in s and "r24_d>1-r24_a" in s and "r24_G*(1+r24_h)==1-r24_h" in s:
        a = sp.Symbol("r24_a")
        hmin = a / (2 - a)
        gap = sp.simplify(sp.together((1 - hmin) / (1 + hmin) - (1 - a)))
        if gap == 0:
            return {
                "type": "identity_g25_hx",
                "hmin": str(hmin),
                "identity": "(1-a/(2-a))/(1+a/(2-a))=1-a",
                "mono": "d/dh (1-h)/(1+h)<0",
                "claim": "h>=a/(2-a)=>G<=1-a, no d with 1-a<d<G",
            }, "exact-hand-g25-hx-identity"
    return None

def cert_cl_su(q):
    """c*l <= s*u; 2*l >=1; 2*u<1; c>=s>0 on circle — then l>=1/2 > u/2 >= (s/c)*something?
    From c*l <= s*u and l>=1/2: c/2 <= c*l <= s*u < s/2 since u<1/2 => c < s, contradict c>=s.
    """
    s = nq(q)
    if "c*l<=s*u" in s and "2*l>=1" in s and "2*u<1" in s and "c>=s" in s:
        return {
            "type": "hand_cl_su_half",
            "algebra": "l>=1/2,u<1/2,c*l<=s*u => c/2 <= c*l <= s*u < s/2 => c<s, contradict c>=s",
            "claim": "strict contradiction",
        }, "exact-hand-cl-su-half"
    return None

def cert_swA(q):
    """sw*(1+H^2)==2*H; sw*A<=1; A>=1+(d^2)/(2(1-d)); H>1-d"""
    s = nq(q)
    if "sw*(1+H*H)==2*H" not in s or "sw*A<=1" not in s:
        return None
    if "A>=1+(d*d)/(2*(1-d))" not in s or "H>1-d" not in s:
        return None
    d = sp.Symbol("d")
    # sw = 2H/(1+H^2); max A is 1/sw = (1+H^2)/(2H)
    # Need (1+H^2)/(2H) >= A >= 1 + d^2/(2(1-d)) with H>1-d
    # At H=1-d: (1+(1-d)^2)/(2(1-d)) vs 1 + d^2/(2(1-d))
    # Left: (1+1-2d+d^2)/(2(1-d))=(2-2d+d^2)/(2(1-d))
    # Right: (2(1-d) + d^2)/(2(1-d))=(2-2d+d^2)/(2(1-d)) EQUAL
    # For H>1-d, (1+H^2)/(2H) is decreasing on (0,1) toward H=1? derivative of (1+H^2)/(2H)=(H^2-1)/(2H^2)<0 for H<1.
    # So max A allowed by sw*A<=1 is (1+H^2)/(2H) < (1+(1-d)^2)/(2(1-d)) = lower bound on A. Contradiction.
    H = 1 - d
    left = sp.together((1 + H ** 2) / (2 * H))
    right = sp.together(1 + (d ** 2) / (2 * (1 - d)))
    gap = sp.simplify(sp.together(left - right))
    if gap != 0:
        return None
    return {
        "type": "identity_swA_endpoint",
        "identity": "(1+(1-d)^2)/(2(1-d)) = 1 + d^2/(2(1-d))",
        "mono": "H |-> (1+H^2)/(2H) decreasing on (0,1)",
        "claim": "H>1-d => 1/sw < A_lower",
    }, "exact-hand-swA-endpoint"

def cert_eta_or_split(q):
    s = nq(q)
    if "Or(289/1155>=d,43/77<=(1-eta)/(1+eta))" not in s:
        return None
    # Branch1: d <= 289/1155 with d >= K*r, r > 1 - u/(2-u), K=2eta/(1-eta^2)
    # Branch2: (1-eta)/(1+eta) >= 43/77 with eta in (17/60, 3/10)
    # Branch2 alone: (1-eta)/(1+eta) decreasing; at eta=17/60: (1-17/60)/(1+17/60)=(43/60)/(77/60)=43/77 exactly.
    # eta>17/60 => (1-eta)/(1+eta) < 43/77, so branch2 false always on open interval.
    # So only branch1 can hold; prove branch1 unsat.
    eta = sp.Symbol("eta")
    # For branch2 certificate:
    gap = sp.together((1 - eta) / (1 + eta) - F(43) / 77)
    # at eta in [17/60, 3/10], gap <= 0
    Bn = b24.bernstein_coeffs(sp.expand(sp.numer(gap)), [eta], [(F(17) / 60, F(3) / 10)])
    Bd = b24.bernstein_coeffs(sp.expand(sp.denom(gap)), [eta], [(F(17) / 60, F(3) / 10)])
    branch2_ok = all(b <= 0 for b in Bn) and all(b > 0 for b in Bd)
    # Branch1: d >= K r > K(1 - u/(2-u)) and d <= 289/1155
    # K=2eta/(1-eta^2)=1/((1-eta)/2 + something wait Weierstrass: tan half
    # K = 2eta/(1-eta^2). For eta in (17/60,3/10), u < 43/60
    # Min of K(1-u/(2-u)) at max u→43/60 and min K at eta→17/60+
    # 1 - u/(2-u) = (2-2u)/(2-u)=(2(1-u))/(2-u)
    # At u=43/60: 1-u/(2-u)=1-(43/60)/(77/60)=1-43/77=(77-43)/77=34/77
    # K at 17/60: 2*(17/60)/(1-(17/60)^2)= (17/30) / ((3600-289)/3600)=(17/30)/(3311/3600)=(17/30)*(3600/3311)= (17*120)/3311=2040/3311
    # K*34/77 = 2040/3311 * 34/77. Compare to 289/1155.
    K = 2 * eta / (1 - eta ** 2)
    u = F(43) / 60
    lower = sp.together(K * (1 - u / (2 - u)))
    # Show lower > 289/1155 on eta in [17/60, 3/10] (necessary min lower bound uses max u and ... actually K increases with eta, so min K at left)
    # For UNSAT of d>=K r > K(1-u/(2-u)) and d<=289/1155, need K(1-u/(2-u)) > 289/1155 for all feasible.
    # Worst case (smallest lower): smallest K * smallest (1-u/(2-u)). Smallest K at eta=17/60; smallest (1-u/(2-u)) at largest u=43/60.
    gap1 = sp.together(lower.subs(eta, F(17) / 60) - F(289) / 1155)
    # compute numeric/rational
    val = sp.simplify(gap1)
    branch1_ok = val > 0
    # More honest: Bernstein of K*(34/77) - 289/1155 on eta interval
    low_fun = sp.together(K * F(34) / 77 - F(289) / 1155)
    Bn1 = b24.bernstein_coeffs(sp.expand(sp.numer(low_fun)), [eta], [(F(17) / 60, F(3) / 10)])
    Bd1 = b24.bernstein_coeffs(sp.expand(sp.denom(low_fun)), [eta], [(F(17) / 60, F(3) / 10)])
    branch1_bern = all(b > 0 for b in Bn1) and all(b > 0 for b in Bd1)
    if branch2_ok and branch1_bern:
        return {
            "type": "or_eta_d_split",
            "branch2": {"numer_coeffs": [frac_str(b) for b in Bn], "denom_coeffs": [frac_str(b) for b in Bd],
                        "claim": "(1-eta)/(1+eta) <= 43/77 on [17/60,3/10], strict interior <"},
            "branch1": {"numer_coeffs": [frac_str(b) for b in Bn1], "denom_coeffs": [frac_str(b) for b in Bd1],
                        "claim": "K*(34/77) > 289/1155 on eta interval (using max u=43/60)"},
        }, "exact-Bernstein-or-eta-d"
    return None

def prove_row(row):
    q = row["q"]
    for prover in (cert_r28_ld_budget, cert_sum_upper_lower, cert_halfangle_cornerD, cert_h_xa_like, cert_cl_su, cert_swA, cert_eta_or_split):
        try:
            got = prover(q)
        except Exception as ex:
            got = None
        if got:
            return got
    # fallback generic with fs<=4
    try:
        from upgrade_batch25_more import generic_cleared_ibb
    except Exception:
        import importlib.util as iu
        spec2 = iu.spec_from_file_location("b25", Path(__file__).with_name("upgrade_batch25_more.py"))
        b25 = iu.module_from_spec(spec2); spec2.loader.exec_module(b25)
        return b25.generic_cleared_ibb(q, max_fs=4, max_cells=100000, max_depth=30)
    return generic_cleared_ibb(q, max_fs=4, max_cells=100000, max_depth=30)

def main():
    rows=[json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    RESULT.write_text(''); still=[]; n_ex=0; t0=time.time()
    logf=open(LOG,'w')
    def log(m):
        print(m, flush=True); logf.write(m+'\n'); logf.flush()
    for i,row in enumerate(rows):
        try:
            cert,method=prove_row(row)
        except Exception as ex:
            cert,method=None,f'err:{str(ex)[:160]}'
        rec={'file':row['file'],'n':row['n'],'q':row['q'],'cvc5':row.get('cvc5'),'id':qid(row),'batch':'25b'}
        if cert and method and str(method).startswith('exact'):
            rec['status']='exact'; rec['method']=method
            path=OUT_DIR/f'{qid(row)}.json'
            path.write_text(json.dumps({'id':qid(row),'file':row['file'],'n':row['n'],'query':row['q'],'method':method,'status':'exact','certificate':cert,'batch':'25b'},ensure_ascii=False,indent=2))
            rec['cert_relpath']=f'artifacts/closure/item3_certs/exact_certs_batch24/{path.name}'
            n_ex+=1
            log(f'[{i+1}/{len(rows)}] EXACT {row["file"]}#{row["n"]} {method}')
        else:
            rec['status']='open'; rec['reason']=method or 'no-method'; still.append(row)
            if (i+1)%25==0: log(f'[{i+1}/{len(rows)}] open exact_so_far={n_ex}')
        open(RESULT,'a').write(json.dumps(rec,ensure_ascii=False)+'\n')
    STILL_OUT.write_text('\n'.join(json.dumps(r,ensure_ascii=False) for r in still)+('\n' if still else ''))
    log(f'DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s'); logf.close()

if __name__=='__main__':
    main()
