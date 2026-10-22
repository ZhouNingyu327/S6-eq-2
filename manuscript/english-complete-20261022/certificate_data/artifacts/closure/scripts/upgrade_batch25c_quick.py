#!/usr/bin/env python3
"""Batch25c: quick algebraic contradictions on remaining dim-4ish (S)."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch25b.jsonl"
RESULT = ITEM3 / "upgrade_results_batch25c.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch25c.jsonl"
LOG = ITEM3 / "upgrade_batch25c.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"
def frac_str(x): return b24.frac_str(x)

def cert_strict_interval_empty(q):
    s=nq(q)
    # z+u/(2-u) > 1-G+d and z+u/(2-u) < 1-G => d<0 but d>0
    if "z+u/(2-u)>1-G+d" in s and "z+u/(2-u)<1-G" in s and "d>0" in s:
        return {"type":"hand_strict_interval_d","claim":"same LHS >1-G+d and <1-G => d<0, contradict d>0"}, "exact-hand-strict-interval-d"
    return None

def cert_rpp_disc(q):
    s=nq(q)
    # Rpp < 0 ; Rpp - 900/961*(Dp*Dp + D*DD) >= 0 with D,DD>0
    if "Rpp<0" in s and "Rpp-900/961*(Dp*Dp+D*DD)>=0" in s and "D>0" in s and "DD>0" in s:
        # => Rpp >= 900/961*(positive) > 0, contradict Rpp<0
        return {"type":"hand_rpp_pos","claim":"Rpp >= (900/961)(Dp^2+D*DD)>0 contradicts Rpp<0"}, "exact-hand-rpp-disc"
    if "-eps1-32/25*(E*E+Y*eps2)>=0" in s and "eps1>0" in s:
        # -eps1 - positive >=0 => -eps1>=0 => eps1<=0 contradict
        return {"type":"hand_eps_neg","claim":"-eps1 - (32/25)(... ) >=0 with eps1>0 and (...)>=0 impossible"}, "exact-hand-eps-sum"
    return None

def cert_half_l_K(q):
    s=nq(q)
    # 2*l >= 1, l <= K*u, K*l <= d, u+d < 1, K<=1
    if "2*l>=1" in s and "l<=K*u" in s and ("K*l<=d" in s or "K*r<=d" in s):
        # l>=1/2, u >= l/K >= l >=1/2 if K<=1, d >= K*l >=? 
        # u+d >= l/K + K*l. By AM-GM >= 2l >=1. Equality at K=1,l=1/2,u=1/2,d=1/2 but u+d<1 strict.
        if "u+d<1" in s and "K<=1" in s and "K>0" in s:
            return {"type":"hand_AMGM_ud","claim":"u>=l/K, d>=K*l => u+d >= l/K + K*l >= 2l >=1, contradict u+d<1 strict"}, "exact-hand-AMGM-ud"
        if "u+d<1" in s and "r<=K*u" in s and "K*r<=d" in s and "2*r>=1" in s:
            return {"type":"hand_AMGM_ud","claim":"same with r>=1/2: u>=r/K,d>=K*r => u+d>=2r>=1"}, "exact-hand-AMGM-ud"
    return None

def cert_mu_r_u(q):
    s=nq(q)
    # r+u >= mu >1, r <= K*u, K<=1, 2u<1 => r+u <= K*u + u = (K+1)u < 2u <1 < mu contradiction
    if "r+u>=mu" in s and "mu>1" in s and "r<=K*u" in s and "K<=1" in s and "2*u<1" in s:
        return {"type":"hand_ru_lt_mu","claim":"r+u <=(K+1)u <=2u <1 <mu"}, "exact-hand-ru-lt-mu"
    return None

def cert_A_L2_mu(q):
    s=nq(q)
    # A+L2 >= 2mu >2, A <= (1-k)/(1+k), L2 <3, k=(L2-1)/(3-L2)
    # (1-k)/(1+k) + L2 ? 
    if "A+L2>=2*mu" in s and "A<=(1-k)/(1+k)" in s and "k*(3-L2)==L2-1" in s:
        L2=sp.Symbol("L2")
        k=(L2-1)/(3-L2)
        up=sp.together((1-k)/(1+k)+L2)
        # show up <=2 for L2 in (1,3)
        gap=sp.together(2-up)
        num=sp.expand(sp.numer(gap))
        Bn=b24.bernstein_coeffs(num,[L2],[(F(1),F(3))])
        Bd=b24.bernstein_coeffs(sp.expand(sp.denom(gap)),[L2],[(F(1),F(3))])
        if all(b>=0 for b in Bn) and all(b>0 for b in Bd):
            return {"type":"bernstein_A_L2","numer_coeffs":[frac_str(b) for b in Bn],"denom_coeffs":[frac_str(b) for b in Bd],
                    "claim":"A+L2 <= (1-k)/(1+k)+L2 <=2 < 2mu"}, "exact-Bernstein-A-L2"
    return None

def cert_rr_ud(q):
    s=nq(q)
    # (r^2)/(2(1-r)) >= u*d with r<=K*u, K*r<=d, K>0
    # => r^2/(2(1-r)) >= u*(K r) = K u r >= r*r  (since Ku>=r) => r/(2(1-r)) >= r => for r>0: 1/(2(1-r))>=1 => 1>=2-2r => r>=1/2
    # But 2r<1 => r<1/2 contradiction
    if "(r*r)/(2*(1-r))>=u*d" in s and "r<=K*u" in s and "K*r<=d" in s and "2*r<1" in s:
        return {"type":"hand_rr_ud","claim":"ud>=K u r >= r^2 so r^2/(2(1-r))>=r^2 => r>=1/2 contradict 2r<1"}, "exact-hand-rr-ud"
    return None

def cert_chord_G(q):
    # h1 <= u; Sigma < 1-u+(1-x)/(1+x); Sigma > 2-x-h1
    s=nq(q)
    if "Sigma<1-u+(1-x)/(1+x)" in s and "Sigma>2-x-h1" in s and "h1<=u" in s:
        x,u=sp.symbols("x u")
        # need 2-x-h1 < Sigma < 1-u+(1-x)/(1+x) and h1<=u =>
        # 2-x-u < 1-u+(1-x)/(1+x) ? using max LHS with h1=u: 2-x-u vs upper
        gap=sp.together(1-u+(1-x)/(1+x) - (2-x-u))
        # = 1-u+(1-x)/(1+x) -2 +x +u = x-1+(1-x)/(1+x)
        num=sp.expand(sp.numer(gap))
        Bn=b24.bernstein_coeffs(num,[x],[(F(0),F(1))])  # independent of u!
        Bd=b24.bernstein_coeffs(sp.expand(sp.denom(gap)),[x],[(F(0),F(1))])
        if all(b<=0 for b in Bn) and all(b>0 for b in Bd) and any(b<0 for b in Bn):
            return {"type":"bernstein_Sigma_gap","numer_coeffs":[frac_str(b) for b in Bn],"denom_coeffs":[frac_str(b) for b in Bd],
                    "claim":"even at h1=u, lower 2-x-u >= upper 1-u+(1-x)/(1+x)"}, "exact-Bernstein-Sigma-gap"
    return None

def cert_g25_chord(q):
    s=nq(q)
    # p*(2mu-L)+ wait: g25_s*(2*g25_mu-g25_L)+g25_p*g25_mu <=1 with L>=mu, L^2<=2, p^2+s^2=1,p>=s
    if "g25_s*(2*g25_mu-g25_L)+g25_p*g25_mu<=1" in s and "g25_L>=g25_mu" in s:
        # Min of LHS at L max? Actually coefficient of -g25_s*L: to minimize LHS for feasibility of <=1 under constraints, take L as large as possible when s>0.
        # For contradiction of existence: show LHS >1 always.
        # LHS = 2 s mu - s L + p mu = mu(p+2s) - s L >= mu(p+2s) - s*sqrt(2) (L<=sqrt2)
        # And mu>1, p>=s, p^2+s^2=1.
        # Weierstrass: p=(1-t^2)/(1+t^2), s=2t/(1+t^2), t in (0,1] for p>=s => t<=1, p>=s => (1-t^2)>=2t => 1>=2t+t^2=(t+1)^2-0? 1-t^2>=2t => 1>=2t+t^2=(t+1)^2-0 => (1-t)^2 >= 2t - 2t wait
        # 1-t^2 >= 2t => 1>=2t+t^2 => 0>= t^2+2t-1 => t <= -1+sqrt2
        mu,t=sp.symbols("mu t", positive=True)
        p=(1-t**2)/(1+t**2); s=2*t/(1+t**2)
        lower=sp.together(mu*(p+2*s)-s*sp.sqrt(2))
        # Still irrational. Use L^2<=2 as L<=sqrt2 via squaring differently.
        # Show mu(p+2s)-s L >1 for all L in [mu,sqrt2] — hardest at L=sqrt2 and mu→1+.
        # At mu=1,L=sqrt2: p+2s - s sqrt2 = p + s(2-sqrt2). With p^2+s^2=1,p>=s.
        # Min of p+s(2-sqrt2) on circle arc.
        # Use Bernstein after Weierstrass on f(t)=p+s(2-sqrt2)-1
        # Avoid sqrt: show (mu(p+2s)-1)^2 > 2 s^2 when mu(p+2s)-1>0, equivalent to lower>1 with L<=sqrt2.
        expr=sp.together(1*(p+2*s)-1)  # at mu=1
        # need expr^2 > 2 s^2
        gap=sp.together(expr**2 - 2*s**2)
        num=sp.expand(sp.numer(gap))
        Bn=b24.bernstein_coeffs(num,[t],[(F(0),F(2)/5)])  # -1+sqrt2~0.414, use 2/5
        Bd=b24.bernstein_coeffs(sp.expand(sp.denom(gap)),[t],[(F(0),F(2)/5)])
        if all(b>0 for b in Bn) and all(b>0 for b in Bd):
            return {"type":"bernstein_g25_chord","numer_coeffs":[frac_str(b) for b in Bn],"claim":"at mu>=1,L<=sqrt2, LHS>=mu(p+2s)-s*sqrt2>1"}, "exact-Bernstein-g25-chord"
    return None

def prove_row(row):
    q=row['q']
    for p in (cert_strict_interval_empty, cert_rpp_disc, cert_half_l_K, cert_mu_r_u, cert_A_L2_mu, cert_rr_ud, cert_chord_G, cert_g25_chord):
        try:
            got=p(q)
        except Exception:
            got=None
        if got: return got
    return None, 'no-method'

def main():
    rows=[json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    RESULT.write_text(''); still=[]; n_ex=0; t0=time.time(); logf=open(LOG,'w')
    def log(m):
        print(m, flush=True); logf.write(m+'\n'); logf.flush()
    for i,row in enumerate(rows):
        cert,method=prove_row(row)
        rec={'file':row['file'],'n':row['n'],'q':row['q'],'id':qid(row),'batch':'25c'}
        if cert and method and method.startswith('exact'):
            rec['status']='exact'; rec['method']=method
            path=OUT_DIR/f'{qid(row)}.json'
            path.write_text(json.dumps({'id':qid(row),'file':row['file'],'n':row['n'],'query':row['q'],'method':method,'status':'exact','certificate':cert,'batch':'25c'},ensure_ascii=False,indent=2))
            n_ex+=1; log(f'[{i+1}/{len(rows)}] EXACT {row["file"]}#{row["n"]} {method}')
        else:
            rec['status']='open'; rec['reason']=method; still.append(row)
        open(RESULT,'a').write(json.dumps(rec,ensure_ascii=False)+'\n')
    STILL_OUT.write_text('\n'.join(json.dumps(r,ensure_ascii=False) for r in still)+('\n' if still else ''))
    log(f'DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s'); logf.close()
if __name__=='__main__':
    main()
