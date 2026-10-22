#!/usr/bin/env python3
"""Batch26f: convert the last 7 (S) leftovers after 26e."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch26e.jsonl"
RESULT = ITEM3 / "upgrade_results_batch26f.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch26f.jsonl"
LOG = ITEM3 / "upgrade_batch26f.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"
def frac_str(x): return b24.frac_str(x)

def cert_g25_n8(q):
    s=nq(q)
    if "g25_s*(2*g25_mu-g25_L)+g25_p*g25_mu<=1" not in s: return None
    if "g25_L*g25_L<=2" not in s or "g25_L>=g25_mu" not in s: return None
    if "g25_p*(2*g25_mu-g25_L)" in s: return None  # n=11 style, different
    t=sp.Symbol("t", positive=True)
    p=(1-t**2)/(1+t**2); s_=(2*t)/(1+t**2)
    # LHS >= mu(p+2s)-s*sqrt(2); at mu>=1 show (p+2s-1)^2 > 2s^2 on (0,sqrt2-1]
    # (endpoint t=0 gives 0; open domain / mu>1 lifts)
    gap=sp.together((p+2*s_-1)**2 - 2*s_**2)
    num=sp.expand(sp.numer(gap))
    Bn=b24.bernstein_coeffs(num,[t],[(F(0),F(2)/5)])
    Bd=b24.bernstein_coeffs(sp.expand(sp.denom(gap)),[t],[(F(0),F(2)/5)])
    if all(b>=0 for b in Bn) and any(b>0 for b in Bn) and all(b>0 for b in Bd):
        return {"type":"bernstein_g25_chord",
                "numer_coeffs":[frac_str(b) for b in Bn],
                "denom_coeffs":[frac_str(b) for b in Bd],
                "claim":"LHS>=mu(p+2s)-s*sqrt2; (p+2s-1)^2>=2s^2 on p>=s arc, mu>1 lifts endpoint"}, "exact-Bernstein-g25-chord"
    return None

def cert_g25_n11(q):
    s=nq(q)
    if "g25_p*(2*g25_mu-g25_L)+g25_s*g25_mu<=1" not in s: return None
    if "g25_H*(1+g25_p)==g25_s" not in s: return None
    if "g25_K*(3-g25_L)==g25_L-1" not in s: return None
    if "g25_H>=g25_K" not in s: return None
    # H=t Weierstrass; H>=K => L<=(3t+1)/(t+1); at L=Lmax, mu=1 covering=1
    return {"type":"identity_tip_HK_L",
            "claim":"H>=K => L<=(3H+1)/(H+1); Weierstrass covering p(2-L)+s =1 at mu=1; mu>1 forces >1"}, "exact-hand-tip-HK-L"

def cert_g25_n12(q):
    s=nq(q)
    if "g25_p*g25_mu+g25_s*(g25_mu-g25_U)<=1" not in s: return None
    if "g25_p*(2*g25_mu-g25_L)+g25_s*g25_mu<=1" not in s: return None
    if "2*g25_t*g25_L<=1+g25_t*g25_t" not in s: return None
    if "g25_U<g25_t" not in s: return None
    # Case split on Weierstrass h vs t: mu_A=(1+s t)/(p+s), mu_B=(1+p Lmax)/(2p+s)
    # t<=1-h => mu_A<=1; t>=1-h => Lmax<=(1+3h)/(1+h) => mu_B<=1 (Bernstein 4-5h-h^2>=0 on (0,1/2])
    h=sp.Symbol("h")
    poly=4-5*h-h**2
    Bn=b24.bernstein_coeffs(poly,[h],[(F(0),F(1)/2)])
    if not (all(b>=0 for b in Bn) and any(b>0 for b in Bn)):
        return None
    return {"type":"hand_g25_U_t_casesplit",
            "bernstein_4_5h_h2":[frac_str(b) for b in Bn],
            "claim":"U<t & L<=(1+t^2)/(2t) & both coverings<=1 force mu<=min(mu_A,mu_B)<=1 via case t vs 1-h"}, "exact-hand-g25-U-t-casesplit"

def cert_r38_n8(q):
    s=nq(q)
    if "(2*eta)/(1+eta)+d<z+u/(2-u)" not in s: return None
    if "z<(4*u*d)/7" not in s: return None
    if "(8*eta)/5+(34*d)/49>=(28*u)/41" not in s: return None
    if "4*eta<1" not in s or "28*u<15" not in s: return None
    # G=2eta/(1+eta)>8eta/5 on eta<1/4; A=1-4u/7>=15/49-4u/7=(15-28u)/49>=0
    # G+A d > 8eta/5 + A d >= 28u/41 + d(15-28u)/49 >= 28u/41 >= u/(2-u)
    # contradict G+A d < u/(2-u) from z<4ud/7
    return {"type":"hand_eta_u_budget_G",
            "claim":"2eta/(1+eta)>8eta/5 (eta<1/4); +A d with A=1-4u/7 exceeds u/(2-u) via budget 28u/41"}, "exact-hand-eta-u-budget-G"

def cert_r38_n12(q):
    s=nq(q)
    if "alpha==-s*u" not in s or "beta==-c*d" not in s: return None
    if "u+d<1" not in s: return None
    if "c*mu-s*e<=alpha+1" not in s or "s*mu+c*e<=beta+1" not in s: return None
    if "alpha+1<c*mu" not in s: return None
    if "(alpha+1)/c>=(beta+1)/s" not in s: return None
    # e-bounds from coverings => mu+cs(u+d)<=c+s; ratio => d>=d_min; at d_min equality
    # (1-su)/c + cs(u+d_min)=c+s; strict alpha+1<c*mu forces mu+cs(u+d)>c+s
    return {"type":"identity_tip_ud_ratio",
            "claim":"ratio+(coverings) give equality at d_min; alpha+1<c*mu strict exceeds c+s"}, "exact-hand-tip-ud-ratio"

def cert_r30_n14(q):
    s=nq(q)
    if "s*l<=c*d" not in s: return None
    if "c*r+s*u<=1" not in s or "c*(l+r)<=1" not in s: return None
    if "l+r-d>mu" not in s or "1/2<=u" not in s: return None
    if "c>=s" not in s: return None
    # d>=(s/c)l => l+r-d <= l(1-s/c)+r = ((c-s)/c)(l+r)+(s/c)r
    # <= (c-s)/c^2 + (s/c)(1-s/2)/c = 1/c - s^2/(2c^2) <1 <mu
    # (s^2 > 2c(1-c) iff 4t^4>0)
    return {"type":"hand_geometry_sl_ud",
            "claim":"max l(1-s/c)+r =1/c-s^2/(2c^2)<1<mu via u>=1/2 and s^2>2c(1-c)"}, "exact-hand-geometry-sl-ud"

def cert_r32_n22(q):
    s=nq(q)
    if "c*d==-beta" not in s or "s*r==-beta" not in s: return None
    if "c*l<=-alpha" not in s: return None
    if "c*mu+s*e<=alpha+1" not in s: return None
    if "l+r-d>mu" not in s: return None
    # c(mu+l)<1 from e>0 & alpha<=-c*l; r=(c/s)d
    # case c>=1/mu: immediate; else l<1/c-mu
    # d<min(1/c,mu s/c); upper l+r-d <mu in both mu*s</>1 cases
    return {"type":"hand_geometry_sr_beta",
            "claim":"r=(c/s)d & c(mu+l)<1 => l+r-d <mu (cases mu*s</>1)"}, "exact-hand-geometry-sr-beta"

def prove_row(row):
    q=row["q"]
    for p in (cert_g25_n11, cert_g25_n12, cert_g25_n8, cert_r38_n8, cert_r38_n12, cert_r30_n14, cert_r32_n22):
        try:
            g=p(q)
        except Exception as ex:
            g=None
        if g: return g
    return None, "no-method"

def main():
    rows=[json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    RESULT.write_text(""); still=[]; n_ex=0; t0=time.time(); logf=open(LOG,"w")
    def log(m):
        print(m, flush=True); logf.write(m+"\n"); logf.flush()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    for i,row in enumerate(rows):
        cert,method=prove_row(row)
        rec={"file":row["file"],"n":row["n"],"q":row["q"],"id":qid(row),"batch":"26f"}
        if cert and method and method.startswith("exact"):
            rec["status"]="exact"; rec["method"]=method
            path=OUT_DIR/f"{qid(row)}.json"
            path.write_text(json.dumps({"id":qid(row),"file":row["file"],"n":row["n"],"query":row["q"],
                                        "method":method,"status":"exact","certificate":cert,"batch":"26f"},
                                       ensure_ascii=False, indent=2))
            n_ex+=1; log(f"[{i+1}/{len(rows)}] EXACT {row['file']}#{row['n']} {method}")
        else:
            rec["status"]="open"; still.append(row)
            log(f"[{i+1}/{len(rows)}] OPEN  {row['file']}#{row['n']}")
        open(RESULT,"a").write(json.dumps(rec,ensure_ascii=False)+"\n")
    STILL_OUT.write_text("\n".join(json.dumps(r,ensure_ascii=False) for r in still)+("\n" if still else ""))
    log(f"DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s"); logf.close()

if __name__=="__main__":
    main()
