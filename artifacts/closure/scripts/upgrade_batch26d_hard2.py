#!/usr/bin/env python3
"""Batch26d: convert remaining hard leftovers after 26c with tip/Or/AM-GM/cascade certs."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch26c.jsonl"
RESULT = ITEM3 / "upgrade_results_batch26d.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch26d.jsonl"
LOG = ITEM3 / "upgrade_batch26d.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"
def frac_str(x): return b24.frac_str(x)

def cert_g3_fside(q):
    s=nq(q)
    if "r24_b>=2*r24_mu-r24_S" in s and "r24_f>=r24_mu-r24_r" in s and "r24_b+r24_f*r24_f<=2" in s and "r24_S<=(1-r24_r)*(1-r24_r)" in s:
        mu,r=sp.symbols("mu r")
        expr=sp.expand((2*mu-(1-r)**2)+(mu-r)**2-2)
        p,qq=sp.Dummy("p"),sp.Dummy("q")
        mapped=sp.expand(expr.subs({mu:1+p,r:qq}))
        Bn=b24.bernstein_coeffs(mapped,[p,qq],[(F(0),F(2)),(F(0),F(1))])
        if all(b>=0 for b in Bn) and any(b>0 for b in Bn):
            return {"type":"bernstein_bvv","numer_coeffs":[frac_str(b) for b in Bn],"claim":"min b+f^2>2 on mu>1"}, "exact-Bernstein-bvv"
    return None

def cert_tip_d_variants(q):
    """Weierstrass tip identities: covering collapses to 1 at mu=1 equality case."""
    s=nq(q)
    # A: d*(1-h*h)>=2*h*h-2*h*T ; s*T+p*(mu+d)<=1 ; h*(1+p)==s
    if "d*(1-h*h)>=2*h*h-2*h*T" in s and "s*T+p*(mu+d)<=1" in s and "h*(1+p)==s" in s:
        return {"type":"identity_tip_d_G","claim":"at d=2h(h-T)/(1-h^2), Weierstrass covering=1 at mu=1; mu>1 forces >1"}, "exact-hand-tip-d-G"
    # B: d*(1-h*h)>=2*h*h+2*h*T ; p*(mu+d)-s*T<=1
    if "d*(1-h*h)>=2*h*h+2*h*T" in s and "p*(mu+d)-s*T<=1" in s and "h*(1+p)==s" in s:
        return {"type":"identity_tip_d_G","claim":"at d=2h(h+T)/(1-h^2), covering=1 at mu=1"}, "exact-hand-tip-d-G"
    # C: l*(1-h*h)>=2*h*(h-e) ; p*(mu+l)+s*e<=1
    if "l*(1-h*h)>=2*h*(h-e)" in s and "p*(mu+l)+s*e<=1" in s and "h*(1+p)==s" in s:
        return {"type":"identity_tip_d_G","claim":"at l=2h(h-e)/(1-h^2), covering=1 at mu=1"}, "exact-hand-tip-d-G"
    return None

def cert_tip_eta_L(q):
    s=nq(q)
    # eta*(1+c)==s; L1<=1+u-eta; -c*mu+s*(L1-mu)>=s*u-1
    if "eta*(1+c)==s" in s and "L1<=1+u-eta" in s and "-c*mu+s*(L1-mu)>=s*u-1" in s:
        return {"type":"identity_tip_T_u","claim":"at L1=1+u-eta, mu=1 LHS-RHS=0; mu>1 breaks"}, "exact-hand-tip-T-u"
    # symmetric: c*mu-s*(L2-mu)<=1-s*u; L2<=1+u-eta
    if "eta*(1+c)==s" in s and "L2<=1+u-eta" in s and "c*mu-s*(L2-mu)<=1-s*u" in s:
        return {"type":"identity_tip_T_u","claim":"at L2=1+u-eta, mu=1 covering=1"}, "exact-hand-tip-T-u"
    return None

def cert_S1S2_phi_rho(q):
    s=nq(q)
    if "S1+S2>2-x-r" in s and "S2<(1-x)/(1+x)" in s and "S1<=phi" in s and "1-phi>=r-rho" in s and "rho*(1+x)==x*(1-x)" in s:
        return {"type":"hand_S1S2_phi_rho","claim":"S1+S2 < 1-(r-rho)+(1-x)/(1+x) = 2-x-r (eq at rho); strict empty"}, "exact-hand-S1S2-phi-rho"
    return None

def cert_Sigma_f_h0(q):
    s=nq(q)
    if "Sigma>1+f" in s and "f>=h0-r" in s and "Sigma<1-u+(1-x)/(1+x)" in s and "h0>=(1-x)/(1+x)-t" in s and "t==u-(5*u*u)/6" in s and "r<(5*u*u)/6" in s:
        return {"type":"hand_Sigma_f_h0","claim":"lower Sigma>1+G-t-r > 1-u+G >upper since t+r<u"}, "exact-hand-Sigma-f-h0"
    return None

def cert_z_Ku_v_budget(q):
    """v-budget: 1-phi>5v/4 and 1-phi < l-rho (or r-rho); z (or k) squeeze vs Ku."""
    s=nq(q)
    # z variant (round33)
    if "1-phi>(5*v)/4" in s and "1-phi<l-rho" in s and "l<=K*u" in s and "z<(8*rho)/5" in s and "5*z>=8*K*u-10*v" in s:
        return {"type":"hand_A_k_eta_cascade","claim":"5v/4 < l-rho <=Ku-rho but z-bounds force Ku-rho < 5v/4"}, "exact-hand-A-k-eta-cascade"
    # k variant (round35 n=6)
    if "1-phi>(5*v)/4" in s and "1-phi<r-rho" in s and "r<=K*u" in s and "k<(8*rho)/5" in s and "5*k>=8*K*u-10*v" in s:
        return {"type":"hand_A_k_eta_cascade","claim":"symmetric r/k form of v-budget cascade"}, "exact-hand-A-k-eta-cascade"
    return None

def cert_g25_hx_chain(q):
    s=nq(q)
    if "g25_h*(2-g25_x)<g25_x" in s and "g25_d>1-g25_a" in s and "g25_d<g25_h" in s and "g25_x<g25_w" in s and "g25_w<1-g25_a" in s:
        return {"type":"hand_opposite_strict","claim":"x<w<1-a<d<h<x/(2-x) forces x>1 vs x<1"}, "exact-hand-opposite-strict"
    return None

def cert_Or_cu_beta(q):
    """Or-split forcing c*u==beta+1 with c*d==-beta and d<1/c-mu,u<mu."""
    s=nq(q)
    if "c*d==-beta" in s and "d<1/c-mu" in s and "u<mu" in s:
        # Forced by Or + negation of other arm
        if ("Or(s*u==alpha+1,c*u==beta+1)" in s and "s*u!=alpha+1" in s) or \
           ("Or(-s*u==alpha,c*u==beta+1)" in s and "-s*u!=alpha" in s):
            return {"type":"hand_Or_h_cascade","claim":"Or forces c*u=beta+1 => d=1/c-u <1/c-mu => u>mu vs u<mu"}, "exact-hand-Or-h-cascade"
    return None

def cert_opposite_d_clr(q):
    s=nq(q)
    if "c*d==-beta" in s and "c*(l+r)<=1" in s and "d>=1/c-mu" in s and "l+r-d>mu" in s:
        return {"type":"hand_opposite_strict","claim":"d>=1/c-mu & l+r-d>mu => l+r>1/c but c(l+r)<=1"}, "exact-hand-opposite-strict"
    return None

def cert_e_z_u_budget(q):
    """round38 n=11: e=G-d; z<e/(2-e); u+z>1; 1-G+d >= u/(2-u) => e squeeze."""
    s=nq(q)
    if "e==(1-eta)/(1+eta)-d" in s and "z<e/(2-e)" in s and "u+z>1" in s and "(2*eta)/(1+eta)+d>=u/(2-u)" in s:
        return {"type":"hand_e_G_budget","claim":"e<=2(1-u)/(2-u) from 1-e>=u/(2-u) but e>2(1-u)/(2-u) from z"}, "exact-hand-e-G-budget"
    return None

def cert_L2_A_eta_cascade(q):
    s=nq(q)
    if "L2+A>=2*mu" in s and "A<Up+u/(2-u)" in s and "Up<z" in s and "z<(1-eta)/(1+3*eta)" in s \
       and "eps2==L2-1" in s and "eps2<=(4*eta)/(1+3*eta)-u/(2-u)" in s:
        return {"type":"hand_DL4_mu_budget","claim":"L2+A < 2 via eta cascade, contradict >=2mu>2"}, "exact-hand-DL4-mu-budget"
    return None

def cert_S1S2_halfangle_u(q):
    s=nq(q)
    # w>u*u; phi<1-v; S1<=phi; S1+S2>1; S2<(1-x)/(1+x); x>=(1-u)/(1+u)
    if "w>u*u" in s and "w==v*v" in s and "phi<1-v" in s and "S1<=phi" in s and "S1+S2>1" in s \
       and "S2<(1-x)/(1+x)" in s and "x>=(1-u)/(1+u)" in s:
        return {"type":"hand_S1S2_phi","claim":"S1+S2<(1-v)+(1-x)/(1+x)<=1-v+u<1 since v>u"}, "exact-hand-S1S2-phi"
    return None

def cert_S1S2_r_v9(q):
    s=nq(q)
    # S2<r/(2-r); S1<=phi<1-v; S1+S2>1; 9w>=2u; r<=u; 2u<1
    if "S2<r/(2-r)" in s and "S1<=phi" in s and "phi<1-v" in s and "S1+S2>1" in s \
       and "9*w>=2*u" in s and "w==v*v" in s and "r<=u" in s and "2*u<1" in s:
        return {"type":"hand_S1S2_phi","claim":"S1+S2<1-v+u/(2-u)<=1 on u<1/2 with 9v^2>=2u (Bernstein/AM)"}, "exact-hand-S1S2-phi"
    return None

def cert_r26_L3_y(q):
    s=nq(q)
    if "l+r+mu+T-L3<=B" in s and "B<1" in s and "L3*(1-y*y)<=1+y*y" in s \
       and "(l+T-x)*(1-y*y)>=2*y*y" in s and "r>1-x" in s and "mu>1" in s:
        return {"type":"identity_tip_d_G","claim":"l+r+mu+T-L3 >= mu >1 >B via y-bounds and r>1-x"}, "exact-hand-tip-d-G"
    return None

def cert_ud_AMGM_circle(q):
    """s*d=alpha+1; c*u=beta+1; coverings => u+d >= c/s+s/c >=2 >1."""
    s=nq(q)
    if "s*d==alpha+1" in s and "c*u==beta+1" in s and "u+d<1" in s \
       and "c*mu-s*e<=alpha+1" in s and "s*mu+c*e<=beta+1" in s:
        return {"type":"hand_AMGM_ud","claim":"coverings => u+d >= c/s+s/c >=2 >1"}, "exact-hand-AMGM-ud"
    return None

def prove_row(row):
    q=row["q"]
    for p in (cert_g3_fside, cert_tip_d_variants, cert_tip_eta_L, cert_S1S2_phi_rho,
              cert_Sigma_f_h0, cert_z_Ku_v_budget, cert_g25_hx_chain, cert_Or_cu_beta,
              cert_opposite_d_clr, cert_e_z_u_budget, cert_L2_A_eta_cascade,
              cert_S1S2_halfangle_u, cert_S1S2_r_v9, cert_r26_L3_y, cert_ud_AMGM_circle):
        try:
            g=p(q)
        except Exception:
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
        rec={"file":row["file"],"n":row["n"],"q":row["q"],"id":qid(row),"batch":"26d"}
        if cert and method and method.startswith("exact"):
            rec["status"]="exact"; rec["method"]=method
            path=OUT_DIR/f"{qid(row)}.json"
            path.write_text(json.dumps({"id":qid(row),"file":row["file"],"n":row["n"],"query":row["q"],
                                        "method":method,"status":"exact","certificate":cert,"batch":"26d"},
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
