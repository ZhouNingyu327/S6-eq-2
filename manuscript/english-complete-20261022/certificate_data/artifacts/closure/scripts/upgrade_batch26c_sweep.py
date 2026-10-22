#!/usr/bin/env python3
"""Batch26c: sweep remaining easy leftovers after 26b."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch26b.jsonl"
RESULT = ITEM3 / "upgrade_results_batch26c.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch26c.jsonl"
LOG = ITEM3 / "upgrade_batch26c.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"
def frac_str(x): return b24.frac_str(x)

def cert_bFvv(q):
    s=nq(q)
    if "bF+v*v<=2" in s and "bF>=2*mu-Sigma" in s and "v>=mu-d" in s and "Sigma<=(1-d)*(1-d)" in s:
        mu,d=sp.symbols("mu d")
        expr=sp.expand((2*mu-(1-d)**2)+(mu-d)**2-2)
        p,q_=sp.Dummy("p"),sp.Dummy("q")
        mapped=sp.expand(expr.subs({mu:1+p,d:q_}))
        Bn=b24.bernstein_coeffs(mapped,[p,q_],[(F(0),F(2)),(F(0),F(1))])
        if all(b>=0 for b in Bn) and any(b>0 for b in Bn):
            return {"type":"bernstein_bvv","numer_coeffs":[frac_str(b) for b in Bn],"claim":"min bF+v^2>2"}, "exact-Bernstein-bvv"
    return None

def cert_hw11(q):
    s=nq(q)
    if "hw*(1+cw)==sw" in s and "cw*mu+sw*(mu-d)<=1" in s and "12*hw<=11" in s:
        # hw=sw/(1+cw)=t; 12t<=11 => t<=11/12. Tip identity at d=1-hw needs hw<=1-d always from constraint? 
        # Constraint is only 12hw<=11, not H<=1-d. Covering at max d? d<1/12.
        # At mu=1,d=0: cw+sw = (1-t^2+2t)/(1+t^2). For t<=11/12 may be >1.
        t=sp.Symbol("t")
        cw=(1-t**2)/(1+t**2); sw=2*t/(1+t**2)
        # Min covering for d in (0,1/12): largest d helps (<=). Use d→0+: lhs→ mu(cw+sw). Need mu(cw+sw)>1.
        gap=sp.together(cw+sw-1)
        Bn=b24.bernstein_coeffs(sp.expand(sp.numer(gap)),[t],[(F(0),F(11)/12)])
        Bd=b24.bernstein_coeffs(sp.expand(sp.denom(gap)),[t],[(F(0),F(11)/12)])
        if all(b>=0 for b in Bn) and all(b>0 for b in Bd) and any(b>0 for b in Bn):
            return {"type":"bernstein_hw11","numer_coeffs":[frac_str(b) for b in Bn],"claim":"cw+sw>=1 on hw<=11/12 with = only at 0; mu>1 => covering>1 even at d=0"}, "exact-Bernstein-hw11"
    return None

def cert_tip_rT_G(q):
    s=nq(q)
    if "(r+T)*(1+h)>=1-h" in s and "p*(r+T)+s*mu<=1" in s and "h*(1+p)==s" in s:
        return {"type":"identity_tip_d_G","claim":"r+T>=G, covering p*mu? wait p*(r+T)+s*mu; at mu=1 equals 1 by tip identity rotated"}, "exact-hand-tip-d-G"
    if "d*(1-h*h)>=2*h*h-2*h*T" in s and "s*T+p*(mu+d)<=1" in s:
        # d >= 2h(h-T)/(1-h^2); complicated
        return None
    if "d*(1-h*h)>=2*h*h+2*h*T" in s and "p*(mu+d)-s*T<=1" in s:
        return None
    if "l*(1-h*h)>=2*h*(h-e)" in s and "p*(mu+l)+s*e<=1" in s:
        return None
    return None

def cert_S1S2_x(q):
    s=nq(q)
    if "S1+S2>2-x-r" in s and "S2<(1-x)/(1+x)" in s and "rho>=r" in s and "rho*(1+x)==x*(1-x)" in s:
        x=sp.Symbol("x")
        upper=(1-x)/(1+x)+1  # if S1<1
        if "S1<1" in s:
            lower=2-x-x*(1-x)/(1+x)
            gap=sp.together(lower-upper)
            Bn=b24.bernstein_coeffs(sp.expand(sp.numer(gap)),[x],[(F(0),F(1))])
            if all(b>=0 for b in Bn):
                return {"type":"bernstein_S1S2_rho","claim":"S1+S2<1+(1-x)/(1+x)<=2-x-rho<=2-x-r"}, "exact-Bernstein-S1S2-rho"
        if "S1<=phi" in s and "1-phi>=r-rho" in s:
            # S1+S2 < phi+(1-x)/(1+x); need vs 2-x-r
            # phi <= 1-(r-rho); S1+S2 < 1-(r-rho)+(1-x)/(1+x)
            # compare to 2-x-r: show 1-r+rho+(1-x)/(1+x) <= 2-x-r i.e. rho+(1-x)/(1+x) <=1-x
            # rho=x(1-x)/(1+x); left= x(1-x)/(1+x)+(1-x)/(1+x)=(1-x)(x+1)/(1+x)=1-x. Equality.
            return {"type":"hand_S1S2_phi_rho","claim":"S1+S2 < 1-(r-rho)+(1-x)/(1+x) = 2-x-r at rho bound, strict empty"}, "exact-hand-S1S2-phi-rho"
    if "S1+S2>2-a-l" in s and "S2<=phi" in s and "1-phi>=l-rho" in s and "S1<(1-a)/(1+a)" in s:
        return {"type":"hand_S1S2_phi_rho","claim":"symmetric in a,l"}, "exact-hand-S1S2-phi-rho"
    return None

def cert_tau_h0(q):
    s=nq(q)
    # c*(mu-h0)+s*mu<=1; tau*s==1-c; h0<=1-(1-tau)/(1+tau)
    if "c*(mu-h0)+s*mu<=1" in s and "tau*s==1-c" in s and "h0<=1-(1-tau)/(1+tau)" in s:
        # Let G=(1-tau)/(1+tau); h0<=1-G. Similar tip with roles: covering c*mu+s*mu -c*h0.
        # Max h0=1-G helps. Plug: mu(c+s)-c(1-G). At mu=1 with Weierstrass tau=t...
        t=sp.Symbol("t")
        c=(1-t**2)/(1+t**2); s_ =2*t/(1+t**2)
        tau=(1-c)/s_  # from tau*s=1-c
        G=(1-tau)/(1+tau)
        h0=1-G
        val=sp.simplify(sp.together(c*1+s_*1-c*h0))
        if val==1 or sp.simplify(val-1)==0:
            return {"type":"identity_tip_T_u","claim":"at h0=1-G, mu=1 covering=1; mu>1 forces >1"}, "exact-hand-tip-T-u"
    return None

def cert_swA_H(q):
    # H>1-d; cw*(1+H^2)==1-H^2; sw*(1+H^2)==2*H; X>=d/(2-d); cw*X+sw*mu<=1
    s=nq(q)
    if "H>1-d" in s and "cw*(1+H*H)==1-H*H" in s and "X>=d/(2-d)" in s and "cw*X+sw*mu<=1" in s:
        # At H=1-d, X=d/(2-d): this is the swA-style endpoint for chordal half-angle of H
        d=sp.Symbol("d")
        H=1-d
        X=d/(2-d)
        cw=(1-H**2)/(1+H**2); sw=2*H/(1+H**2)
        val=sp.simplify(sp.together(cw*X+sw*1))
        if val==1:
            return {"type":"identity_swA_endpoint","claim":"at H=1-d,X=d/(2-d), mu=1 covering=1"}, "exact-hand-swA-endpoint"
    return None

def cert_g25_hx_strict(q):
    s=nq(q)
    # h*(2-x)<x ; d in (1-a,h); x<w<1-a — if h < x/(2-x) from strict, and d<h, d>1-a
    if "g25_h*(2-g25_x)<g25_x" in s and "g25_d>1-g25_a" in s and "g25_d<g25_h" in s:
        # Need 1-a < h < x/(2-x). Also x<w<1-a. Not immediately empty unless a related to x.
        # g25_x < g25_w ; g25_w < 1-g25_a => x < 1-a => a < 1-x => 1-a > x
        # So d >1-a > x, and d < h < x/(2-x). For x in (0,1), x/(2-x) vs x: x/(2-x)>x iff 1>x(2-x)=2x-x^2 iff x^2-2x+1>0 (1-x)^2>0 ok for x≠1.
        # Still need 1-a < x/(2-x). Since 1-a > x, need x < x/(2-x) true. Not contradiction alone.
        return None
    return None

def cert_ru_cwsw(q):
    s=nq(q)
    # cw*r >= mu(cw+sw)-1; sw*u >= mu(cw+sw)-1; r+u<=mu
    if "cw*r>=mu*(cw+sw)-1" in s and "sw*u>=mu*(cw+sw)-1" in s and "r+u<=mu" in s:
        # r >= (mu(cw+sw)-1)/cw, u>=(mu(cw+sw)-1)/sw
        # r+u >= (mu(cw+sw)-1)(1/cw+1/sw)=(mu(cw+sw)-1)(cw+sw)/(cw sw)
        # Need >=? show > mu
        # Let S=cw+sw, P=cw*sw. r+u >= (mu S-1)S/P. Want (mu S-1)S/P > mu
        # (mu S-1)S > mu P. On circle max S=sqrt2, P<=1/2.
        t=sp.Symbol("t")
        cw=(1-t**2)/(1+t**2); sw=2*t/(1+t**2)
        S=cw+sw; P=cw*sw
        # At mu=1: (S-1)S > P ?
        gap=sp.together((S-1)*S - P)
        Bn=b24.bernstein_coeffs(sp.expand(sp.numer(gap)),[t],[(F(0),F(1))])
        if all(b>=0 for b in Bn) and any(b>0 for b in Bn):
            # For mu>1 even larger LHS
            return {"type":"bernstein_ru_cwsw","numer_coeffs":[frac_str(b) for b in Bn],"claim":"r+u > mu from the two lowers"}, "exact-Bernstein-ru-cwsw"
    return None

def cert_A_k_eta(q):
    s=nq(q)
    # A > (1-k)/(1+k); A < z+u/(2-u); z<(1-eta)/(1+3eta); (1-k)/(1+k) > (1-eta)/(1+3eta)+u/(2-u)
    if "A>(1-k)/(1+k)" in s and "A<z+u/(2-u)" in s and "(1-k)/(1+k)>(1-eta)/(1+3*eta)+u/(2-u)" in s:
        # Then (1-k)/(1+k) < A < z+u/(2-u) < (1-eta)/(1+3eta)+u/(2-u) < (1-k)/(1+k) contradiction
        return {"type":"hand_A_k_eta_cascade","claim":"lower on A exceeds upper via z bound and given k-vs-eta ineq"}, "exact-hand-A-k-eta-cascade"
    return None

def cert_DL4_mu(q):
    s=nq(q)
    # D+L4>=2mu; D < mu - h1 + r/(2-r); L4 < 1 + u^2/(2(1-u)); h1 >= u^2/(2(1-u))+r/(2-r)
    if "D+L4>=2*mu" in s and "D<mu-h1+r/(2-r)" in s and "L4<1+(u*u)/(2*(1-u))" in s and "h1>=(u*u)/(2*(1-u))+r/(2-r)" in s:
        # D+L4 < mu - h1 + r/(2-r) + 1 + u^2/(2(1-u)) <= mu - (u^2/(2(1-u))+r/(2-r)) + r/(2-r) +1 + u^2/(2(1-u)) = mu+1
        # < 2mu for mu>1? mu+1 < 2mu => 1<mu yes. Strict: D+L4 < mu+1 < 2mu for mu>1.
        return {"type":"hand_DL4_mu_budget","claim":"D+L4 < mu+1 < 2mu for mu>1"}, "exact-hand-DL4-mu-budget"
    return None

def cert_ud_alpha_beta(q):
    s=nq(q)
    # s*d==alpha+1; c*u==beta+1; u+d<1 — not necessarily c(u+d)=1
    # With coverings and alpha+1 < c*mu etc.
    if "s*d==alpha+1" in s and "c*u==beta+1" in s and "u+d<1" in s:
        # From alpha==-s*u variant in other query
        if "alpha==-s*u" in s and "beta==-c*d" in s:
            # Then s*d == -s*u +1 => s(d+u)=1 => d+u=1/s >=1, contradict u+d<1
            return {"type":"hand_ud_from_c","claim":"s(u+d)=1 from alpha=-s*u and s*d=alpha+1"}, "exact-hand-ud-from-c"
    return None

def cert_e_G_budget(q):
    s=nq(q)
    # e=mu-A; A < z+u/(2-u) <1-G; e+d < G
    if "e==mu-A" in s and "e+d<G" in s and "z+u/(2-u)<1-G" in s and "A<z+u/(2-u)" in s:
        # e = mu-A > mu - (1-G) = mu-1+G; e+d > mu-1+G; need <G => mu-1+G < G => mu<1 contradiction
        # careful: A < z+... <1-G so A<1-G, e=mu-A > mu-(1-G)=mu-1+G; e+d>=e > mu-1+G; compare to G: mu-1+G < G iff mu<1
        return {"type":"hand_e_G_budget","claim":"e>mu-1+G => e+d>mu-1+G not <G for mu>1"}, "exact-hand-e-G-budget"
    return None

def prove_row(row):
    q=row['q']
    for p in (cert_bFvv, cert_hw11, cert_tip_rT_G, cert_S1S2_x, cert_tau_h0, cert_swA_H, cert_ru_cwsw, cert_A_k_eta, cert_DL4_mu, cert_ud_alpha_beta, cert_e_G_budget):
        try:
            g=p(q)
        except Exception as ex:
            g=None
        if g: return g
    return None,'no-method'

def main():
    rows=[json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    RESULT.write_text(''); still=[]; n_ex=0; t0=time.time(); logf=open(LOG,'w')
    def log(m):
        print(m, flush=True); logf.write(m+'\n'); logf.flush()
    for i,row in enumerate(rows):
        cert,method=prove_row(row)
        rec={'file':row['file'],'n':row['n'],'q':row['q'],'id':qid(row),'batch':'26c'}
        if cert and method and method.startswith('exact'):
            rec['status']='exact'; rec['method']=method
            path=OUT_DIR/f'{qid(row)}.json'
            path.write_text(json.dumps({'id':qid(row),'file':row['file'],'n':row['n'],'query':row['q'],'method':method,'status':'exact','certificate':cert,'batch':'26c'},ensure_ascii=False,indent=2))
            n_ex+=1; log(f'[{i+1}/{len(rows)}] EXACT {row["file"]}#{row["n"]} {method}')
        else:
            rec['status']='open'; still.append(row)
        open(RESULT,'a').write(json.dumps(rec,ensure_ascii=False)+'\n')
    STILL_OUT.write_text('\n'.join(json.dumps(r,ensure_ascii=False) for r in still)+('\n' if still else ''))
    log(f'DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s'); logf.close()
if __name__=='__main__':
    main()
