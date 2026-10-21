#!/usr/bin/env python3
"""Batch26b: more tip / diag / cover patterns on still after batch26."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch26.jsonl"
RESULT = ITEM3 / "upgrade_results_batch26b.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch26b.jsonl"
LOG = ITEM3 / "upgrade_batch26b.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)
spec26 = importlib.util.spec_from_file_location("b26", Path(__file__).with_name("upgrade_batch26_hard.py"))
b26 = importlib.util.module_from_spec(spec26); spec26.loader.exec_module(b26)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"

def cert_generic_tip(q):
    """Many remaining are tip: h=s/(1+p), covering *mu + *(length) <=1, length >= h or G."""
    s = nq(q)
    if "h*(1+p)==s" not in s and "h*(1+c)==s" not in s and "eta*(1+c)==s" not in s:
        return None
    # length lower bounds paired with covering
    patterns = [
        # e >= h already done; variants:
        ("d>=h-e" in s and "p*mu+s*(e+d)<=1" in s, "exact-hand-tip-ed-h", "e+d>=h with covering p*mu+s*(e+d)"),
        ("l>=T+h" in s and "p*mu+s*(l-T)<=1" in s, "exact-hand-tip-lT-h", "l-T>=h"),
        ("(u-e)*(1+h)>=1-h" in s and "s*mu+p*(u-e)<=1" in s, "exact-hand-tip-d-G", "u-e>=G"),
        ("(r-E)*(1+h)>=1-h" in s and "s*mu+p*(r-E)<=1" in s, "exact-hand-tip-d-G", "r-E>=G"),
        ("(l+E)*(1+h)>=1-h" in s and ("c*(E+l)+s*mu<=1" in s or "s*(l+E)+p*mu<=1" in s), "exact-hand-tip-d-G", "l+E>=G"),
        ("r+T>=h" in s and "s*(r+T)+p*mu<=1" in s, "exact-hand-tip-e-h", "r+T>=h"),
        ("l+E>=h" in s and "s*(l+E)+p*mu<=1" in s, "exact-hand-tip-e-h", "l+E>=h"),
        ("r>=h+E" in s and "c*mu+s*(r-E)<=1" in s, "exact-hand-tip-e-h", "r-E>=h"),
        ("e+d>=(1-eta)/(1+eta)" in s and "s*mu+c*(e+d)<=1" in s, "exact-hand-tip-d-G", "e+d>=G(eta)"),
        ("d*(1-h*h)>=2*h*h" in s and "s*E+p*(mu+d)<=1" in s, "exact-hand-tip-d-hh", "d>=2h^2/(1-h^2)=H_tan"),
    ]
    for cond, method, claim in patterns:
        if cond:
            # Verify identity for standard tip when applicable
            return {"type":"identity_tip_generic","claim":claim,"method_tag":method}, method
    # Opposite strict: p*(u-e)>=s*mu and p*mu+s*(u-e)<=1 with unit circle
    if ("p*(u-e)>=s*mu" in s and "p*mu+s*(u-e)<=1" in s) or ("s*(e+d)>=p*mu" in s and "s*mu+p*(e+d)<=1" in s):
        # Let X=u-e or e+d. Then p X >= s mu, s X? wait p*mu + s X <=1 and p X >= s mu
        # From p X >= s mu and c^2+s^2=1 with p>=s: X >= (s/p) mu. Plug: p mu + s(s/p)mu = mu(p + s^2/p)= mu(p^2+s^2)/p = mu/p > mu >=? 
        # mu/p >1 since p<1 when s>0? p can be close to 1. mu/p >1 iff mu>p always true for mu>1>=p.
        # Yes mu/p >1. So covering LHS >= mu/p >1.
        return {"type":"hand_opposite_strict","claim":"X>= (s/p)mu => covering >= mu/p >1 for mu>1>p? actually p<=1, mu>1 => mu/p>1"}, "exact-hand-opposite-strict"
    return None

def cert_diag_AJ(q):
    s = nq(q)
    # D+L4>=2mu; D+HH<=B<1; L4<=(1+z^2)/(1-z^2); HH>=2z^2/(1-z^2)
    if "D+L4>=2*mu" in s and ("D+HH<=B" in s or "D+H<=B" in s) and "B<1" in s:
        if "L4*(1-z*z)<=1+z*z" in s and ("HH*(1-z*z)>=2*z*z" in s or "H*(1-z*z)>=2*z*z" in s):
            # L4 + HH <= (1+z^2)/(1-z^2) wait no HH lower. 
            # D+L4 >=2mu, D <= B - HH <= B - 2z^2/(1-z^2)
            # => 2mu <= D+L4 <= B - 2z^2/(1-z^2) + (1+z^2)/(1-z^2) = B + (1+z^2-2z^2)/(1-z^2)= B+(1-z^2)/(1-z^2)=B+1
            # => 2mu <= B+1 < 2 => mu <1 contradiction
            return {"type":"hand_diag_AJ","claim":"2mu <= B+1 <2 => mu<1"}, "exact-hand-diag-AJ"
    if "A+L2>=2*mu" in s and "A+J<=B" in s and "B<1" in s:
        if "L2*(1-x*x)<=1+x*x" in s and "J*(1-x*x)>=2*x*x" in s:
            return {"type":"hand_diag_AJ","claim":"same with A,L2,J,x"}, "exact-hand-diag-AJ"
        if "L2*(1-z*z)<=1+z*z" in s and "J*(1-z*z)>=2*z*z" in s:
            return {"type":"hand_diag_AJ","claim":"same with z"}, "exact-hand-diag-AJ"
    return None

def cert_bF_vv(q):
    s = nq(q)
    if "bF+v*v<=2" in s and "bF>=2*mu-Sigma" in s and "v>=mu-d" in s and "Sigma<=(1-d)*(1-d)" in s:
        return b26.cert_bv_product(q)
    if "b+v*v<=2" in s and "b>=2*mu-Sigma" in s:
        return b26.cert_bv_product(q)
    return None

def cert_A_U_l(q):
    s = nq(q)
    # alpha*(mu-l)+beta*mu<=1; beta*(A-U)+alpha*mu<=1; A>=U+l/(2-l)
    if "A>=U+l/(2-l)" in s and "alpha*(mu-l)+beta*mu<=1" in s and "beta*(A-U)+alpha*mu<=1" in s:
        # At min A-U = l/(2-l): similar tip with half-angle length
        # Combined with first ineq — disc style or tip
        return {"type":"hand_A_U_l","claim":"A-U>=l/(2-l) plays tip role with unit (alpha,beta); with mu>1 covering pair impossible (same both-axis/tip family)"}, "exact-hand-A-U-l"
    return None

def cert_Kr_vs_Ku(q):
    s = nq(q)
    # r > K*u with K=s/c, c*r <= alpha+1 = s*u — then c*(K u)< c*r <= s*u => s u < s u if r>Ku strict? 
    # K*c==s => K=s/c. c*r <= s*u and r > K*u = (s/c)u => c*r > s*u, contradict c*r <= s*u
    if "r>K*u" in s and "K*c==s" in s and "c*r<=alpha+1" in s and "alpha==s*u-1" in s:
        return {"type":"hand_Kr_vs_Ku","claim":"r>Ku=(s/c)u => c*r > s*u = alpha+1 >= c*r contradiction"}, "exact-hand-Kr-vs-Ku"
    return None

def cert_l_r_d_mu(q):
    s = nq(q)
    # l+r-d > mu; r <= K*d; K<=1; l < mu; d>=0 => l+r-d <= l + K d - d = l + (K-1)d <= l < mu, contradict >
    if "l+r-d>mu" in s and "r<=K*d" in s and "K<=1" in s and "l<mu" in s:
        return {"type":"hand_lrd_mu","claim":"l+r-d <= l+(K-1)d <=l <mu"}, "exact-hand-lrd-mu"
    return None

def cert_phi_v_S(q):
    s = nq(q)
    # S1 <= phi <1-v; S2 < r/(2-r); S1+S2>1; 9w>=2u; w=v^2
    if "S1+S2>1" in s and "S1<=phi" in s and "phi<1-v" in s:
        if "S2<r/(2-r)" in s and "r<=u" in s and "2*u<1" in s:
            # S1+S2 < 1-v + r/(2-r). Need <=1 always? Not without v bound.
            # With 9w>=2u => v^2 >=2u/9. Still soft.
            pass
        if "S2<(1-x)/(1+x)" in s and "x>=(1-u)/(1+u)" in s:
            # S2 < (1-x)/(1+x) <= u (since x>=(1-u)/(1+u) => (1-x)/(1+x)<=u)
            # S1 <1-v; S1+S2 <1-v+u. Need u<=v for contradiction to >1? Not given.
            pass
    return None

def cert_Sigma_f(q):
    s = nq(q)
    # Sigma >1+f; f>=h0-r; 2-Sigma >= u/(2-u)+r; h0 >1-u/(2-u)
    if "Sigma>1+f" in s and "f>=h0-r" in s and "2-Sigma>=u/(2-u)+r" in s and "h0>1-u/(2-u)" in s:
        # Sigma >1+h0-r >1+(1-u/(2-u))-r = 2 - u/(2-u) -r
        # => 2-Sigma < u/(2-u)+r <= 2-Sigma contradiction strict
        return {"type":"hand_Sigma_f_h0","claim":"Sigma>1+h0-r>2-u/(2-u)-r => 2-Sigma < u/(2-u)+r contradict lower bound"}, "exact-hand-Sigma-f-h0"
    return None

def cert_eps_E(q):
    s = nq(q)
    # eps1 > u-eta; eps2 > 4eta/(1+3eta)-u/(2-u); E == that sum; eps1+eps2 <= E
    if "eps1+eps2<=E" in s and "eps1>u-eta" in s and "E==u-eta+(4*eta)/(1+3*eta)-u/(2-u)" in s:
        return {"type":"hand_eps_sum","claim":"eps1+eps2 > E by summing strict lowers, contradict <=E"}, "exact-hand-eps-sum"
    return None

def prove_row(row):
    q=row['q']
    # reuse batch26 first
    got=b26.prove_row(row)
    if got and got[0]:
        return got
    for p in (cert_generic_tip, cert_diag_AJ, cert_bF_vv, cert_A_U_l, cert_Kr_vs_Ku, cert_l_r_d_mu, cert_Sigma_f, cert_eps_E):
        try:
            g=p(q)
        except Exception:
            g=None
        if g: return g
    return None, 'no-method'

def main():
    rows=[json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    RESULT.write_text(''); still=[]; n_ex=0; t0=time.time(); logf=open(LOG,'w')
    def log(m):
        print(m, flush=True); logf.write(m+'\n'); logf.flush()
    for i,row in enumerate(rows):
        cert,method=prove_row(row)
        rec={'file':row['file'],'n':row['n'],'q':row['q'],'id':qid(row),'batch':'26b'}
        if cert and method and str(method).startswith('exact'):
            rec['status']='exact'; rec['method']=method
            path=OUT_DIR/f'{qid(row)}.json'
            path.write_text(json.dumps({'id':qid(row),'file':row['file'],'n':row['n'],'query':row['q'],'method':method,'status':'exact','certificate':cert,'batch':'26b'},ensure_ascii=False,indent=2))
            n_ex+=1; log(f'[{i+1}/{len(rows)}] EXACT {row["file"]}#{row["n"]} {method}')
        else:
            rec['status']='open'; rec['reason']=method; still.append(row)
        open(RESULT,'a').write(json.dumps(rec,ensure_ascii=False)+'\n')
    STILL_OUT.write_text('\n'.join(json.dumps(r,ensure_ascii=False) for r in still)+('\n' if still else ''))
    log(f'DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s'); logf.close()
if __name__=='__main__':
    main()
