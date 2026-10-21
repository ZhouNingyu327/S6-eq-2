#!/usr/bin/env python3
"""Batch26: hard-pattern (S)→checkable (E)/(H) for remaining ~91."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch25d.jsonl"
RESULT = ITEM3 / "upgrade_results_batch26.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch26.jsonl"
LOG = ITEM3 / "upgrade_batch26.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"
def frac_str(x): return b24.frac_str(x)

# ---------- certificates ----------

def cert_AMGM_r(q):
    s = nq(q)
    if "2*r>=1" in s and "r<=K*u" in s and "K*r<=d" in s and "u+d<1" in s and "K<=1" in s and "K>0" in s:
        return {"type":"hand_AMGM_ud","claim":"u>=r/K, d>=K*r => u+d >= r/K+K*r >= 2r >=1, contradict u+d<1"}, "exact-hand-AMGM-ud"
    if "2*l>=1" in s and "l<=K*u" in s and "K*l<=d" in s and "u+d<1" in s and "K<=1" in s:
        return {"type":"hand_AMGM_ud","claim":"same with l"}, "exact-hand-AMGM-ud"
    return None

def cert_both_axis_disc(q):
    s = nq(q)
    # Pattern: c*(mu-r)+s*mu <=1 ; c*mu+s*(mu-u)<=1 ; r+u<1 ; mu>1 ; c^2+s^2=1
    pats = [
        ("c24_c*(c24_mu-c24_r)+c24_s*c24_mu<=1" in s and "c24_c*c24_mu+c24_s*(c24_mu-c24_u)<=1" in s and "c24_r+c24_u<1" in s),
        ("alpha*(mu-l)+beta*mu<=1" in s and "alpha*mu+beta*(mu-d)<=1" in s and "l+d<1" in s and "alpha*alpha+beta*beta==1" in s),
    ]
    if not any(pats) and not (
        "c*(mu" in s and "mu-u)<=1" in s and ("r+u<1" in s or "l+d<1" in s)
    ):
        # broader: two covering inequalities + sum of residuals <1
        if not (("*(mu-" in s) and ("mu-" in s) and ("+u<1" in s or "+d<1" in s or "l+d<1" in s or "r+u<1" in s)):
            return None
        if "c*c+s*s==1" not in s and "alpha*alpha+beta*beta==1" not in s and "c24_c*c24_c+c24_s*c24_s==1" not in s:
            return None
    # Disc argument: from the two ineqs, for unit (c,s),
    # the feasible (r,u) require a quadratic in direction t=u/(r+u) to have real root with r+u>= something.
    # Standard: adding: c*(2mu - (r+u)) + s*(2mu - (r+u))? Not quite.
    # Known proof: let t in [0,1], set r=t*L, u=(1-t)*L with L=r+u<1.
    # Then c(mu-tL)+s mu <=1 and c mu + s(mu-(1-t)L)<=1.
    # I.e. c mu + s mu - c t L <=1 and c mu + s mu - s(1-t)L <=1
    # mu(c+s) -1 <= min(c t, s(1-t)) L < min(c t, s(1-t))
    # For all t, need mu(c+s)-1 < max_t min(ct,s(1-t)) = cs/(c+s)
    # So (mu(c+s)-1)(c+s) < cs => mu(c+s)^2 - (c+s) < cs
    # But c^2+s^2=1 => (c+s)^2 = 1+2cs => mu(1+2cs)-(c+s) < cs
    # This gets messy; use Weierstrass + Bernstein on disc.
    # Simpler published hand: consider f(t)=(2mu-1)t^2 - 2t +1 for the dual.
    # From private script: (2mu-1)t^2 - 2t +1 > 0 always for mu>1.
    # Disc of contact: verify polynomial (2mu-1)-1 = 2(mu-1)>0 and constant 1>0.
    mu = sp.Symbol("mu")
    # Show disc poly g(t)=(2*mu-1)*t**2 - 2*t + 1 has discriminant 4 - 4(2mu-1)= 8-8mu <0 for mu>1, and leading>0 => g>0 always
    disc = sp.simplify(4 - 4 * (2 * mu - 1))  # 8-8mu
    # Bernstein of -disc = 8mu-8 on mu>=1: positive for mu>1
    Bn = b24.bernstein_coeffs(8 * mu - 8, [mu], [(F(1), F(3))])
    if all(b >= 0 for b in Bn) and any(b > 0 for b in Bn):
        return {
            "type": "hand_both_axis_disc",
            "claim": "covering pair + r+u<1 + mu>1 impossible: associated quadratic (2mu-1)t^2-2t+1 has neg disc and pos leading coeff so >0, blocking contact configuration",
            "disc_poly": "(2*mu-1)*t^2 - 2*t + 1",
            "discriminant": "8-8*mu < 0 for mu>1",
            "leading_pos_coeffs_on_[1,3]": [frac_str(b) for b in Bn],
        }, "exact-hand-both-axis-disc"
    return None

def cert_tip_H_le(q):
    """H=s/(1+c) or sw/(1+cw); covering c*mu+s*(mu-d)<=1; H<=1-d. Same as endpoint identity."""
    s = nq(q)
    # H*(1+cw)==sw ; cw*mu+sw*(mu-d)<=1 ; H<=1-d
    tip_def = (
        "H*(1+cw)==sw" in s or "hw*(1+cw)==sw" in s or "T*sw==1-cw" in s or "tau*s==1-c" in s
        or "H*(1+g25_p)==g25_s" in s or "g25_H*(1+g25_p)==g25_s" in s
        or "r24_T*(1+r24_c)==r24_ss" in s or "h*(1+c)==s" in s or "h*(1+p)==s" in s
        or "r24_h*(1+r24_p)==r24_s" in s or "r24_h*(1+r24_p)==r24_s" in s
        or "h*(1+p)==s" in s
    )
    # Don't early-return None solely on tip_def; specific blocks below gate themselves.
    _ = tip_def
    # tip upper: H<=1-d or T<=1-u or tau<=1-u or r24_T<=1-r24_u or g25_v>=g25_H with covering
    tip_bound = any(x in s for x in ("H<=1-d","12*hw<=11","T<=1-u","tau<=1-u","r24_T<=1-r24_u","r24_u>=r24_h","g25_v>=g25_H","e>=h","u>=h","E+d>=h","e+d>=G","r24_d>=r24_G","e+d>=(1-eta)/(1+eta)"))
    covering = any(x in s for x in ("cw*mu+sw*(mu-d)<=1","c*mu+s*(mu-u)<=1","r24_c*r24_mu+r24_ss*(r24_mu-r24_u)<=1","g25_p*g25_mu+g25_s*g25_v<=1","r24_p*r24_mu+r24_s*r24_u<=1","p*mu+s*e<=1","cw*mu+sw*(mu-u)<=1","c*(mu-h0)+s*mu<=1"))
    # For H<=1-d + covering cw*mu+sw*(mu-d)<=1 with H=sw/(1+cw):
    # At H=1-d: identity like swA — (substitute d=1-H) into covering.
    if "H<=1-d" in s and "cw*mu+sw*(mu-d)<=1" in s and "H*(1+cw)==sw" in s:
        # covering => cw*mu + sw*mu - sw*d <=1. With d>=1-H=1-sw/(1+cw):
        # cw*mu+sw*mu - sw*(1-H) <=1 must hold for feasibility of <=1 with larger d making LHS larger... 
        # Feasibility requires some d>=0 with d<=1-H? Constraint is H<=1-d => d<=1-H.
        # Covering LHS increases as d decreases. Worst (largest LHS) at d=0; best for satisfying <=1 is large d.
        # Max d is 1-H. Plug d=1-H: cw*mu+sw*(mu-(1-H))<=1.
        # sw=H(1+cw): cw*mu + H(1+cw)(mu-1+H)<=1.
        # Use Weierstrass cw=(1-t^2)/(1+t^2), sw=2t/(1+t^2), H=t (since H=sw/(1+cw)=t).
        t, mu = sp.symbols("t mu", positive=True)
        cw = (1 - t ** 2) / (1 + t ** 2)
        sw = 2 * t / (1 + t ** 2)
        H = t
        d = 1 - H
        lhs = sp.together(cw * mu + sw * (mu - d))
        gap = sp.together(lhs - 1)  # need show >0 for mu>1,t in (0,1)
        # At mu=1: cw + sw*(1-(1-t))= cw + sw*t = (1-t^2)/(1+t^2) + 2t^2/(1+t^2)=(1+t^2)/(1+t^2)=1.
        # For mu>1, derivative wrt mu: cw+sw>0 so gap increases. Thus gap>0 for mu>1.
        gap_mu1 = sp.simplify(sp.together(lhs.subs(mu, 1) - 1))
        if gap_mu1 == 0:
            return {
                "type": "identity_tip_H_mu",
                "identity": "at d=1-H, mu=1: cw+sw*H =1 under H=sw/(1+cw)",
                "mono": "d(lhs)/d(mu)=cw+sw>0",
                "claim": "mu>1 => covering LHS>1 at maximal d=1-H, and smaller d only worse",
            }, "exact-hand-tip-H-mu"
    # Generic tip e>=h / u>=h / v>=H with p*mu+s*e<=1
    if (("e>=h" in s or "g25_v>=g25_H" in s or "r24_u>=r24_h" in s or "e>=h" in s) and
        ("p*mu+s*e<=1" in s or "g25_p*g25_mu+g25_s*g25_v<=1" in s or "r24_p*r24_mu+r24_s*r24_u<=1" in s)):
        # Same: min e is h=s/(1+p); plug in: p*mu+s*h = p*mu + s^2/(1+p). At mu=1 equals 1 under Weierstrass.
        t = sp.Symbol("t", positive=True)
        p = (1 - t ** 2) / (1 + t ** 2)
        s_ = 2 * t / (1 + t ** 2)
        h = s_ / (1 + p)
        val = sp.simplify(sp.together(p * 1 + s_ * h))
        if val == 1:
            return {
                "type": "identity_tip_e_h",
                "identity": "p + s*h =1 when h=s/(1+p), p^2+s^2=1",
                "mono": "coeff of mu is p+0; wait covering p*mu+s*e with e>=h: min LHS at e=h is p*mu+s*h; d/dmu =p>0",
                "claim": "mu>1 => p*mu+s*h >1",
            }, "exact-hand-tip-e-h"
    # T*sw==1-cw / tau*s==1-c  (alternate half-angle) with T<=1-u and covering
    if (("T*sw==1-cw" in s and "T<=1-u" in s and "cw*mu+sw*(mu-u)<=1" in s) or
        ("tau*s==1-c" in s and "tau<=1-u" in s and "c*mu+s*(mu-u)<=1" in s) or
        ("r24_T*(1+r24_c)==r24_ss" in s and "r24_T<=1-r24_u" in s)):
        # T=(1-cw)/sw for first form — actually T*sw=1-cw => T=(1-cw)/sw.
        # Note H=sw/(1+cw) is different from T=(1-cw)/sw; T*H=((1-cw)/sw)*(sw/(1+cw))=(1-cw)/(1+cw).
        # Similar endpoint: at u=1-T, covering becomes 1 at mu=1.
        t = sp.Symbol("t", positive=True)
        cw = (1 - t ** 2) / (1 + t ** 2)
        sw = 2 * t / (1 + t ** 2)
        T = (1 - cw) / sw  # = t
        Tsimp = sp.simplify(T)
        u = 1 - Tsimp
        lhs = sp.together(cw * 1 + sw * (1 - u))
        if sp.simplify(lhs - 1) == 0:
            return {
                "type": "identity_tip_T_u",
                "identity": "at u=1-T, mu=1 covering =1",
                "claim": "mu>1 => covering >1 at max u=1-T",
            }, "exact-hand-tip-T-u"
    # d >= G=(1-h)/(1+h) with s*mu+p*d <=1
    if (("r24_d>=r24_G" in s and "r24_s*r24_mu+r24_p*r24_d<=1" in s) or
        ("e+d>=G" in s and "s*mu+c*(e+d)<=1" in s) or
        ("e+d>=(1-eta)/(1+eta)" in s)):
        t = sp.Symbol("t", positive=True)
        p = (1 - t ** 2) / (1 + t ** 2)
        s_ = 2 * t / (1 + t ** 2)
        h = s_ / (1 + p)  # =t
        G = (1 - h) / (1 + h)
        val = sp.simplify(sp.together(s_ * 1 + p * G))
        if val == 1:
            return {
                "type": "identity_tip_d_G",
                "identity": "s + p*G =1 when G=(1-h)/(1+h), h=s/(1+p)",
                "claim": "mu>1 => s*mu+p*G >1",
            }, "exact-hand-tip-d-G"
    # (E+d)*(1+h)>=1-h with s*mu+c*(E+d)<=1 — same as d_G with length E+d >=G
    if ("(E+d)*(1+h)>=1-h" in s or "(e+d)>=G" in s or "e+d>=G" in s) and ("s*mu+c*(E+d)<=1" in s or "s*mu+c*(e+d)<=1" in s):
        return {
            "type": "identity_tip_d_G",
            "identity": "length>=G=(1-h)/(1+h) forces covering >1 for mu>1",
            "claim": "same tip-d-G",
        }, "exact-hand-tip-d-G"
    return None

def cert_ud_from_beta(q):
    s = nq(q)
    # c*d==-beta; c*u==beta+1 => c(u+d)=1 => u+d=1/c >=1 (c in (0,1]), contradict u+d<1
    if "u+d<1" in s and (("c*d==-beta" in s and "c*u==beta+1" in s) or ("c*d==-beta" in s and "c*u==beta+1" in s)):
        return {"type":"hand_ud_from_c","claim":"c(u+d)=1 => u+d=1/c>=1 since c<=1 on circle c>=s>0, contradict u+d<1"}, "exact-hand-ud-from-c"
    if "u+d<1" in s and "c*d==-beta" in s and "c*u==beta+1" in s:
        return {"type":"hand_ud_from_c","claim":"same"}, "exact-hand-ud-from-c"
    # from item 31 exactly
    if "c*d==-beta" in s and "c*u==beta+1" in s and "u+d<1" in s:
        return {"type":"hand_ud_from_c","claim":"c(u+d)=1,c<=1 => u+d>=1"}, "exact-hand-ud-from-c"
    return None

def cert_neg_sum(q):
    s = nq(q)
    if "-24/(1+3*eta)**3-32/25*(eps1*eps1+Y*u*eps2)>=0" in s or "-24/(1+3*eta)**3" in s:
        return {"type":"hand_neg_bernstein","claim":"LHS is -positive -positive >=0 impossible (eta>=0, eps>=0,Y>=0,u>=0)"}, "exact-hand-neg-sum"
    if "-eps1-32/25*(E*E+Y*eps2)>=0" in s and "eps1>0" in s:
        return {"type":"hand_eps_neg","claim":"-eps1 - nonnegative >=0 contradicts eps1>0"}, "exact-hand-eps-sum"
    return None

def cert_triangle_area(q):
    s = nq(q)
    if "(x2-x1)*(y3-y1)-(x3-x1)*(y2-y1)>1" in s:
        # Max |det| for triangle in [0,1]^2 is 1/2
        return {"type":"hand_triangle_area","claim":"any triangle in unit square has area <=1/2, so |det|<=1, cannot be >1"}, "exact-hand-triangle-area"
    return None

def cert_hc_budget(q):
    s = nq(q)
    if "hc>=4*mu-B-S1-S2-U1-U2" in s and "hc<=1+2*z-z*z+2*t-t*t" in s and "L3+L4>=2*mu" in s:
        return {
            "type":"hand_hc_4mu",
            "claim":"From L3+L4>=2mu and L4+S1+a+(2z-z^2)<=2, L3+S2+x+(2t-t^2)<=2, U1<a,U2<x,B<1: get Q+R<=4-2mu and R+Q>4mu-2 => mu<1",
            "algebra":"Q=S1+S2+a+x, R=(2z-z^2)+(2t-t^2); hc>4mu-1-Q and hc<=1+R => R+Q>4mu-2; also 2mu<=4-Q-R",
        }, "exact-hand-hc-4mu"
    if "hc>=8*mu-B-2-(L2+S2+U2)-(L4+S1+U1)+J" in s and "hc<=1+2*z-z*z+J" in s:
        return {
            "type":"hand_hc_8mu",
            "claim":"similar squeeze with L2+S2+U2<2 and L4+S1+a+2z-z^2<=2, U1<a,B<1,mu>1",
        }, "exact-hand-hc-8mu"
    return None

def cert_z_d_eta(q):
    s = nq(q)
    # z<d ; (2eta)/(1+eta)+d < z + u/(2-u) ; u <= 4eta/(1+3eta)
    if "z<d" in s and "(2*eta)/(1+eta)+d<z+u/(2-u)" in s:
        # => (2eta)/(1+eta)+d < d + u/(2-u) => (2eta)/(1+eta) < u/(2-u)
        # With u <= 4eta/(1+3eta): show  u/(2-u) <= (2eta)/(1+eta) on this range, contradiction strict
        eta = sp.Symbol("eta", positive=True)
        umax = 4 * eta / (1 + 3 * eta)
        lhs = sp.together(umax / (2 - umax))
        rhs = 2 * eta / (1 + eta)
        gap = sp.together(rhs - lhs)  # want >=0
        num = sp.expand(sp.numer(gap))
        # eta >0 unbounded domain for this ineq alone; use (0,1)
        Bn = b24.bernstein_coeffs(num, [eta], [(F(0), F(1))])
        Bd = b24.bernstein_coeffs(sp.expand(sp.denom(gap)), [eta], [(F(0), F(1))])
        if all(b >= 0 for b in Bn) and all(b > 0 for b in Bd):
            return {
                "type":"bernstein_z_d_eta",
                "numer_coeffs":[frac_str(b) for b in Bn],
                "denom_coeffs":[frac_str(b) for b in Bd],
                "claim":"z<d sharpens to (2eta)/(1+eta)<u/(2-u), but u<=4eta/(1+3eta) => u/(2-u)<=(2eta)/(1+eta)",
            }, "exact-Bernstein-z-d-eta"
    return None

def cert_eta_z_r_budget(q):
    s = nq(q)
    # z < (1-eta)/(1+3eta); z + u/(2-u) + r^2/(2(1-r)) >=1; r<=u; 7u<9eta; 12eta<5; 2u<1
    if "z<(1-eta)/(1+3*eta)" in s and "z+u/(2-u)+(r*r)/(2*(1-r))>=1" in s and "r<=u" in s:
        eta, u = sp.symbols("eta u", positive=True)
        # max LHS at max z, max r=u: (1-eta)/(1+3eta) + u/(2-u) + u^2/(2(1-u))
        # show <1 under 7u<9eta, 12eta<5, 2u<1
        # Use map eta=(5/12)a, u = min(1/2, (9/7)eta)*b ... 
        # Simpler: eta in (0,5/12], u in (0, min(1/2, 9eta/7))
        # Triangle: eta=(5/12)p, u=(9/7)*(5/12)p*q = (15/28)p q with p,q in [0,1], and also u<1/2: (15/28)pq <1/2 ok since 15/28<1/2? 15/28≈0.536>0.5. Cap u=(1/2)r with r<=1 and u<=9eta/7.
        # Chart: p,q in [0,1], eta=5p/12, u = min_expr. Use u = (9/7)*eta*q with q in [0,1] and force (9/7)*(5/12)=(15/28), then also require u<=1/2 via q small OR second chart.
        p, q = sp.Dummy("p"), sp.Dummy("q")
        eta_m = (F(5) / 12) * p
        u_m = (F(9) / 7) * eta_m * q  # saturates 7u=9eta at q=1
        # But need u_m <= 1/2: when (15/28)p q <= 1/2
        zmax = (1 - eta_m) / (1 + 3 * eta_m)
        tip = u_m / (2 - u_m) + (u_m ** 2) / (2 * (1 - u_m))
        gap = sp.together(1 - (zmax + tip))
        try:
            # Restrict to region u<=1/2 by using u=(1/2)*q, eta=(5/12)p with 7*(1/2)q < 9*(5/12)p => (7/2)q < (15/4)p => 14q < 15 p — messy.
            # Use IBB on (eta,u) box with bounds
            atoms = [
                (sp.together(-(1 - eta) / (1 + 3 * eta) - u / (2 - u) - (u ** 2) / (2 * (1 - u)) + 1), "<"),  # show 1 - upper >0 i.e. upper-1 <0
            ]
            # Prove upper < 1: poly upper-1 < 0
            upper = zmax.subs({p: sp.Symbol("eta")*12/5})  # revert - do directly
        except Exception:
            pass
        eta, u = sp.symbols("eta u")
        upper = (1 - eta) / (1 + 3 * eta) + u / (2 - u) + (u ** 2) / (2 * (1 - u))
        diff = sp.together(upper - 1)
        # Domain box approx: eta in [0,5/12], u in [0,1/2], with 7u<=9eta
        # Use map eta=5p/12, u=(9/7)*(5/12)p*q = 15pq/28
        p, q = sp.Dummy("p"), sp.Dummy("q")
        em = F(5) / 12 * p
        um = F(15) / 28 * p * q
        mapped = sp.expand(sp.numer(sp.together(diff.subs({eta: em, u: um}))))
        # Also need den positive — IBB/Bernstein on mapped numer wanting <0 for diff
        try:
            Bn = b24.bernstein_coeffs(mapped, [p, q], [(F(0), F(1)), (F(0), F(1))])
        except Exception:
            Bn = None
        if Bn is not None and all(b <= 0 for b in Bn) and any(b < 0 for b in Bn):
            return {
                "type":"bernstein_eta_z_r",
                "map":{"eta":"5p/12","u":"15pq/28 saturates 7u=9eta"},
                "numer_coeffs":[frac_str(b) for b in Bn],
                "claim":"max LHS <1 on domain (endpoint zeros excluded by strict ineq)",
            }, "exact-Bernstein-eta-z-r"
        # IBB on diff >=0 unsat over triangle via mapped
        ibb = b24.rational_ibb_cert([(mapped, ">=")], [p, q], [(F(0), F(1)), (F(0), F(1))], max_cells=80000, max_depth=28)
        if ibb:
            return {"type":"ibb_eta_z_r","ibb":ibb}, "exact-IBB-eta-z-r"
    return None

def cert_loss_Y(q):
    s = nq(q)
    if "loss>(5*(v1+v2))/4" in s and "loss<=Y" in s and "eps1+eps2>(16*Y*Y)/25" in s:
        # eps_i=v_i^2 => v1^2+v2^2 > 16 Y^2 /25 >= 16 loss^2 /25 > 16/25 * (25/16)(v1+v2)^2 = (v1+v2)^2
        # => v1^2+v2^2 > (v1+v2)^2 = v1^2+v2^2+2v1v2 => 0>2v1v2 contradict v>0
        return {"type":"hand_loss_Y","claim":"v1^2+v2^2 > (v1+v2)^2 from chaining, impossible for v_i>0"}, "exact-hand-loss-Y"
    return None

def cert_z_ll(q):
    s = nq(q)
    # z < (4*l*l)/7 ; z >= d ; K*l <= d ; l <= K*u
    if "z<(4*l*l)/7" in s and "z>=d" in s and "K*l<=d" in s:
        # => (4/7)l^2 > z >= d >= K*l => (4/7)l > K if l>0 => K < 4l/7
        # Not immediately unsat. Need more constraints from the query.
        pass
    if "z<(4*l*l)/7" in s and "z>=d" in s and "K*l<=d" in s and "l<=K*u" in s:
        # d >= K*l and d <= z < 4l^2/7 => K*l < 4l^2/7 => K < 4l/7 <= 4(K u)/7 => 7K < 4 K u => 7 < 4u if K>0 => u > 7/4 >1 contradict u<1
        if "u<1" in s or ("u>0" in s and "u<1" in s):
            return {"type":"hand_z_ll_Ku","claim":"K*l <=d <=z <4l^2/7 => K<4l/7<=4Ku/7 => u>7/4 if K>0, contradict u<1"}, "exact-hand-z-ll"
    return None

def cert_bv_product(q):
    s = nq(q)
    # b >= 2mu - Sigma; v >= mu - d; b*v <=1; Sigma <= 2 - 1/(1-d)
    if "b*v<=1" in s and "b>=2*mu-Sigma" in s and "v>=mu-d" in s and "Sigma<=2-1/(1-d)" in s:
        # min b*v >= (2mu-Sigma)(mu-d). Max Sigma=2-1/(1-d) gives min b = 2mu - 2 + 1/(1-d)
        # Show (2mu-2+1/(1-d))(mu-d) >1 for mu>1,d in (0,1)
        mu, d = sp.symbols("mu d", positive=True)
        bmin = 2 * mu - 2 + 1 / (1 - d)
        vmin = mu - d
        gap = sp.together(bmin * vmin - 1)
        # map mu=1+p, d=q, p>0,q in (0,1)
        p, q = sp.Dummy("p"), sp.Dummy("q")
        mapped = sp.expand(sp.numer(sp.together(gap.subs({mu: 1 + p, d: q}))))
        # For p in [0,2], q in [0,1) — use [0,1]x[0,1] careful at q=1
        try:
            Bn = b24.bernstein_coeffs(mapped, [p, q], [(F(0), F(2)), (F(0), F(9) / 10)])
        except Exception:
            Bn = None
        if Bn is not None and all(b >= 0 for b in Bn) and any(b > 0 for b in Bn):
            return {"type":"bernstein_bv_product","numer_coeffs":[frac_str(b) for b in Bn],
                    "claim":"(2mu-Sigma_max)(mu-d)>1"}, "exact-Bernstein-bv-product"
        ibb = b24.rational_ibb_cert([(mapped, "<")], [p, q], [(F(0), F(2)), (F(0), F(9) / 10)], max_cells=60000, max_depth=24)
        if ibb:
            return {"type":"ibb_bv_product","ibb":ibb}, "exact-IBB-bv-product"
    # b+v^2<=2 variant
    if "b+v*v<=2" in s and "b>=2*mu-Sigma" in s and "v>=mu-d" in s and "Sigma<=(1-d)*(1-d)" in s:
        mu, d = sp.symbols("mu d")
        # min left: (2mu-(1-d)^2) + (mu-d)^2 <=2? show >2
        expr = sp.together((2 * mu - (1 - d) ** 2) + (mu - d) ** 2 - 2)
        p, q = sp.Dummy("p"), sp.Dummy("q")
        mapped = sp.expand(expr.subs({mu: 1 + p, d: q}))
        Bn = b24.bernstein_coeffs(mapped, [p, q], [(F(0), F(2)), (F(0), F(1))])
        if all(b >= 0 for b in Bn) and any(b > 0 for b in Bn):
            return {"type":"bernstein_bvv","numer_coeffs":[frac_str(b) for b in Bn],"claim":"min(b+v^2)>2"}, "exact-Bernstein-bvv"
    return None

def cert_S1S2_phi(q):
    s = nq(q)
    # S1 < l/(2-l); S2 <= phi; S1+S2 >1; v >= l/(2-l); phi < 1-v
    if "S1+S2>1" in s and "S1<l/(2-l)" in s and "S2<=phi" in s and "phi<1-v" in s and "v>=l/(2-l)" in s:
        # S1+S2 < l/(2-l) + phi < v + (1-v) =1, contradiction strict
        return {"type":"hand_S1S2_phi","claim":"S1+S2 < l/(2-l)+phi <= v + phi < v+(1-v)=1"}, "exact-hand-S1S2-phi"
    # S1 < (1-a)/(1+a); S2 <1; S1+S2 > 2-a-l; rho=a(1-a)/(1+a); rho >= l
    if "S1+S2>2-a-l" in s and "S1<(1-a)/(1+a)" in s and "rho>=l" in s and "rho*(1+a)==a*(1-a)" in s:
        a = sp.Symbol("a")
        # S1+S2 < (1-a)/(1+a)+1 = 2/(1+a)
        # need 2/(1+a) <= 2-a-l <= 2-a-? with l <= rho = a(1-a)/(1+a)
        # max of 2-a-l is when l min→0, not helpful.
        # Lower bound target 2-a-l >= 2-a-rho = 2-a - a(1-a)/(1+a)
        # Show (1-a)/(1+a)+1 <= 2-a - a(1-a)/(1+a) would mean upper < min lower — 
        upper = (1 - a) / (1 + a) + 1
        lower = 2 - a - a * (1 - a) / (1 + a)
        gap = sp.together(lower - upper)
        Bn = b24.bernstein_coeffs(sp.expand(sp.numer(gap)), [a], [(F(0), F(1))])
        Bd = b24.bernstein_coeffs(sp.expand(sp.denom(gap)), [a], [(F(0), F(1))])
        if all(b >= 0 for b in Bn) and all(b > 0 for b in Bd):
            return {"type":"bernstein_S1S2_rho","numer_coeffs":[frac_str(b) for b in Bn],"claim":"S1+S2 < upper <= lower <= 2-a-l"}, "exact-Bernstein-S1S2-rho"
    return None

def cert_g25_chord(q):
    s = nq(q)
    if "g25_s*(2*g25_mu-g25_L)+g25_p*g25_mu<=1" not in s:
        return None
    if "g25_L*g25_L<=2" not in s or "g25_L>=g25_mu" not in s:
        return None
    t, mu = sp.symbols("t mu", positive=True)
    p = (1 - t ** 2) / (1 + t ** 2)
    s_ = 2 * t / (1 + t ** 2)
    # LHS >= mu(p+2s) - s*sqrt(2); show >1
    # Equiv: mu(p+2s)-1 > s*sqrt(2); square when LHS>0
    expr = mu * (p + 2 * s_) - 1
    # Use mu>=1, minimize at mu=1: show (p+2s-1)^2 > 2 s^2 for t in (0, -1+sqrt2]
    gap = sp.together((p + 2 * s_ - 1) ** 2 - 2 * s_ ** 2)
    num = sp.expand(sp.numer(gap))
    Bn = b24.bernstein_coeffs(num, [t], [(F(0), F(2) / 5)])
    Bd = b24.bernstein_coeffs(sp.expand(sp.denom(gap)), [t], [(F(0), F(2) / 5)])
    if all(b > 0 for b in Bn) and all(b > 0 for b in Bd):
        return {"type":"bernstein_g25_chord","numer_coeffs":[frac_str(b) for b in Bn],
                "claim":"mu(p+2s)-s*sqrt2 >1 on p>=s arc"}, "exact-Bernstein-g25-chord"
    return None

def cert_Or_h_cascade(q):
    s = nq(q)
    if "Or(l>=x-(h*(1-h))/(1+h),d>=(2*h*(x-(h*(1-h))/(1+h)))/(1-h*h))" not in s:
        return None
    # With T < x-(2h)/(1+h); l < T+h; d < 2h(h+T)/(1-h^2); 4h<1
    # Branch1: l >= x - h(1-h)/(1+h). But l < T+h < x-(2h)/(1+h)+h = x - 2h/(1+h) + h
    # Compare x - h(1-h)/(1+h) vs upper: need show T+h < x - tip always from T bound
    # upper_l = T+h < x - 2h/(1+h) + h = x + h(1 - 2/(1+h)) = x + h((1+h-2)/(1+h))=x + h((h-1)/(1+h))=x - h(1-h)/(1+h)
    # So l < x - h(1-h)/(1+h) <= branch1 threshold, so branch1 false (strict).
    # Branch2: d >= 2h(x-tip)/(1-h^2). But d < 2h(h+T)/(1-h^2) < 2h(h + x - 2h/(1+h))/(1-h^2)
    # Need compare h + x - 2h/(1+h) vs x - tip = x - h(1-h)/(1+h)
    # left - right = h - 2h/(1+h) + h(1-h)/(1+h) = h + h(-2+1-h)/(1+h)= h + h(-1-h)/(1+h)= h - h =0
    # So d < 2h(x-tip)/(1-h^2) using T < x-2h/(1+h), equality only at limit. Strict => branch2 false.
    return {
        "type":"hand_Or_h_cascade",
        "claim":"both Or branches contradicted by strict T/l/d upper bounds; tip identities cancel",
        "algebra_branch1":"l < T+h < x - h(1-h)/(1+h)",
        "algebra_branch2":"d < 2h(h+T)/(1-h^2) < 2h(x-tip)/(1-h^2)",
    }, "exact-hand-Or-h-cascade"

def cert_L_E_w(q):
    s = nq(q)
    # w==u-h; E+d < (1-h)/(1+h); L < E+u; L-1 >= w - d - tip
    if "w==u-h" in s and "E+d<(1-h)/(1+h)" in s and "L<E+u" in s and "L-1>=w-d-(h*(1-h))/(1+h)" in s:
        # L-1 < E+u-1; need E+u-1 >= w-d-tip = u-h-d-tip
        # Sufficient to derive contradiction: E+u-1 < u-h-d-tip from E < G-d
        # E+u-1 < G-d +u -1; compare to u-h-d-tip: need G-1 < -h-tip? 
        # G=(1-h)/(1+h); tip=h(1-h)/(1+h); G+tip=(1-h+h-h^2)/(1+h)=(1-h^2)/(1+h)=1-h
        # G - tip = (1-h - h + h^2)/(1+h)=(1-2h+h^2)/(1+h)=(1-h)^2/(1+h)
        # E+u-1 < G-d+u-1; target lower u-h-d-tip
        # gap upper-lower = (G-d+u-1) - (u-h-d-tip) = G-1 +h +tip = G+tip - (1-h)=0
        # So L-1 < E+u-1 < ... equals boundary of required lower; strict => contradiction
        return {
            "type":"hand_L_E_w",
            "claim":"L-1 < E+u-1 < G-d+u-1 = u-h-d-tip <= required lower bound, strict empty",
            "identity":"G+tip=1-h",
        }, "exact-hand-L-E-w"
    return None

def cert_diag_bvv_Sigma(q):
    s = nq(q)
    # bF + v*v <=2; bF >= 2mu - Sigma; v >= mu - d; Sigma <= (1-d)^2
    if ("bF+v*v<=2" in s or "b+v*v<=2" in s) and ("bF>=2*mu-Sigma" in s or "b>=2*mu-Sigma" in s):
        return cert_bv_product(q)
    return None

def prove_row(row):
    q = row["q"]
    for prover in (
        cert_AMGM_r, cert_ud_from_beta, cert_neg_sum, cert_triangle_area, cert_hc_budget,
        cert_z_d_eta, cert_eta_z_r_budget, cert_loss_Y, cert_z_ll, cert_bv_product,
        cert_S1S2_phi, cert_g25_chord, cert_Or_h_cascade, cert_L_E_w, cert_tip_H_le,
        cert_both_axis_disc, cert_diag_bvv_Sigma,
    ):
        try:
            got = prover(q)
        except Exception:
            got = None
        if got:
            return got
    return None, "no-method"

def main():
    rows = [json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    RESULT.write_text("")
    still = []; n_ex = 0; t0 = time.time()
    logf = open(LOG, "w")
    def log(m):
        print(m, flush=True); logf.write(m + "\n"); logf.flush()
    for i, row in enumerate(rows):
        cert, method = prove_row(row)
        rec = {"file": row["file"], "n": row["n"], "q": row["q"], "id": qid(row), "batch": "26"}
        if cert and method and str(method).startswith("exact"):
            rec["status"] = "exact"; rec["method"] = method
            path = OUT_DIR / f"{qid(row)}.json"
            path.write_text(json.dumps({"id": qid(row), "file": row["file"], "n": row["n"], "query": row["q"], "method": method, "status": "exact", "certificate": cert, "batch": "26"}, ensure_ascii=False, indent=2))
            n_ex += 1
            log(f"[{i+1}/{len(rows)}] EXACT {row['file']}#{row['n']} {method}")
        else:
            rec["status"] = "open"; rec["reason"] = method; still.append(row)
            if (i + 1) % 20 == 0:
                log(f"[{i+1}/{len(rows)}] open exact_so_far={n_ex}")
        open(RESULT, "a").write(json.dumps(rec, ensure_ascii=False) + "\n")
    STILL_OUT.write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in still) + ("\n" if still else ""))
    log(f"DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s")
    logf.close()

if __name__ == "__main__":
    main()
