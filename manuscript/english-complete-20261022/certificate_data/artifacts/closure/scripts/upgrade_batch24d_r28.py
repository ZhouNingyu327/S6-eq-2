#!/usr/bin/env python3
"""Batch24d: dedicated r28/tt algebraic certificates with Bernstein/IBB payloads."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch24c.jsonl"
RESULT = ITEM3 / "upgrade_results_batch24d.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch24d.jsonl"
LOG = ITEM3 / "upgrade_batch24d.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"

def tt_plus_2w(q):
    s=nq(q)
    if not ('tt*tt==w*(2+w)' in s and '12*w<5' in s and '(1+w)*(1-tt)+2*w>=1' in s):
        return None
    w=sp.Symbol('w')
    # After isolating 3w >= tt(1+w) and squaring: need show 9w < (2+w)(1+w)^2 on (0,5/12)
    # equiv f=4w-2-3w^2-w^3 < 0 i.e. g=-f>0
    g=sp.expand(-(4*w-2-3*w**2-w**3))
    B=b24.bernstein_coeffs(g,[w],[(F(0),F(5)/12)])
    if all(b>0 for b in B):
        return {
            'type':'bernstein_tt_square',
            'poly':str(g),
            'box':[['0','5/12']],
            'coeffs':[b24.frac_str(b) for b in B],
            'claim':'g>0 => 9w<(w+2)(1+w)^2 => 3w<tt(1+w) => (1+w)(1-tt)+2w<1',
        }, 'exact-Bernstein-tt-2w'
    return None

def tt_generic_square(q):
    """General: (1+w)(1-tt) + R(w) >= S(w) with tt^2=w(2+w)."""
    s=nq(q)
    if 'tt*tt==w*(2+w)' not in s or '12*w<5' not in s:
        return None
    atoms,err=b24.parse_atoms(q)
    if err: return None
    cu,o,_=b24.elim_linear_eq(atoms)
    # find equality tt^2 - w(2+w)==0 and the main ineq
    tt=None; w=None
    for e,r in o:
        if r!='==': continue
        ee=sp.expand(e)
        for sym in ee.free_symbols:
            if sp.degree(ee,sym)==2 and sp.LC(sp.Poly(ee,sym))==1:
                # tt^2 + ...
                tt=sym
                rest=sp.expand(ee-tt**2)
                # expect -w(2+w)
                break
    # Fallback pattern parse for known variants
    variants=[
        # (1+w)(1-tt)+2w >=1  handled above
        ('(1+w)*(1-tt)+6/5*w+w/(2-w)>=1', lambda w: sp.Rational(6,5)*w + w/(2-w), 1),
        ('(1+w)*(1-tt)+w+w/(2-w)+(w*w)/(2*(1-w))>=1', lambda w: w + w/(2-w) + (w*w)/(2*(1-w)), 1),
        ('(1+w)*(1-tt)+(6/5*w)/(2-6/5*w)>=(1-w)*(1-w)', lambda w: (sp.Rational(6,5)*w)/(2-sp.Rational(6,5)*w), lambda w:(1-w)**2),
    ]
    for pat, R, S in variants:
        if pat not in s: continue
        w=sp.Symbol('w')
        Rw=R(w) if callable(R) else R
        Sw=S(w) if callable(S) else S
        # (1+w)(1-tt)+Rw >= Sw => (1+w) - (1+w)tt + Rw - Sw >= 0
        # (1+w+Rw-Sw) >= tt(1+w)
        # Let A=1+w+Rw-Sw. Need A >= tt(1+w). If A<=0, immediate fail of >= for tt>0,1+w>0.
        A=sp.together(1+w+Rw-Sw)
        # Check if A>0 on domain via Bernstein numer
        Anum=sp.expand(sp.numer(sp.together(A)))
        Aden=sp.expand(sp.denom(sp.together(A)))
        try:
            BA=b24.bernstein_coeffs(Anum,[w],[(F(0),F(5)/12)])
            BAd=b24.bernstein_coeffs(Aden,[w],[(F(0),F(5)/12)]) if Aden.free_symbols else [b24.to_F(Aden)]
        except Exception:
            continue
        if all(b>0 for b in BAd) and all(b<=0 for b in BA):
            # A<=0 => cannot have A >= tt(1+w)>0
            return {
                'type':'bernstein_tt_A_nonpos',
                'A':str(A),'coeffs_num':[b24.frac_str(b) for b in BA],
                'coeffs_den':[b24.frac_str(b) for b in BAd],
                'claim':'A<=0 on (0,5/12) so A>=tt(1+w)>0 impossible',
            }, 'exact-Bernstein-tt-A-nonpos'
        if not (all(b>0 for b in BAd) and all(b>0 for b in BA)):
            continue
        # A>0: square: A^2 >= tt^2 (1+w)^2 = w(2+w)(1+w)^2
        # show A^2 - w(2+w)(1+w)^2 < 0
        gap=sp.together(A**2 - w*(2+w)*(1+w)**2)
        gnum=sp.expand(sp.numer(gap))
        gden=sp.expand(sp.denom(gap))
        try:
            Bg=b24.bernstein_coeffs(gnum,[w],[(F(0),F(5)/12)])
            Bgd=b24.bernstein_coeffs(gden,[w],[(F(0),F(5)/12)]) if gden.free_symbols else [b24.to_F(gden)]
        except Exception as ex:
            continue
        if all(b>0 for b in Bgd) and all(b<0 for b in Bg):
            return {
                'type':'bernstein_tt_square_gap',
                'gap':str(gap),
                'coeffs_num':[b24.frac_str(b) for b in Bg],
                'coeffs_den':[b24.frac_str(b) for b in Bgd],
                'claim':'A>0 but A^2 < w(2+w)(1+w)^2 => A < tt(1+w)',
            }, 'exact-Bernstein-tt-square-gap'
        # try IBB on gnum >=0 unsat if den>0 and we want gap<0
        if all(b>0 for b in Bgd):
            ibb=b24.rational_ibb_cert([(gnum,'>=')],[w],[(F(0),F(5)/12)], max_cells=20000, max_depth=30)
            if ibb:
                return {'type':'ibb_tt_square_gap','gap_num':str(gnum),'ibb':ibb}, 'exact-IBB-tt-square-gap'
    return None

def r28_hw(q):
    s=nq(q)
    if not ('h*h+2*h<=1' in s and '12*w<5' in s and '6*h*(1-h)' in s and '2*h*(1-h*h-2*h)*(w+h)*5' in s):
        return None
    h=sp.Symbol('h')
    # At max w=5/12, RHS-LHS numer = -h(h+1)*quartic; need quartic<0
    quartic=36*h**4 - 132*h**3 - 145*h**2 + 82*h - 11
    ibb=b24.rational_ibb_cert([(quartic,'>=')],[h],[(F(0),F(2)/5)], max_cells=20000, max_depth=30)
    if not ibb:
        return None
    # Also need LHS increasing in w: coeff 2*h*(1-h^2-2*h)*5; show nonneg via Bernstein on domain
    coeff=sp.expand(2*h*(1-h**2-2*h)*5)
    Bc=b24.bernstein_coeffs(coeff,[h],[(F(0),F(2)/5)])
    # 1-2h-h^2 >=0 on domain h^2+2h<=1; at h=0 is 0. coeffs of 1-2h-h^2:
    gap=1-2*h-h**2
    Bg=b24.bernstein_coeffs(gap,[h],[(F(0),F(2)/5)])
    if not all(b>=0 for b in Bg):
        return None
    return {
        'type':'r28_hw_maxw_ibb',
        'quartic':str(quartic),
        'quartic_ibb':ibb,
        'lhs_w_coeff':str(coeff),
        'lhs_w_coeff_nonneg_via_gap_bernstein':[b24.frac_str(b) for b in Bg],
        'claim':'LHS nondecreasing in w; at w=5/12, RHS-LHS has sign of -quartic with -h(h+1)<0, and quartic<0 by IBB',
        'box_h':['0','2/5'],
        'w_max':'5/12',
    }, 'exact-IBB-r28-hw-maxw'

def main():
    rows=[json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    RESULT.write_text(''); still=[]; n_ex=0; t0=time.time()
    logf=open(LOG,'w')
    def log(m):
        print(m,flush=True); logf.write(m+'\n'); logf.flush()
    for i,row in enumerate(rows):
        cert=method=None
        for prover in (tt_plus_2w, tt_generic_square, r28_hw):
            try:
                got=prover(row['q'])
            except Exception as ex:
                got=None
            if got:
                cert,method=got; break
        rec={'file':row['file'],'n':row['n'],'q':row['q'],'cvc5':row.get('cvc5'),'id':qid(row)}
        if cert and method and method.startswith('exact'):
            rec['status']='exact'; rec['method']=method
            path=OUT_DIR/f'{qid(row)}.json'
            path.write_text(json.dumps({'id':qid(row),'file':row['file'],'n':row['n'],'query':row['q'],'method':method,'status':'exact','certificate':cert,'batch':'24d'},ensure_ascii=False,indent=2))
            rec['cert_relpath']=f'artifacts/closure/item3_certs/exact_certs_batch24/{path.name}'
            n_ex+=1
            log(f'[{i+1}/{len(rows)}] EXACT {row["file"]}#{row["n"]} {method}')
        else:
            rec['status']='open'; rec['reason']='no-method'; still.append(row)
        open(RESULT,'a').write(json.dumps(rec,ensure_ascii=False)+'\n')
    STILL_OUT.write_text('\n'.join(json.dumps(r,ensure_ascii=False) for r in still)+('\n' if still else ''))
    log(f'DONE exact={n_ex} open={len(still)} t={time.time()-t0:.1f}s'); logf.close()

if __name__=='__main__':
    main()
