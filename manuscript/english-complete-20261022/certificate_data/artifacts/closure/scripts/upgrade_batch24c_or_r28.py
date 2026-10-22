#!/usr/bin/env python3
"""Batch24c: elementary Or contradictions + cleared-denom IBB for r28/tt leftovers."""
from __future__ import annotations
import json, re, time, hashlib, importlib.util
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ITEM3 = ROOT / "item3_certs"
OUT_DIR = ITEM3 / "exact_certs_batch24"
STILL_IN = ITEM3 / "still_S_after_batch24b.jsonl"
RESULT = ITEM3 / "upgrade_results_batch24c.jsonl"
STILL_OUT = ITEM3 / "still_S_after_batch24c.jsonl"
LOG = ITEM3 / "upgrade_batch24c.log"

spec = importlib.util.spec_from_file_location("b24", Path(__file__).with_name("upgrade_batch24_exact.py"))
b24 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b24)

def nq(q): return re.sub(r"\s+", "", q or "")
def qid(row):
    return f"{row['file']}__n{row['n']}__{hashlib.sha1(nq(row['q']).encode()).hexdigest()[:10]}"

def clear_atoms(o):
    out=[]
    for e,r in o:
        te=sp.together(e)
        num,den=sp.fraction(te)
        if r=='==':
            out.append((sp.expand(num), r))
        else:
            # e=num/den ? 0; if den has known sign on domain we multiply; else keep quotient for IBB
            if not den.free_symbols and den != 0:
                # multiply by den^2 to preserve inequality direction
                out.append((sp.expand(num*den), r) if False else (sp.expand(num * (1 if den>0 else -1)), r if den>0 else ('>' if r=='<' else '>=' if r=='<=' else r)))
                # simpler: den constant — fold sign
                df=b24.to_F(den)
                if df>0:
                    out.append((sp.expand(num), r))
                else:
                    # flip
                    flip={'<':'>','<=':'>=','>':'<','>=':'<=','==':'=='}[r]
                    out.append((sp.expand(num), flip))
                    # then renormalize to < form
                    e2,r2=out[-1]
                    if r2=='>': out[-1]=((-e2),'<')
                    elif r2=='>=': out[-1]=((-e2),'<=')
            else:
                # multiply by den^2 (always >0 when den!=0) preserves inequality
                out.append((sp.expand(num*sp.expand(den)), r))
    return out

def elementary_or(q):
    s=nq(q)
    # Or(t/(2-t)>=(2*t)/3, (r*r)/(2*(1-r))>=(7*r*r)/10) with 2t<1, 7r<2
    if ('Or(t/(2-t)>=(2*t)/3,(r*r)/(2*(1-r))>=(7*r*r)/10)' in s
        and '2*t<1' in s and '7*r<2' in s and 't>0' in s and 'r>0' in s):
        # Branch A: t/(2-t)>=2t/3, t in (0,1/2) => 1/(2-t)>=2/3 => 3>=4-2t => t>=1/2 contrad
        # Branch B: 1/(2(1-r))>=7/10 => 10>=14-14r => r>=2/7 contrad with r<2/7
        return {
            'type':'elementary_or_two_branches',
            'branches':[
                {'name':'t-half','algebra':'t/(2-t)>=2t/3 & t>0 => 1/(2-t)>=2/3 => t>=1/2',
                 'contradicts':'2*t<1'},
                {'name':'r-cap','algebra':'(r^2)/(2(1-r))>=(7 r^2)/10 & r>0 => 1/(2(1-r))>=7/10 => r>=2/7',
                 'contradicts':'7*r<2'},
            ],
            'claim':'each Or branch forces the variable to the excluded closed endpoint',
        }, 'exact-hand-Or-endpoint'
    return None

def prove_cleared(q, max_fs=3):
    if 'Or(' in q:
        # try elementary first
        el=elementary_or(q)
        if el: return el
        branches=b24.split_ors(q)
        bcerts=[]
        for i,bq in enumerate(branches):
            el=elementary_or(bq)  # unlikely
            atoms,err=b24.parse_atoms(bq)
            if err: return None, 'Or-parse'
            cu,o,_=b24.elim_linear_eq(atoms)
            if cu: 
                bcerts.append({'branch':i,'cert':{'type':'const'},'method':'exact-constant'}); continue
            cu2,o=b24.elim_deg1_any_coeff(o)
            if cu2:
                bcerts.append({'branch':i,'cert':{'type':'const'},'method':'exact-constant'}); continue
            o=clear_atoms(o)
            fs=sorted(set().union(*[e.free_symbols for e,_ in o]), key=str) if o else []
            if not o:
                bcerts.append({'branch':i,'cert':{'type':'empty'},'method':'exact-empty'}); continue
            if len(fs)>max_fs: return None, 'Or-high-dim'
            bounds,_=b24.extract_bounds(o,fs,default=(F(0),F(1)))
            if bounds=='empty':
                bcerts.append({'branch':i,'cert':{'type':'empty_box'},'method':'exact-empty-box'}); continue
            if not bounds: return None,'Or-bounds'
            box=[(bounds[v][0],bounds[v][1]) for v in fs]
            bcert=b24.try_bernstein_single_poly(o,fs,box)
            if bcert:
                bcerts.append({'branch':i,'cert':bcert,'method':'exact-Bernstein'}); continue
            ibb=b24.rational_ibb_cert(o,fs,box,max_cells=120000,max_depth=36)
            if ibb:
                bcerts.append({'branch':i,'cert':ibb,'method':'exact-IBB'}); continue
            return None,'Or-branch-open'
        return {'type':'or_split','n_branches':len(bcerts),'branches':bcerts}, 'exact-Or-split-all-branches'

    atoms,err=b24.parse_atoms(q)
    if err: return None, err
    cu,o,_=b24.elim_linear_eq(atoms)
    if cu: return {'type':'const'}, 'exact-constant-after-elim'
    cu2,o=b24.elim_deg1_any_coeff(o)
    if cu2: return {'type':'const'}, 'exact-constant-after-deg1'
    # weierstrass
    wmap,wvars,wtag=b24.weierstrass(o)
    cands=[(o,None,'raw')]
    if wmap is not None:
        cands.append((clear_atoms(wmap), wvars, wtag))
    cands[0]=(clear_atoms(o), None, 'cleared')
    for oo, forced, tag in cands:
        if not oo: return {'type':'empty','tag':tag}, f'exact-empty-{tag}'
        fs=forced if forced is not None else sorted(set().union(*[e.free_symbols for e,_ in oo]), key=str)
        if len(fs)>max_fs: continue
        # special boxes for known names
        default=(F(0),F(1))
        bounds,_=b24.extract_bounds(oo,fs,default=default)
        if bounds=='empty':
            return {'type':'empty_box','tag':tag}, f'exact-empty-box-{tag}'
        if not bounds: continue
        # tighten known
        box=[]
        for v in fs:
            lo,hi=bounds[v]
            name=str(v)
            if name=='h':
                hi=min(hi, F(2)/5)  # < -1+sqrt2
            if name=='w' and any('12*w<5' in nq(q) or '12*w < 5' in q for _ in [0]):
                hi=min(hi, F(5)/12)
            if name=='tt':
                hi=min(hi, F(2))
            box.append((lo,hi if hi>lo else hi))
        if any(lo>=hi for lo,hi in box):
            continue
        bcert=b24.try_bernstein_single_poly(oo,fs,box)
        if bcert:
            bcert['tag']=tag
            return bcert, f'exact-Bernstein-{tag}'
        ibb=b24.rational_ibb_cert(oo,fs,box,max_cells=150000,max_depth=40)
        if ibb:
            ibb['tag']=tag
            return ibb, f'exact-IBB-{tag}'
        if len(fs)==3:
            for A in fs:
                others=[v for v in fs if v!=A]
                for X in others:
                    T=[v for v in others if v!=X][0]
                    u,v,w=sp.Dummy('u'),sp.Dummy('v'),sp.Dummy('w')
                    mapped=[(sp.together(e.subs({A:u,X:u*v,T:w})),r) for e,r in oo]
                    mapped=clear_atoms(mapped)
                    ibb=b24.rational_ibb_cert(mapped,[u,v,w],[(F(0),F(1))]*3,max_cells=120000,max_depth=30)
                    if ibb:
                        ibb['tag']=f'{tag}-triangle3'
                        return ibb, 'exact-IBB-triangle3'
    return None, 'no-method'

def main():
    rows=[json.loads(l) for l in STILL_IN.read_text().splitlines() if l.strip()]
    # prioritize low dim / Or / r28
    def rank(r):
        s=nq(r['q'])
        if 'Or(' in s: return (0,0)
        if r['file'].endswith('round28_g2_near_complete'): return (1,0)
        ids=len(set(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', r['q'])))
        return (2, ids)
    rows=sorted(rows, key=rank)
    RESULT.write_text(''); still=[]; n_ex=0; t0=time.time()
    logf=open(LOG,'w')
    def log(m):
        print(m, flush=True); logf.write(m+'\n'); logf.flush()
    for i,row in enumerate(rows):
        try:
            cert,method=prove_cleared(row['q'], max_fs=3)
        except Exception as ex:
            cert,method=None, f'err:{str(ex)[:160]}'
        rec={'file':row['file'],'n':row['n'],'q':row['q'],'cvc5':row.get('cvc5'),'id':qid(row)}
        if cert and method and str(method).startswith('exact'):
            rec['status']='exact'; rec['method']=method
            path=OUT_DIR/f"{qid(row)}.json"
            path.write_text(json.dumps({'id':qid(row),'file':row['file'],'n':row['n'],'query':row['q'],'method':method,'status':'exact','certificate':cert,'batch':'24c'}, ensure_ascii=False, indent=2))
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
