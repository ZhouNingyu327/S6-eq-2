#!/usr/bin/env python3
"""Machine-check G3 M7.1 narrative↔certificate alignment checklist."""
from __future__ import annotations
import json, sys
from pathlib import Path

ROOT = Path('/workspace/uploads/s6_user_proof')
CHECKLIST = ROOT / 'formalization/certs/g3_m7_1_alignment_checklist.json'
EX = ROOT / 'ex/all'
OUT = ROOT / 'formalization/audit/g3_alignment_check_result.json'

def main() -> int:
    cl = json.loads(CHECKLIST.read_text())
    errors, warnings = [], []
    for st in cl['steps']:
        for key in ('pdf_hyp', 'module_hyp', 'cert_query_hyp'):
            if key not in st or not st[key]:
                errors.append(f"{st['step_id']}: missing {key}")
        for hyp_key in ('pdf_hyp', 'module_hyp'):
            src = st[hyp_key]['source'].split()[0].split('§')[0]
            p = ROOT / src
            if not p.exists():
                alt = list(ROOT.rglob(Path(src).name))
                if not alt:
                    errors.append(f"{st['step_id']}: source missing: {src}")
                else:
                    warnings.append(f"{st['step_id']}: rglob {alt[0]}")
        for ch in st['cert_query_hyp']['primary_checkers']:
            if not list(EX.glob(ch)) and not list(ROOT.rglob(ch)):
                errors.append(f"{st['step_id']}: checker missing: {ch}")
        if st.get('smt_still_S', 1) != 0:
            errors.append(f"{st['step_id']}: still_S != 0")
        if not st.get('citation_aligned'):
            errors.append(f"{st['step_id']}: citation_aligned false")
    inv = json.loads((ROOT/'formalization/certs/m7_m8_m11_certificate_inventory.json').read_text())
    if inv['blocks']['M7']['still_S'] != 0:
        errors.append('inventory M7 still_S != 0')
    lean_geo = all(s.get('lean_geometry') for s in cl['steps'])
    result = {
        'updated': '2026-10-20 Asia/Shanghai',
        'n_steps': len(cl['steps']),
        'n_citation_aligned': sum(1 for s in cl['steps'] if s.get('citation_aligned')),
        'n_lean_geometry': sum(1 for s in cl['steps'] if s.get('lean_geometry')),
        'errors': errors,
        'warnings': warnings,
        'pass': len(errors) == 0,
        'G3_checklistClosed': len(errors) == 0,
        'G3_overallClosed': len(errors) == 0 and lean_geo,
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result['pass'] else 1

if __name__ == '__main__':
    sys.exit(main())
