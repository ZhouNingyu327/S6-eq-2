#!/usr/bin/env python3
"""Machine-check G3 M7.1 narrative↔certificate alignment checklist.

Paths are repo-relative to this script:
  artifacts/audit/g3_alignment_check.py
  → ARTIFACTS = artifacts/
  → REPO = repository root

Honesty: this script checks that cited sources/checkers exist and that
checklist metadata fields are non-empty / have expected flags. It does **not**
translate paper hypotheses into solver constraints, nor prove geometric
equivalence. See the 2026-10-21 public-snapshot referee report.
"""
from __future__ import annotations
import json, sys
from pathlib import Path

AUDIT = Path(__file__).resolve().parent
ARTIFACTS = AUDIT.parent
REPO = ARTIFACTS.parent
CHECKLIST = ARTIFACTS / 'certs' / 'g3_m7_1_alignment_checklist.json'
INVENTORY = ARTIFACTS / 'certs' / 'm7_m8_m11_certificate_inventory.json'
CHECKERS = ARTIFACTS / 'checkers'
OUT = AUDIT / 'g3_alignment_check_result.json'

# Optional *in-repo* overlay only (no absolute private paths).
PRIVATE_HINTS = [
    REPO / 'private_ex_all',
    ARTIFACTS / 'private_overlay',
]


def _exists_named(name: str) -> Path | None:
    """Find a checker/source by basename under the public tree / optional overlays."""
    for base in (CHECKERS, ARTIFACTS, REPO, *PRIVATE_HINTS):
        if not base.exists():
            continue
        hits = list(base.rglob(name))
        if hits:
            return hits[0]
    return None


def main() -> int:
    if not CHECKLIST.exists():
        print(f'Missing checklist: {CHECKLIST}', file=sys.stderr)
        return 2
    cl = json.loads(CHECKLIST.read_text(encoding='utf-8'))
    errors, warnings = [], []
    for st in cl.get('steps', []):
        sid = st.get('step_id', '?')
        for key in ('pdf_hyp', 'module_hyp', 'cert_query_hyp'):
            if key not in st or not st[key]:
                errors.append(f'{sid}: missing {key}')
        for hyp_key in ('pdf_hyp', 'module_hyp'):
            if hyp_key not in st or not st[hyp_key]:
                continue
            src = st[hyp_key]['source'].split()[0].split('§')[0]
            # Sources often point at private closure/*.md — search publicly first.
            # Strip trailing parenthetical notes and URL fragments for filesystem check.
            src_path = src.split('(')[0].strip().split('#')[0].strip()
            p = REPO / src_path
            if not p.exists():
                alt = _exists_named(Path(src_path).name)
                # Prefer long-proof module if checklist already points there by fragment.
                if alt is None and 'long_proof' in src:
                    lp = ARTIFACTS / 'long_proof' / 'S6_full_proof.md'
                    if lp.exists():
                        warnings.append(
                            f'{sid}: source path has fragment/anchor; using {lp.relative_to(REPO)}'
                        )
                        alt = lp
                if alt is None:
                    # Graceful: warn for known migrated peer_ready history; error otherwise.
                    if 'peer_ready' in src or 'S6_attack_round' in src:
                        warnings.append(
                            f'{sid}: historical source not in public tree: {src} '
                            f'(see artifacts/long_proof/S6_full_proof.md module anchors)'
                        )
                    else:
                        errors.append(
                            f'{sid}: source missing in public tree: {src}'
                        )
                else:
                    warnings.append(f'{sid}: resolved via search → {alt}')
        cq = st.get('cert_query_hyp') or {}
        for ch in cq.get('primary_checkers', []):
            hit = _exists_named(ch)
            if hit is None:
                errors.append(f'{sid}: checker missing: {ch}')
            elif 'uploads/s6_user_proof' in str(hit):
                warnings.append(f'{sid}: checker only in private hint path: {ch}')
        if st.get('smt_still_S', 1) != 0:
            errors.append(f'{sid}: still_S != 0')
        if not st.get('citation_aligned'):
            errors.append(f'{sid}: citation_aligned false')
    if INVENTORY.exists():
        inv = json.loads(INVENTORY.read_text(encoding='utf-8'))
        if inv.get('blocks', {}).get('M7', {}).get('still_S', 1) != 0:
            errors.append('inventory M7 still_S != 0')
    else:
        errors.append(f'missing inventory: {INVENTORY}')
    lean_geo = all(s.get('lean_geometry') for s in cl.get('steps', []))
    result = {
        'updated': '2026-10-21 Asia/Shanghai',
        'repo_root': str(REPO),
        'artifacts_root': str(ARTIFACTS),
        'honesty': (
            'File/metadata checklist only; not a geometric entailment check. '
            'Private closure/*.md sources may be absent from the public dump.'
        ),
        'n_steps': len(cl.get('steps', [])),
        'n_citation_aligned': sum(1 for s in cl.get('steps', []) if s.get('citation_aligned')),
        'n_lean_geometry': sum(1 for s in cl.get('steps', []) if s.get('lean_geometry')),
        'errors': errors,
        'warnings': warnings,
        'pass': len(errors) == 0,
        'G3_checklistClosed': len(errors) == 0,
        'G3_overallClosed': len(errors) == 0 and lean_geo,
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result['pass'] else 1


if __name__ == '__main__':
    sys.exit(main())
