# Reproduction guide (ancillary package for arXiv)

**Paper:** Ningyu Zhou — *Six unit squares cannot cover a square of side greater than 2*  
**Claim tier:** computer-assisted mathematical completeness of \(S(6)=2\)  
**Not claimed:** independent peer review; full Lean re-proof of every metric inequality  

This folder is a self-contained *skeleton* for checking the Lean obligation layer
and the certificate registries. Full round-by-round JSON certificates and the
complete `ex/all/` checker tree live in the author’s verification archive
(companion to the long manuscript); spot-check scripts for key rounds are
included under `checkers/`.

---

## 0. Layout

| Path | Contents |
|---|---|
| `lean/S6Core/` | Lean 4 sources + `lakefile.toml` + `lean-toolchain` + `lake-manifest.json` |
| `certs/` | Certificate registries (near-end leaves, M7–M11, obligation batches) |
| `checkers/` | Representative Python checkers (R16, R29, R38, R41–42, R50, R55, R60–64) |
| `still_S/` | Evidence that `still_S=0` after batch b23d + R65 audit pointers |
| `audit/` | G3 alignment script/result; M8–M11 dual-wrapper / faithfulness JSON |
| `docs/` | Upload gate, publish checklist, obligation notes, soft-residual disposition |
| `scripts/` | Small auxiliary verifiers |

---

## 1. Lean 4: `lake build`

Requires a working Lean 4 / Lake installation. The pin is:

```
leanprover/lean4:v4.35.0
mathlib @ v4.35.0   (see lakefile.toml / lake-manifest.json)
```

```bash
cd lean/S6Core
lake update   # first time: fetches mathlib (large download)
lake build
```

Success: `Build completed successfully`. Closed modules build with **no `sorry`**
and **no extra axioms**.

Flag smoke-check (after a successful build):

```bash
cd lean/S6Core
cat > /tmp/eval_s6_flags.lean << 'LEAN'
import S6Core.WholeTheoremStatus
#eval S6.WholeTheoremStatus.wholeTheorem_S6_eq_2_closed
#eval S6.WholeTheoremStatus.minimal_blocking_set_for_math_completeness
LEAN
lake env lean /tmp/eval_s6_flags.lean
# expect: true
# expect: []
```

---

## 2. G3 narrative ↔ checker alignment

```bash
python3 audit/g3_alignment_check.py
# expect: pass / G3_checklistClosed / G3_overallClosed = true
# (script reads certs/g3_m7_1_alignment_checklist.json when run from package root;
#  if paths are hard-coded, run from the original formalization/ tree or edit cwd)
```

Precomputed result: `audit/g3_alignment_check_result.json`.

---

## 3. Certificate registries and `still_S=0`

- Inventories: `certs/m7_m8_m11_certificate_inventory.json`,
  `certs/m{8,9,10,11}_certificate_registry.json`,
  `certs/near_end_leaf_certificate_registry.json`
- Clearance note: `still_S/STILL_S_BLOCKED_zh.md` — **still_S = 0** after b23d
- Snapshots: `still_S/still_S_after_b23d.jsonl` (and prior b22d/b23*)
- Round-65 internal audit summary: `still_S/S6_round65_full_audit.md`,
  `still_S/bundle_verification_result.json`, `still_S/r65_manifest.json`

Faithfulness / dual-wrapper spot checks (M8–M11):

- `audit/faithfulness_G4_M8_M11_expanded.json`
- `audit/dual_wrapper_M8_M11_results.jsonl`
- `audit/faithfulness_M8_M11_spotcheck.json`

---

## 4. Spot-check checkers

Scripts under `checkers/` are the paper’s representative rounds. They typically
expect companion certificate JSON files that lived next to them in `ex/all/` of
the full verification tree. Use them as:

1. **Source audit** — read the predicates and certificate wiring; or
2. **Replay** — place the matching `*_certificate.json` (and helpers) beside
   the script, then `python3 checkers/check_round64.py` (etc.).

Included: R16 interval cover; R29 far-TOP; R38 empty-right; R41–42 (M8);
R50 / R55-final (M9); R60 / R62 (M10); R63 / R64 (M11).

---

## 5. Accuracy reminder

| Layer | Status in this package |
|---|---|
| Mathematical completeness \(S(6)=2\) (computer-assisted) | Asserted / closed |
| Lean obligations 1–4 skeleton | Closed (`wholeTheorem_S6_eq_2_closed = true`) |
| Certificate `still_S` | 0 |
| Independent peer review | **Not done** |
| Full Lean re-proof of every R30–64 metric inequality | **Not done** (certificate-primary) |

See `docs/UPLOAD_GATE_zh.md` and `docs/THEOREM_CORE_summary.md`.
