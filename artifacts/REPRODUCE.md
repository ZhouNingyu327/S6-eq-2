# Reproduction guide

**Paper:** AI assistant (released by Ningyu Zhou) — *Six unit squares cannot cover a square of side greater than 2*  
**Claim tier:** computer-assisted **candidate** (under revision after 2026-10-21 public-snapshot review)  
**Not claimed:** independent peer review; confirmed resolution of \(S(6)=2\); Lean Bool flags as geometric theorems

Paths below are relative to the **repository root** unless noted.

---

## 0. Layout

| Path | Contents |
|---|---|
| `lean/S6Core/` | Lean 4 skeleton + Lake pin |
| `artifacts/certs/` | Certificate registries |
| `artifacts/checkers/` | Spot-check Python scripts **plus companion JSON** for R42/R54–55/R64 |
| `artifacts/still_S/` | Audit notes + honest manifests (empty `b23d` replaced) |
| `artifacts/audit/` | G3 alignment script (repo-relative paths) |
| `artifacts/long_proof/` | Long verification manuscript (`.md` + `.pdf`) |
| `artifacts/ex_all.tar.gz`, `artifacts/ex/all/` | Historical verification tree |
| `artifacts/SHA256SUMS.txt` | Hashes for archive + files |
| `artifacts/closure/` | M1–M4 notes + `m3_branch_checker.py` |
| `artifacts/DOWNLOADS/` | Pointer README (ex/all now shipped) |

---

## 1. Lean 4: `lake build` (skeleton only)

```bash
cd lean/S6Core
lake update   # first time: fetches mathlib
lake build
```

Success means the **shipped skeleton** builds with no `sorry` / extra axioms.
Boolean flags such as `wholeTheorem_S6_eq_2_closed` are **status metadata**
(`statusMetadata_candidate_S6_eq_2_flag`); evaluating them to `true` is not a
proof of \(S(6)=2\).

---

## 2. G3 narrative ↔ file checklist

```bash
cd artifacts
python3 audit/g3_alignment_check.py
```

Paths are resolved from this repository only (optional in-repo overlays:
`private_ex_all/`, `artifacts/private_overlay/`). On a clean public clone the
script is expected to **report errors** for checklist sources such as
`closure/*.md` and some far-end checkers that were not shipped — that is
documented deferred delivery, not a path bug. Precomputed
`audit/g3_alignment_check_result.json` records the latest run.

---

## 3. Spot-check checkers (clean clone)

Companion JSON files are next to the scripts (and under `checkers/work/` for
scripts that prefer a `work/` directory):

```bash
cd artifacts/checkers
python3 check_round64.py      # needs round64_certificate.json (shipped)
python3 check_round63.py      # self-contained identities
python3 check_round55_final.py  # needs round55_certificate.json + round54_certificate.json
python3 check_round42.py      # needs work/round42_interval_certificate.json (shipped) + `z3` (`pip install z3-solver`)
# R29 / R38 scripts generate JSON; prior outputs are also shipped for comparison
```

---

## 4. `still_S` honesty

- `still_S/still_S_after_b23d.jsonl` was **0 bytes** in public commit `9930699`.
  It is replaced by a one-line pointer + `still_S_after_b23d_MANIFEST.json`.
- Do **not** treat an empty log as PASS.
- Prior non-empty snapshots: `still_S_after_b22d.jsonl`, `still_S_after_b23c.jsonl`.
- Round-65 audit narrative: `S6_round65_full_audit.md` (includes β-clamp /
  stepwise reclassification notes in §4).

---

## 5. Long proof

See `long_proof/S6_full_proof.md` and `.pdf` with `long_proof/SHA256SUMS.json`.

---

## 6. Omitted `ex/all/`

Full historical checker/certificate tree omitted for size. Hash inventory:
`DOWNLOADS/ex_all_SHA256_manifest.json`. Spot-check companions for key rounds
are shipped under `checkers/`.

---

## 7. Accuracy reminder

| Layer | Status in this package |
|---|---|
| \(S(6)=2\) as confirmed theorem | **Not claimed** (candidate under revision) |
| Lean obligations skeleton | Partial; Bool flags = metadata |
| Ownership / role fidelity to manuscript | **Open** (FIXME in Lean sources) |
| One-shot “later normalisations = id” | **Retracted** in short paper; stepwise reclassification |
| Certificate spot checks (shipped) | Runnable for R63/R64/R55/R42 when deps present |
| Independent peer review | **Not done** |
