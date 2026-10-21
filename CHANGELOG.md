# Changelog

## 2026-10-21 — KNOWN_GAPS advance (vs `8672f31`)

- Lean: `Faithfulness.lean` + classification regressions; README / formalization.yaml state proved vs open.
- Internal G5 rebuild notes (EN+ZH); external-referee gap kept open.
- Strong M1 explicitly deferred; primary remains stepwise reclassification.
- Item3 upgrade ledger + remaining (S) inventory under `artifacts/closure/`.
- Short paper §§5–7 expanded with Hyp⇒Concl module tables.

## 2026-10-21 — Lean Major 3 API + normalisation migration note (vs `5bfd66a`)

- **Ownership flags:** primary API is `flagsOfTarget` / `flagsOfTargetRotated` using the four target outer mids and `F∋O` (centre). Legacy MidCandidates wiring moved to `legacyFlagsOf*`; `flagsOfRotated` no longer feeds `fHasAnyMidCandidate` into `fHasO`.
- **Regression:** `ClassificationExample.lean` — rereview counterexample now has `k=1`, `fHasO=false` (legacy still `k=0`, `fHasO=true`).
- **Roles:** `RoleSelection.ofCover` uses the sixth Fin-6 index as `iF`; `toManuscript` / `manuscriptOfRoles` apply one `RotatedSquare.pullback` into the centre body chart.
- **Normalisation:** `artifacts/closure/M1_module_migration.md` (+ zh); long-proof “later = id” scoped to optional strong scheme.
- **Not claimed:** end-to-end geometric faithfulness theorem, external peer review, or elevation of strong M1.


## 2026-10-21 — rereview fixes (vs `32e0e0f`)

Addressed the 2026-10-21 public-repository rereview without inventing new geometry:

- **R8:** shipped `artifacts/ex/all/round8_pair_bernstein_certificate.json` (45 Bernstein leaves; also under `artifacts/checkers/`).
- **R13:** shipped `round13_pair_certificate.json`.
- **R16:** documented generate-then-verify commands in `REPRODUCE.md` / `referee_pack/HOW_TO_REPRODUCE.md`.
- **R6:** long-proof Markdown tangency fix `d0>0` → `d0≥0` with `c(1−α)+sβ≥μ>1` (Markdown = source of truth).
- **Normalisation:** primary protocol = short-paper stepwise reclassification; App. A / long-proof M1 marked optional candidate; closed first quadrant + axial branch; `W` = post-preprocess free corner.
- **Hygiene:** g3 checklist R38/R39 → long-proof anchors; reproduce docs synced; removed obsolete “ex/all not shipped” conflict.
- **Lean Major 3:** still **open**; stronger FIXME comments only.

See `referee_pack/KNOWN_GAPS.md`.

## 2026-10-21 — expert-facing repository

- Expert-first README and referee guide; non-math process files removed.
- Paper presentation cleaned (author/thanks/abstract surface); mathematical status unchanged.
- Gaps remain as in `referee_pack/KNOWN_GAPS.md` (Lean Major 3; external review; (S)-tier steps).

## 2026-10-21 — submission-oriented pack

- `referee_pack/`, paper Apps. A–D, `artifacts/closure/`, `ex_all.tar.gz` + hashes.
- Spot checks `check_round64` / `check_round63` / `m3_branch_checker` on clean tree.

## 2026-10-21 — maturity fix vs `9930699`

| Item | Status |
| --- | --- |
| 1 Long proof / certificates | Long manuscript + companion JSON + `ex/all` shipped; short paper outlines to module IDs |
| 2 Lean completion flags | Status metadata only |
| 3 Classification Lean ↔ manuscript | **Open** |
| 4 One-shot normalisation ⇒ later = id | Weakened in short paper |
| 5 Π quantifier | Fixed (∃ε) |
