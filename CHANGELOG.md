## v0.26 — centre outer-miss + projWidth mid-miss (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: centre tile misses all four outers when `μ²>2`
  (`RoleSelection` / `PointwiseCover`); `projWidth_lt_mu_of_mu_sq_gt`;
  SW mid-miss when `|c|+|s|<μ` (partial μ²≤2 path).
- `rotatedMidPackingProved` remains false. `principalClaimProvedUnconditionally=false`.
- Lake green. Honest bar still ~80–84%.

## v0.25 — corner mid-miss when μ²>2 (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: SW/SE/NE/NW miss both midlines when `μ²>2`;
  `PointwiseCover_corner_mid_miss_of_mu_sq_gt`; corner outer+mid pack skeleton.
  `rotatedMidPackingProved` remains false (μ²≤2 / fillers open).
- Still open: full mid packing; general `ChordMatrixExport`;
  `principalClaimProvedUnconditionally=false`.
- Lake green. Honest bar still ~80–84%.

## v0.24 — four-corner clamped outer packing (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: SE/NE/NW clamped outer pairs ≤2; helpers
  `clamped*Len_le_hi` / `_le_two_mu_sub_lo`; `PointwiseCover_corner_clamped_outer_le_two`.
  Flag `rotatedCornerClampedOuterPackingProved=true`.
- Still open: mid packing; general `ChordMatrixExport`;
  `principalClaimProvedUnconditionally=false`.
- Lake green. Honest bar still ~80–84%.

## v0.23 — SW clamped outer packing toward squareTotal≤2 (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: `distSq_containsR_le_two`; Inf/Sup endpoints in closed slices;
  `clampedHorizLen`/`clampedVertLen` on `[0,2μ]`; SW corner `bottom+left` clamped sum ≤2.
- Still open: SE/NE/NW pairs; mid packing; general `ChordMatrixExport`;
  `principalClaimProvedUnconditionally=false`.
- Lake green. Honest bar still ~80–84%.

## v0.22 — six-line real lift + parallel miss (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: `|Δx|/|Δy| ≤ |c|+|s|`; parallel miss bottom↔top and
  left↔right when `μ>1`; `vertSliceR` Inf-Sup chords; `RotatedSixLineRealLift`
  inhabited from any `RotatedGridRatCover` (all six grid lines, no axis hyp).
- Flags: `rotatedSixLineRealLiftProved=true`; general `ChordMatrixExport` still open;
  `principalClaimProvedUnconditionally=false`.
- Lake green. Honest bar still ~80–84%.

## v0.21 — real chord slices inhabit LineMeasureLift (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: `containsR`/`toBodyR`/`rotateInvR`; `horizSliceR` closed + bdd;
  Inf/Sup chords with length ≤2; rat→real bottom `Icc` cover; `RotatedLineMeasureLift`
  inhabited from any `RotatedGridRatCover` (no axis hyp). Flag `rotatedLineMeasureLiftProved=true`.
- Still open: general `RotatedChordMatrixExport` / `RotatedSixLineMeasureLift`;
  `principalClaimProvedUnconditionally=false`.
- Lake green. Honest bar still ~80–84%.

## v0.20 — axis path inhabits ChordMatrixExport (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: `RotatedChordMatrixExport_of_axisCoverBridge` /
  `_of_axisRealisation`; `axisGridContrib_le_two_of_roles`; axis six-line chord table;
  axis-aligned ⇒ bottom `RotatedLineChordCover`.
- Flags remain false for general (non-axis) inhabit; `principalClaimProvedUnconditionally=false`.
- Lake green. Honest bar still ~80–84%.

## v0.19 — corner diameter-miss + ChordMatrixExport (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: SW/SE/NE/NW diameter-miss vs opposite outer sides; meet
  predicates; `PointwiseCover_corner_diameter_miss`; onesided axial sum ≤2;
  `RotatedChordMatrixExport` ⇒ SixLineMeasureLift / CoverIneq / G5k0Bridge.
- Flags remain false: `rotatedChordMatrixExportProved`, `principalClaimProvedUnconditionally`.
- Lake green. Honest bar still ~80–84%.

## v0.18 — six-line measure-lift packaging + G3 cap reduction (2026-10-22 Asia/Shanghai)

- `RotatedChordMeasure`: horiz/vert chord Δ²≤2 and |Δ|≤2; `RotatedLineChordCover` with
  `sum_ge` / `sum_le_twelve`; named open `RotatedSixLineMeasureLift` /
  `RotatedLineMeasureLift`; bridges to CoverIneq, G5k0Bridge, GeomExport, LinePackageExport.
- `G3G4Fragments`: `G3CapGeometryExport`, `ParallelBudgetData_of_cap`,
  `G3SepWitnessExport_of_capSep` ⇒ ParallelBudget / exclusion.
- Flags remain false: `rotatedSixLineMeasureLiftProved`, `g3CapGeometryExportProved`,
  `principalClaimProvedUnconditionally`.
- Lake green. Honest bar still ~80–84%.

# Changelog

## 2026-10-22 — RotatedGridRatCover from PointwiseCover + G3 sep witness

- `RotatedChordMeasure`: `RotatedGridRatCover_of_pointwise`; axis lift; meetsHoriz/Vert; LinePackageExport⇒CoverIneq.
- `G3G4Fragments`: `G3SepWitnessExport`⇒ParallelBudgetExport/exclusion; `ParallelBudgetData.mk'`.
- Docs v0.17. `principalClaimProvedUnconditionally` remains **false**.
- BernsteinExact* / NearEndExact* / LivingLeaf* / Closer* untouched.

## 2026-10-22 — Six-line chord algebra + G3 parallel-budget export

- `RotatedChordMeasure`: `SixLineChordMatrix` / `RotatedChordLinePackage`; axis/identity-C ⇒ CoverIneq.
- `ObliqueChart`: unitDir projected-width ≤2 and sq≤2.
- `G3G4Fragments`: `G3ParallelBudgetExport`⇒exclusion.
- Docs v0.16. `principalClaimProvedUnconditionally` remains **false**.
- BernsteinExact* / NearEndExact* / LivingLeafStrengthen untouched.

## 2026-10-22 — SE(2) pullback transport + chord/G3 package split

- `AxisG5k0FromCover`: `pullback_contains_iff`; body-F∋body-O ↔ world-F∋O; manuscript fHasO ↔ world F∋O (identity-C).
- `RotatedChordMeasure`: diameter bounds held; BoundPackage ↔ CoverIneq; max-proxy ineq impossible.
- `G3G4Fragments`: `BudgetHyp.of`; `G3SideGapDataExport`⇒exclusion.
- Docs v0.15. `principalClaimProvedUnconditionally` remains **false**.
- BernsteinExact* / NearEndExact* untouched.

## 2026-10-22 — Body-chart faithfulness + G3/G4 flag iff (Lean)

- `AxisG5k0FromCover`: `pullback_self`; axis pullback preserves alignment; `translate_axis_to_identity`;
  `bodyChartSquares` / `BodyChartAxisAligned` / world-axis ⇒ body identity-C; manuscript F = body-chart F.
- `G3G4Fragments`: `classify_eq_G3_iff` / `classify_eq_G4_iff`; cover flag extracts.
- Docs: CONTINUATION_LEAN, formalization.yaml v0.14, README, KNOWN_GAPS.
- `principalClaimProvedUnconditionally` remains **false**.
- BernsteinExact* / NearEndExact* untouched (other executor).

## 2026-10-22 — (S)-tier inventory cleared to (E)/(H) (`80e8ee0`)

- Batch24–26f family: **151** checkable Bernstein/IBB/hand certificates under `artifacts/closure/item3_certs/exact_certs_batch24/`.
- Checker `artifacts/closure/scripts/check_exact_certs_batch24.py`: **PASS 151/151**.
- Remaining dual-solver (S) from the post-batch25 set of 91: **0** (`S_tier_inventory.md`, `S_tier_remaining.json`).
- Handoff for Lean Bernstein lifts: `artifacts/closure/CERT_TO_LEAN_HANDOFF.md`.
- Referee pack `KNOWN_GAPS` / `STATUS` (+ zh) updated with honest wording: clearing (S) does **not** prove the theorem; Lean e2e faithfulness and external review stay open.
- **Not claimed:** principal geometric theorem, unconditional Lean claim, or peer review.

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
