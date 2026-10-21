# Lean formalizations

Lean 4 library (`S6Core/`) accompanying the manuscript in this repository.

## Principal claim (Prop, not Bool)

`S6.MainTheorem.PrincipalClaim` states the geometric main theorem as a `Prop`:

> for every target half-side `μ > 1`, there is no pointwise cover of `[0, 2μ]²`
> by six rigid unit squares.

Boolean flags such as `wholeTheorem_S6_eq_2_closed` remain **human-maintained
status metadata** only. Theorems of the form `flag = true := rfl` are not
geometric proofs.

## Proved vs open (openai/math-style honesty)

| Item | Status |
| --- | --- |
| `PrincipalClaim` stated as `Prop` | Yes (`MainTheorem.lean`) |
| Cover → 5 distinct roles (4 corners + centre) | **Proved** (`CoveringGeometry`) |
| Outer mids pairwise `distSq > 2`; no unit square holds two | **Proved** |
| Cover → `RoleSelection` → some `TopClass` | **Proved** |
| `principal_of_class_exclusions` (conditional main theorem) | **Proved** |
| Near-end 7 impossible / 17 living table as Props | **Proved** (`NearEndGeometry`) |
| 7 impossible leaves ⇒ `LivingLeafExcluded` | **Proved**; 17 living **open** |
| Parallel-budget algebra + `B(d) < 1` fragments | **Proved** (existing modules) |
| Axis `k=2` mids cannot both sit in C (or both in F) | **Proved** (`AxisClassConstraints`) |
| `d+B(d)<2`; R2 grid hyp ⇒ False | **Proved** (`G5Budget`) |
| Axis grid contrib (SW outer=2, corners≤8 package) | **Proved** (`AxisGridContribution`) |
| Axis six-line cover ⇒ ∑ contrib ≥ 12μ | **Proved** (`AxisGridCover` / Lebesgue) |
| `Icc_subset_of_closed_of_rats` (closed+ℚ⇒Icc) | **Proved** |
| ℚ six-line cover → `AxisGridLineCover` | **Proved** (`AxisGridCover`) |
| Axis G5k0 under outer₄+mid₂ packing | **Proved conditional** |
| Packing ∑=outer₄+mid₂ from OnlyOwners/OnlyFillers | **Proved** |
| OnlyOwners/OnlyFillers from `AxisG5k0Roles` (corners+interior) | **Proved** |
| Axis pointwise⇒`AxisGridRatCover`/`AxisG5k0Roles` (centre fillers) | **Proved** (`AxisG5k0FromCover`) |
| `AxisAlignedG5k0Realisation`⇒`AxisG5k0CoverBridge` | **Proved conditional** |
| `isG5Class`↔`fHasO`; identity-C⇒world F∋O | **Proved** |
| `AxisAlignedIdentityCRealisation`⇒G5k0 bridges/exports | **Proved conditional** |
| `pullback_self`; body-chart C=`identityPose`; axis translate→identity | **Proved** |
| SE(2) `pullback_contains_iff`; body-F∋body-O ↔ world-F∋O | **Proved** |
| Manuscript fHasO ↔ world F∋O (identity-C) | **Proved** |
| `RotatedChordDiameterBounds` held; package ↔ `CoverIneq` | **Proved** |
| Six-line chord matrix algebra; unitDir projected-width ≤2 | **Proved** |
| `RotatedGridRatCover` from every `PointwiseCover` (no axis hyp) | **Proved** |
| Axis rat cover via rotated + alignment; `meetsHoriz`/`meetsVert` | **Proved** |
| `RotatedChordLinePackageExport`⇒CoverIneq; `G3SepWitnessExport`⇒exclusion | **Proved conditional** |
| horiz/vert chord Δ²≤2, `|Δ|≤2`; `RotatedLineChordCover` algebra | **Proved** |
| `RotatedSixLineMeasureLift`⇒CoverIneq/G5k0Bridge/GeomExport | **Proved conditional** |
| `G3CapGeometryExport`⇒ParallelBudget/SepWitness/exclusion | **Proved conditional** |
| Corner diameter-miss (4 corners vs opposite outers) on any cover | **Proved** |
| Onesided axial sum ≤2; `ChordMatrixExport`⇒SixLineMeasureLift | **Proved conditional** |
| `AxisG5k0CoverBridge`/`Realisation` ⇒ `RotatedChordMatrixExport` | **Proved conditional** |
| Roles ⇒ per-square `axisGridContrib ≤ 2`; axis bottom LineChordCover | **Proved** |
| Real `containsR`/Inf-Sup chords; `RotatedLineMeasureLift` from any rat cover | **Proved** |
| `|Δx|/|Δy|≤|c|+|s|`; parallel miss; `RotatedSixLineRealLift` (six lines) | **Proved** |
| `distSq` on `containsR`; four-corner clamped outer pairs ≤2 | **Proved** |
| Corner mid-miss when `μ²>2`; outer+mid pack skeleton | **Proved** |
| Centre outer-miss (`μ²>2`); four-corner projWidth mid-miss (`|c|+|s|<μ`) | **Proved** |
| Four-corner `clampedSquareTotal ≤2` under projWidth | **Proved** |
| μ²>2 auto corner pack; centre outer clamped=0; chord ≤ projWidth | **Proved** |
| Same-dir ⇒ body-chart axis-aligned + C=`identityPose` | **Proved** |
| Filler mid ≤2; general `ChordMatrixExport`; full BodyChartAxis / IdentityC | **Open** |
| Inhabit `RotatedSixLineMeasureLift` from `RotatedGridRatCover` | **Open** |
| Axis/identity-C realisation ⇒ `RotatedChordCoverIneq` | **Proved conditional** |
| `G3ParallelBudgetExport`⇒`G3SideGapDataExport`/exclusion | **Proved conditional** |
| `G3SideGapDataExport`⇒bridge/exclusion; `BudgetHyp.of` | **Proved conditional** |
| World-axis ⇒ `BodyChartAxisAligned` + body identity-C | **Proved** |
| `BodyChartAxisG5k0Realisation` of axis/identity-C realisation | **Proved conditional** |
| Discharge identity-C / body-chart-axis for every G5 k=0 cover | **Open** |
| `classify_eq_G3_iff` / `classify_eq_G4_iff` (+ cover flag extracts) | **Proved** |
| Interior ⇒ outer contrib 0 | **Proved** |
| `G5k*GeomExport ⇒ Bridge ⇒ G5Exclusion` composition | **Proved** (`G5GeometryBridge`) |
| `G5Exclusion` from three geometric bridges | **Proved conditional** |
| `RotatedG5k0ChordExport` ⇒ `G5k*GeomExport`/`Bridge` | **Proved conditional** |
| `RotatedChordBoundPackage`⇒`RotatedG5k0ChordExport` | **Proved conditional** |
| Inhabit chord bound package from PointwiseCover | **Open** |
| G3/G4 mid-split + M7.1 interface | **Proved fragments** (`G3G4Fragments`) |
| G3/G4 budget-bridge ⇒ exclusion | **Proved conditional**; realisation **open** |
| `g2_alg t < 2` on `(0,1/2)`; E-tier coeff nonneg | **Proved** (`BernsteinGridLift`) |
| `RoleSelection.hF_ne_corners` (sixth tile ≠ corners) | **Proved** |
| `G1Exclusion` … `G5Exclusion` | **Open** (named Props) |
| Unconditional `PrincipalClaim` | **Open** (`principalClaimProvedUnconditionally = false`) |
| End-to-end manuscript faithfulness | **Open** |
| Peer review / human mastery of every step | **Not claimed** |

To close the openai/math formalized-result bar unconditionally: prove the six
`G*Exclusion` Props (or a coarser partition), then apply
`principal_of_class_exclusions`.

## Build

```bash
cd lean/S6Core
lake build  # fetches mathlib; may take a long time
```

A successful build checks the statements above that are marked Proved.
