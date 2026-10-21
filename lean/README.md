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
| Packing `∑≤outer₄+mid₂` from roles | **Open** |
| `G5k*GeomExport ⇒ Bridge ⇒ G5Exclusion` composition | **Proved** (`G5GeometryBridge`) |
| `G5Exclusion` from three geometric bridges | **Proved conditional** |
| G5 geom exports from rotated `PointwiseCover` | **Open** (`G5k*GeomExport`) |
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
