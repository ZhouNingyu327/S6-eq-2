import Mathlib.Tactic
import S6Core.CoveringGeometry
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.Faithfulness
import S6Core.TopClassExhaustiveness
import S6Core.ParallelBudget
import S6Core.ParallelBudgetGeometry
import S6Core.Exhaustiveness
import S6Core.NearEndGeometry

/-!
# Principal claim — geometric statement and proved reduction

Manuscript claim (short paper): six unit squares cannot cover a square of
side greater than 2. Equivalently, for every half-side parameter `μ > 1`,
there is no pointwise cover of the target `[0, 2μ]²` by six rigid unit squares.

## What is proved in Lean (this file + imports)

1. The principal claim is stated as a `Prop` (`PrincipalClaim`), not a `Bool`.
2. Any `PointwiseCover` needs five distinct tile indices (4 corners + centre).
3. Any `PointwiseCover` reaches some `TopClass` via `RoleSelection.ofCover`.
4. Outer mids are pairwise farther than √2; no unit square holds two of them.
5. **Conditional closure:** if every `TopClass` is geometrically impossible for
   every cover, then `PrincipalClaim` holds.
6. Parallel-budget *algebra* contradictions (`ParallelBudget`) and `B(d) < 1`
   geometry (`ParallelBudgetGeometry`) are available as lemmas for class work.

## What remains open (named; not silently closed)

* `open_G1_exclusion` … `open_G5_exclusion`: geometric impossibility of each
  top class for an arbitrary cover. The computer-assisted manuscript attacks
  these via certificates; they are **not** fully re-proved in Lean here.
* End-to-end faithfulness of every informal M3.0 covering to `flagsOfTarget*`.

Boolean `flag = true := rfl` elsewhere is status metadata only.
-/

namespace S6.MainTheorem

open S6.Obligation2
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.CoveringGeometry
open S6.TopClassExhaustiveness
open S6.Exhaustiveness
open S6.Faithfulness
open S6.ParallelBudget

/-- **Principal geometric claim** (manuscript main theorem as a `Prop`). -/
def PrincipalClaim : Prop :=
  ∀ (T : Target) (_cov : PointwiseCover T), False

/-- Side length of the target square `[0, 2μ]²`. -/
def targetSide (T : Target) : ℚ := 2 * T.μ

theorem targetSide_gt_two (T : Target) : (2 : ℚ) < targetSide T := by
  simp only [targetSide]; nlinarith [T.hμ]

/-! ## Proved reduction lemmas -/

theorem any_cover_needs_five_roles {T : Target} (cov : PointwiseCover T) :
    let C := cov.toCornerOwners
    let iC := Classical.choose (exists_centre_owner cov)
    C.i1 ≠ C.i2 ∧ C.i1 ≠ C.i3 ∧ C.i1 ≠ C.i4 ∧
      C.i2 ≠ C.i3 ∧ C.i2 ≠ C.i4 ∧ C.i3 ≠ C.i4 ∧
      iC ≠ C.i1 ∧ iC ≠ C.i2 ∧ iC ≠ C.i3 ∧ iC ≠ C.i4 :=
  cover_needs_five_distinct_indices cov

theorem any_cover_is_classified {T : Target} (cov : PointwiseCover T) :
    ∃ tc : TopClass,
      classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership = tc :=
  cover_reaches_topClass cov

/-- Packaged: cover → RoleSelection → TopClass. -/
theorem cover_to_topClass {T : Target} (cov : PointwiseCover T) :
    ∃ (R : RoleSelection T) (tc : TopClass),
      R.cov = cov ∧
        classify R.toManuscript.flags.toOwnership = tc := by
  refine ⟨RoleSelection.ofCover cov, ?_, rfl, ?_⟩
  · exact Classical.choose (cover_reaches_topClass cov)
  · exact Classical.choose_spec (cover_reaches_topClass cov)

/-! ## Open class exclusions (named goals — not proved) -/

/-- Open: every cover classified `G1` is geometrically impossible. -/
def G1Exclusion : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G1 → False

def G2cExclusion : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G2_centerMid → False

def G2fExclusion : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G2_farF → False

def G3Exclusion : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 → False

def G4Exclusion : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G4 → False

def G5Exclusion : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G5 → False

/-- Bundle of all six top-class exclusion hypotheses. -/
structure ClassExclusions where
  g1 : G1Exclusion
  g2c : G2cExclusion
  g2f : G2fExclusion
  g3 : G3Exclusion
  g4 : G4Exclusion
  g5 : G5Exclusion

/-- **Conditional main theorem** (proved): if every TopClass is excluded, the
principal claim holds. This is the honest reduction spine toward an
openai/math-style formalized entry. -/
theorem principal_of_class_exclusions (E : ClassExclusions) : PrincipalClaim := by
  intro T cov
  obtain ⟨tc, htc⟩ := cover_reaches_topClass cov
  cases tc with
  | G1 => exact E.g1 T cov htc
  | G2_centerMid => exact E.g2c T cov htc
  | G2_farF => exact E.g2f T cov htc
  | G3 => exact E.g3 T cov htc
  | G4 => exact E.g4 T cov htc
  | G5 => exact E.g5 T cov htc

/-! ## Partial discharges available today (not full class exclusions) -/

/-- Algebraic side-gap contradiction under `BudgetHyp` (from `ParallelBudget`).
This is a *fragment* used inside G3/near-end arguments, not G3Exclusion itself. -/
theorem sideGap_fragment_impossible (h : BudgetHyp)
    (hp : (12 : ℚ) * h.μ ≤ 8 + 3 * h.B + h.vF) : False :=
  sideGap_covering_impossible h hp

theorem noSideGap_fragment_impossible (μ B : ℚ) (hμ : 1 < μ) (hB : B < 1)
    (hp : (12 : ℚ) * μ ≤ 8 + 2 * B + 2 * μ) : False :=
  noSideGap_covering_impossible μ B hμ hB hp

/-- `B(d) < 1` on both manuscript branches (from `ParallelBudgetGeometry`). -/
theorem B_lt_one_of_data (D : S6.ParallelBudgetGeometry.ParallelBudgetData) :
    D.B < 1 :=
  S6.ParallelBudgetGeometry.ParallelBudgetData.B_lt_one D

/-! ## Near-end reduction fragment -/

open S6.NearEndGeometry

/-- If all 17 living near-end leaves are geometrically excluded, every near-end
leaf is either table-impossible or not living. -/
theorem near_end_of_living_exclusions (h : AllLivingLeavesExcluded) :
    ∀ ℓ : NearLeaf, impossible ℓ ∨ ¬ living ℓ :=
  near_end_closed_of_living_excluded h

/-! ## Status relative to openai/math formalized bar -/

/-- Honest progress flag: reduction spine + geometry lemmas proved;
full `PrincipalClaim` not yet closed without class exclusions. -/
def principalClaimProvedUnconditionally : Bool := false

theorem principalClaimProvedUnconditionally_false :
    principalClaimProvedUnconditionally = false := rfl

def reductionSpineProved : Bool := true
theorem reductionSpineProved_true : reductionSpineProved = true := rfl

def openClassExclusions : List String :=
  [ "G1Exclusion", "G2cExclusion", "G2fExclusion",
    "G3Exclusion", "G4Exclusion", "G5Exclusion" ]

theorem openClassExclusions_length : openClassExclusions.length = 6 := rfl

/-- Documentation anchor: what a follow-up must prove to close the main claim. -/
def pathToUnconditionalClaim : String :=
  "Prove G1Exclusion…G5Exclusion (or a coarser partition), then apply \
   principal_of_class_exclusions. Certificate-backed (E)/(H) leaves and \
   G5 geometry→algebra rebuild are the manuscript route into those Props."

end S6.MainTheorem
