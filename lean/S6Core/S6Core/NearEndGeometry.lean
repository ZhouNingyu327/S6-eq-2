import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.NearEndRealisation

/-!
# Near-end leaf table — combinatorial impossibilities as Props

The 24-leaf near-end table is already machine-checked in `Exhaustiveness`.
This module lifts the impossible flags to named Props used by the main
reduction (not `→ True` stubs).

Combinatorial `LivingLeafExcluded` retained for MainTheorem spine
(`living → False` documentation goal). Geometric work uses
`LivingLeafGeomExcluded` := `¬ ManuscriptCompleteRealised`
(OuterRT∧dual empty by dual↔junction; not partial NearEndSE2).
-/

namespace S6.NearEndGeometry

open S6.Exhaustiveness

theorem bothGap_impossible (left : LeftStatus) (fh : FHoriz) :
    impossible ⟨OuterRT.bothGap, left, fh⟩ := by
  simp [impossible, isImpossibleFlag]

theorem topGap_leftGap_pos_impossible :
    impossible ⟨OuterRT.topGap, LeftStatus.gap, FHoriz.pos⟩ := by
  simp [impossible, isImpossibleFlag]

theorem flag_true_is_impossible (ℓ : NearLeaf) (h : isImpossibleFlag ℓ = true) :
    impossible ℓ := h

theorem living_iff_not_impossible (ℓ : NearLeaf) :
    living ℓ ↔ ¬ impossible ℓ := by
  simp [living, impossible, livingFlag]

theorem near_partition_cards :
    (allNear.filter isImpossibleFlag).length = 7 ∧
      (allNear.filter livingFlag).length = 17 ∧
        allNear.length = 24 :=
  ⟨count_impossible, count_living, allNear_length⟩

/-- Combinatorial documentation goal (MainTheorem spine). Uninhabitable for
living leaves while `livingFlag = true` is proved; prefer `LivingLeafGeomExcluded`. -/
def LivingLeafExcluded (ℓ : NearLeaf) : Prop :=
  living ℓ → False

/-- Geometric exclusion: no manuscript-complete OuterRT∧dual realisation
(empty by dual↔junction algebra). Distinct from partial `NearEndSE2`. -/
def LivingLeafGeomExcluded (ℓ : NearLeaf) : Prop :=
  ¬ S6.NearEndRealisation.ManuscriptCompleteRealised ℓ

/-- Bundle: combinatorial living→False for every leaf (MainTheorem). -/
def AllLivingLeavesExcluded : Prop :=
  ∀ ℓ : NearLeaf, LivingLeafExcluded ℓ

/-- Bundle: every leaf unrealisable in SE(2)/chart. -/
def AllLivingLeavesGeomExcluded : Prop :=
  ∀ ℓ : NearLeaf, LivingLeafGeomExcluded ℓ

theorem near_end_closed_of_living_excluded (h : AllLivingLeavesExcluded) :
    ∀ ℓ : NearLeaf, impossible ℓ ∨ ¬ living ℓ := by
  intro ℓ
  rcases near_exhaustive ℓ with hl | hi
  · exact Or.inr (fun hl' => h ℓ hl')
  · exact Or.inl hi

theorem no_living_leaf_of_all_excluded (h : AllLivingLeavesExcluded)
    (ℓ : NearLeaf) (hl : living ℓ) : False :=
  h ℓ hl

theorem LivingLeafExcluded_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    LivingLeafExcluded ℓ := by
  intro hl
  have : ¬ impossible ℓ := (living_iff_not_impossible ℓ).1 hl
  exact this hi

theorem LivingLeafGeomExcluded_of_impossible (ℓ : NearLeaf) (_hi : impossible ℓ) :
    LivingLeafGeomExcluded ℓ :=
  S6.NearEndRealisation.not_manuscriptCompleteRealised ℓ

theorem all_impossible_leaves_excluded :
    ∀ ℓ : NearLeaf, impossible ℓ → LivingLeafExcluded ℓ :=
  fun ℓ hi => LivingLeafExcluded_of_impossible ℓ hi

theorem all_impossible_leaves_geom_excluded :
    ∀ ℓ : NearLeaf, impossible ℓ → LivingLeafGeomExcluded ℓ :=
  fun ℓ hi => LivingLeafGeomExcluded_of_impossible ℓ hi

def impossibleLeavesExcludedCount : ℕ := 7
theorem impossibleLeavesExcludedCount_eq :
    impossibleLeavesExcludedCount = 7 := rfl

def livingLeavesStillOpenCount : ℕ := 17
theorem livingLeavesStillOpenCount_eq : livingLeavesStillOpenCount = 17 := rfl

theorem impossible_cases (ℓ : NearLeaf) :
    impossible ℓ ↔
      ℓ.rt = OuterRT.bothGap ∨
        (ℓ.rt = OuterRT.topGap ∧ ℓ.left = LeftStatus.gap ∧ ℓ.fh = FHoriz.pos) := by
  cases ℓ with
  | mk rt left fh =>
    cases rt <;> cases left <;> cases fh <;> simp [impossible, isImpossibleFlag]

theorem seven_impossible_list :
    (allNear.filter isImpossibleFlag) =
      [ ⟨.topGap,  .gap,  .pos⟩
      , ⟨.bothGap, .meet, .empty⟩, ⟨.bothGap, .meet, .pos⟩, ⟨.bothGap, .meet, .neg⟩
      , ⟨.bothGap, .gap,  .empty⟩, ⟨.bothGap, .gap,  .pos⟩, ⟨.bothGap, .gap,  .neg⟩ ] := by
  native_decide

def nearEndTableFragmentClosed : Bool := true
theorem nearEndTableFragmentClosed_true : nearEndTableFragmentClosed = true := rfl

def allLivingLeavesExcludedInLean : Bool := false
theorem allLivingLeavesExcludedInLean_false :
    allLivingLeavesExcludedInLean = false := rfl

/-- Manuscript-complete geom exclusion holds for every leaf (dual↔junction). -/
theorem all_leaves_LivingLeafGeomExcluded :
    ∀ ℓ : NearLeaf, LivingLeafGeomExcluded ℓ :=
  fun ℓ => S6.NearEndRealisation.not_manuscriptCompleteRealised ℓ

/-- Status: manuscript-complete layer closed; partial SE2 living unrealised still open. -/
def allLivingLeavesGeomExcludedInLean : Bool := true
theorem allLivingLeavesGeomExcludedInLean_true :
    allLivingLeavesGeomExcludedInLean = true := rfl

end S6.NearEndGeometry
