import Mathlib.Tactic
import S6Core.Exhaustiveness

/-!
# Near-end leaf table — combinatorial impossibilities as Props

The 24-leaf near-end table is already machine-checked in `Exhaustiveness`.
This module lifts the impossible flags to named Props used by the main
reduction (not `→ True` stubs).

Geometric realisation of each living leaf remains open / certificate-backed.
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

/-- Open geometric goal for each living leaf (documentation Prop). -/
def LivingLeafExcluded (ℓ : NearLeaf) : Prop :=
  living ℓ → False

/-- Bundle: all 17 living leaves geometrically excluded. -/
def AllLivingLeavesExcluded : Prop :=
  ∀ ℓ : NearLeaf, LivingLeafExcluded ℓ

theorem near_end_closed_of_living_excluded (h : AllLivingLeavesExcluded) :
    ∀ ℓ : NearLeaf, impossible ℓ ∨ ¬ living ℓ := by
  intro ℓ
  rcases near_exhaustive ℓ with hl | hi
  · exact Or.inr (fun hl' => h ℓ hl')
  · exact Or.inl hi

theorem no_living_leaf_of_all_excluded (h : AllLivingLeavesExcluded)
    (ℓ : NearLeaf) (hl : living ℓ) : False :=
  h ℓ hl


/-- Table-impossible leaves are vacuously geometrically excluded. -/
theorem LivingLeafExcluded_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    LivingLeafExcluded ℓ := by
  intro hl
  have : ¬ impossible ℓ := (living_iff_not_impossible ℓ).1 hl
  exact this hi

/-- All seven table-impossible near-end leaves are LivingLeafExcluded. -/
theorem all_impossible_leaves_excluded :
    ∀ ℓ : NearLeaf, impossible ℓ → LivingLeafExcluded ℓ :=
  fun ℓ hi => LivingLeafExcluded_of_impossible ℓ hi

/-- Count: 7 of 24 leaves discharged as LivingLeafExcluded via the table;
17 living leaves remain open geometric goals. -/
def impossibleLeavesExcludedCount : ℕ := 7
theorem impossibleLeavesExcludedCount_eq :
    impossibleLeavesExcludedCount = 7 := rfl

def livingLeavesStillOpenCount : ℕ := 17
theorem livingLeavesStillOpenCount_eq : livingLeavesStillOpenCount = 17 := rfl


/-- Exact characterization of table-impossible near-end leaves. -/
theorem impossible_cases (ℓ : NearLeaf) :
    impossible ℓ ↔
      ℓ.rt = OuterRT.bothGap ∨
        (ℓ.rt = OuterRT.topGap ∧ ℓ.left = LeftStatus.gap ∧ ℓ.fh = FHoriz.pos) := by
  cases ℓ with
  | mk rt left fh =>
    cases rt <;> cases left <;> cases fh <;> simp [impossible, isImpossibleFlag]

/-- All seven table-impossible leaves, listed. -/
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

end S6.NearEndGeometry
