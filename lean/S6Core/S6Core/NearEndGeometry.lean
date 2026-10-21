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

end S6.NearEndGeometry
