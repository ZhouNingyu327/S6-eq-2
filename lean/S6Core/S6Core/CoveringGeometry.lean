import Mathlib.Tactic
import S6Core.Obligation2
import S6Core.Obligation2Norm
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.OwnershipBridge
import S6Core.Faithfulness
import S6Core.TopClassExhaustiveness

/-!
# Covering geometry — pairwise-far outer mids (μ > 1)

Machine-checked geometric lemmas (not Boolean metadata):

* Any two distinct target outer mids satisfy `distSq > 2`.
* Hence no rigid unit square contains two distinct outer mids.
* Any `PointwiseCover` needs four pairwise-distinct corner owners and a
  fifth centre owner distinct from them.
* Every such cover reaches some `TopClass` via `RoleSelection.ofCover`.
-/

namespace S6.CoveringGeometry

open S6.Obligation2
open S6.Obligation2Norm
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.OwnershipBridge
open S6.TopClassExhaustiveness
open S6.Exhaustiveness
open S6.Faithfulness

abbrev QPt := ℚ × ℚ

/-! ## Named outer mids of `Target` -/

def midBottom (T : Target) : QPt := (T.μ, 0)
def midRight (T : Target) : QPt := (2 * T.μ, T.μ)
def midTop (T : Target) : QPt := (T.μ, 2 * T.μ)
def midLeft (T : Target) : QPt := (0, T.μ)

theorem midBottom_in_target (T : Target) : inTarget T (midBottom T) := by
  simp only [inTarget, midBottom]
  refine ⟨by nlinarith [T.hμ], by nlinarith [T.hμ], by norm_num, by nlinarith [T.hμ]⟩

theorem midRight_in_target (T : Target) : inTarget T (midRight T) := by
  simp only [inTarget, midRight]
  exact ⟨by nlinarith [T.hμ], le_rfl, by nlinarith [T.hμ], by nlinarith [T.hμ]⟩

theorem midTop_in_target (T : Target) : inTarget T (midTop T) := by
  simp only [inTarget, midTop]
  exact ⟨by nlinarith [T.hμ], by nlinarith [T.hμ], by nlinarith [T.hμ], le_rfl⟩

theorem midLeft_in_target (T : Target) : inTarget T (midLeft T) := by
  simp only [inTarget, midLeft]
  exact ⟨by norm_num, by nlinarith [T.hμ], by nlinarith [T.hμ], by nlinarith [T.hμ]⟩

/-! ## Pairwise `distSq > 2` -/

theorem distSq_bottom_right (T : Target) :
    (2 : ℚ) < distSq (midBottom T) (midRight T) := by
  simp only [distSq, midBottom, midRight]; nlinarith [T.hμ]

theorem distSq_bottom_top (T : Target) :
    (2 : ℚ) < distSq (midBottom T) (midTop T) := by
  simp only [distSq, midBottom, midTop]; nlinarith [T.hμ]

theorem distSq_bottom_left (T : Target) :
    (2 : ℚ) < distSq (midBottom T) (midLeft T) := by
  simp only [distSq, midBottom, midLeft]; nlinarith [T.hμ]

theorem distSq_right_top (T : Target) :
    (2 : ℚ) < distSq (midRight T) (midTop T) := by
  simp only [distSq, midRight, midTop]; nlinarith [T.hμ]

theorem distSq_right_left (T : Target) :
    (2 : ℚ) < distSq (midRight T) (midLeft T) := by
  simp only [distSq, midRight, midLeft]; nlinarith [T.hμ]

theorem distSq_top_left (T : Target) :
    (2 : ℚ) < distSq (midTop T) (midLeft T) := by
  simp only [distSq, midTop, midLeft]; nlinarith [T.hμ]

/-- No rigid unit square contains two distinct named outer mids. -/
theorem no_unit_square_two_named_mids (T : Target) (g : RotatedSquare) :
    ¬ (RotatedSquare.contains g (midBottom T) ∧
        RotatedSquare.contains g (midRight T)) ∧
    ¬ (RotatedSquare.contains g (midBottom T) ∧
        RotatedSquare.contains g (midTop T)) ∧
    ¬ (RotatedSquare.contains g (midBottom T) ∧
        RotatedSquare.contains g (midLeft T)) ∧
    ¬ (RotatedSquare.contains g (midRight T) ∧
        RotatedSquare.contains g (midTop T)) ∧
    ¬ (RotatedSquare.contains g (midRight T) ∧
        RotatedSquare.contains g (midLeft T)) ∧
    ¬ (RotatedSquare.contains g (midTop T) ∧
        RotatedSquare.contains g (midLeft T)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨h1, h2⟩; exact cannot_cover_far g _ _ (distSq_bottom_right T) h1 h2
  · intro ⟨h1, h2⟩; exact cannot_cover_far g _ _ (distSq_bottom_top T) h1 h2
  · intro ⟨h1, h2⟩; exact cannot_cover_far g _ _ (distSq_bottom_left T) h1 h2
  · intro ⟨h1, h2⟩; exact cannot_cover_far g _ _ (distSq_right_top T) h1 h2
  · intro ⟨h1, h2⟩; exact cannot_cover_far g _ _ (distSq_right_left T) h1 h2
  · intro ⟨h1, h2⟩; exact cannot_cover_far g _ _ (distSq_top_left T) h1 h2

/-! ## Five distinct roles -/

/-- Any pointwise cover forces four pairwise-distinct corner owners and a
fifth centre owner distinct from all four. -/
theorem cover_needs_five_distinct_indices {T : Target} (cov : PointwiseCover T) :
    let C := cov.toCornerOwners
    let iC := Classical.choose (exists_centre_owner cov)
    C.i1 ≠ C.i2 ∧ C.i1 ≠ C.i3 ∧ C.i1 ≠ C.i4 ∧
      C.i2 ≠ C.i3 ∧ C.i2 ≠ C.i4 ∧ C.i3 ≠ C.i4 ∧
      iC ≠ C.i1 ∧ iC ≠ C.i2 ∧ iC ≠ C.i3 ∧ iC ≠ C.i4 := by
  intro C iC
  have hpd := owners_pairwise_distinct T C
  have hcen : RotatedSquare.contains (cov.squares iC) (Target.centre T) :=
    Classical.choose_spec (exists_centre_owner cov)
  have hsq : C.squares = cov.squares := PointwiseCover_owners_squares cov
  have hcenO : RotatedSquare.contains (C.squares iC) (Target.centre T) := by
    simpa [hsq] using hcen
  have hne := centre_owner_ne_all_corners T C iC hcenO
  exact ⟨hpd.1, hpd.2.1, hpd.2.2.1, hpd.2.2.2.1, hpd.2.2.2.2.1, hpd.2.2.2.2.2,
    hne.1, hne.2.1, hne.2.2.1, hne.2.2.2⟩

theorem cover_reaches_topClass {T : Target} (cov : PointwiseCover T) :
    ∃ tc : TopClass,
      classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership = tc :=
  ofCover_reaches_topClass cov

/-! ## Axis-aligned: bottom+right mids cannot share one axis square when μ>1 -/

theorem axis_square_not_both_bottom_right (T : TargetMids) (s : AxisSquare)
    (hμ : 1 < T.μ)
    (hb : s.contains T.midBottom) (hr : s.contains T.midRight) : False := by
  have hx : |T.midBottom.1 - T.midRight.1| ≤ (1 : ℚ) := by
    simp only [TargetMids.midBottom, TargetMids.midRight, AxisSquare.contains] at hb hr
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hy : |T.midBottom.2 - T.midRight.2| ≤ (1 : ℚ) := by
    simp only [TargetMids.midBottom, TargetMids.midRight, AxisSquare.contains] at hb hr
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hx2 := abs_le_one_sq (T.midBottom.1 - T.midRight.1) hx
  have hy2 := abs_le_one_sq (T.midBottom.2 - T.midRight.2) hy
  have hfar : (2 : ℚ) <
      (T.midBottom.1 - T.midRight.1) * (T.midBottom.1 - T.midRight.1) +
        (T.midBottom.2 - T.midRight.2) * (T.midBottom.2 - T.midRight.2) := by
    simp only [TargetMids.midBottom, TargetMids.midRight]; nlinarith [hμ]
  nlinarith

theorem axis_square_not_both_bottom_top (T : TargetMids) (s : AxisSquare)
    (hμ : 1 < T.μ)
    (hb : s.contains T.midBottom) (ht : s.contains T.midTop) : False := by
  have hx : |T.midBottom.1 - T.midTop.1| ≤ (1 : ℚ) := by
    simp only [TargetMids.midBottom, TargetMids.midTop, AxisSquare.contains] at hb ht
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hy : |T.midBottom.2 - T.midTop.2| ≤ (1 : ℚ) := by
    simp only [TargetMids.midBottom, TargetMids.midTop, AxisSquare.contains] at hb ht
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hx2 := abs_le_one_sq (T.midBottom.1 - T.midTop.1) hx
  have hy2 := abs_le_one_sq (T.midBottom.2 - T.midTop.2) hy
  have hfar : (2 : ℚ) <
      (T.midBottom.1 - T.midTop.1) * (T.midBottom.1 - T.midTop.1) +
        (T.midBottom.2 - T.midTop.2) * (T.midBottom.2 - T.midTop.2) := by
    simp only [TargetMids.midBottom, TargetMids.midTop]; nlinarith [hμ]
  nlinarith

end S6.CoveringGeometry
