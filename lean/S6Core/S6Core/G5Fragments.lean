import Mathlib.Tactic
import S6Core.CoveringGeometry
import S6Core.OwnershipBridge
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.TopClassExhaustiveness
import S6Core.Faithfulness
import S6Core.Exhaustiveness

/-!
# G5 fragments — geometric constraints when `F ∋ O`

Not a full `G5Exclusion`. Proves local impossibilities useful for the G5 branch.
-/

namespace S6.G5Fragments

open S6.Obligation2
open S6.Obligation2Opens
open S6.OwnershipBridge
open S6.CoveringGeometry
open S6.TopClassExhaustiveness
open S6.Exhaustiveness
open S6.Faithfulness

/-- Centre-to-bottom mid distance squared is `μ²`. -/
theorem distSq_centre_bottom (T : Target) :
    distSq (Target.centre T) (midBottom T) = T.μ * T.μ := by
  simp only [distSq, Target.centre, midBottom]; ring

theorem distSq_centre_right (T : Target) :
    distSq (Target.centre T) (midRight T) = T.μ * T.μ := by
  simp only [distSq, Target.centre, midRight]; ring

/-- If `μ² > 2`, no unit square contains both centre and bottom mid. -/
theorem no_square_centre_and_bottom_of_mu_sq (T : Target) (g : RotatedSquare)
    (hμ2 : (2 : ℚ) < T.μ * T.μ)
    (hc : RotatedSquare.contains g (Target.centre T))
    (hb : RotatedSquare.contains g (midBottom T)) : False := by
  have hfar : (2 : ℚ) < distSq (Target.centre T) (midBottom T) := by
    simpa [distSq_centre_bottom] using hμ2
  exact cannot_cover_far g _ _ hfar hc hb

theorem no_square_centre_and_right_of_mu_sq (T : Target) (g : RotatedSquare)
    (hμ2 : (2 : ℚ) < T.μ * T.μ)
    (hc : RotatedSquare.contains g (Target.centre T))
    (hr : RotatedSquare.contains g (midRight T)) : False := by
  have hfar : (2 : ℚ) < distSq (Target.centre T) (midRight T) := by
    simpa [distSq_centre_right] using hμ2
  exact cannot_cover_far g _ _ hfar hc hr

theorem axis_fHasO_is_G5 (T : TargetMids) (cov : Covering)
    (h : (flagsOfTarget T cov).fHasO = true) :
    classify (flagsOfTarget T cov).toOwnership = TopClass.G5 :=
  covering_G5_of_fHasO T cov h

theorem axis_F_not_two_adjacent_mids (T : TargetMids) (cov : Covering)
    (hμ : 1 < T.μ)
    (hb : cov.F.contains T.midBottom) (hr : cov.F.contains T.midRight) : False :=
  axis_square_not_both_bottom_right T cov.F hμ hb hr

theorem faithfulness_g5_sketch :
    classify flags_g5.toOwnership = TopClass.G5 :=
  g5_class

end S6.G5Fragments
