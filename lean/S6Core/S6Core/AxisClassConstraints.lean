import Mathlib.Tactic
import S6Core.CoveringGeometry
import S6Core.OwnershipBridge
import S6Core.TopClassExhaustiveness
import S6Core.Exhaustiveness

/-!
# Axis-aligned class constraints from pairwise-far outer mids

When `μ > 1`, a single axis unit square owns at most one target outer mid.
Hence for `k = 2` (two outer mids in `C ∪ F`), the two mids cannot both lie
in `C` alone or in `F` alone — they must be split across `C` and `F`.
-/

namespace S6.AxisClassConstraints

open S6.OwnershipBridge
open S6.CoveringGeometry
open S6.TopClassExhaustiveness
open S6.Exhaustiveness

/-- The four outer mids of a `TargetMids`. -/
def outer (T : TargetMids) : List (ℚ × ℚ) := T.outerMids

theorem not_both_in_C_bottom_right (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.C.contains T.midBottom) (hr : cov.C.contains T.midRight) : False :=
  axis_square_not_both_bottom_right T cov.C hμ hb hr

theorem not_both_in_C_bottom_top (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.C.contains T.midBottom) (ht : cov.C.contains T.midTop) : False :=
  axis_square_not_both_bottom_top T cov.C hμ hb ht

theorem not_both_in_F_bottom_right (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.F.contains T.midBottom) (hr : cov.F.contains T.midRight) : False :=
  axis_square_not_both_bottom_right T cov.F hμ hb hr

theorem not_both_in_F_bottom_top (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.F.contains T.midBottom) (ht : cov.F.contains T.midTop) : False :=
  axis_square_not_both_bottom_top T cov.F hμ hb ht

/-- If bottom and right are both owned by `C ∪ F` and μ>1, they cannot both
lie in `C`, nor both in `F`. -/
theorem bottom_right_split_across_CF (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    ( _hbC : cov.C.contains T.midBottom ∨ cov.F.contains T.midBottom)
    ( _hrC : cov.C.contains T.midRight ∨ cov.F.contains T.midRight) :
    ¬ (cov.C.contains T.midBottom ∧ cov.C.contains T.midRight) ∧
      ¬ (cov.F.contains T.midBottom ∧ cov.F.contains T.midRight) := by
  refine ⟨?_, ?_⟩
  · intro ⟨h1, h2⟩; exact not_both_in_C_bottom_right T cov hμ h1 h2
  · intro ⟨h1, h2⟩; exact not_both_in_F_bottom_right T cov hμ h1 h2

/-- G5 axis: fHasO forces G5 (re-export). -/
theorem fHasO_classifies_G5 (T : TargetMids) (cov : Covering)
    (h : (flagsOfTarget T cov).fHasO = true) :
    classify (flagsOfTarget T cov).toOwnership = TopClass.G5 :=
  covering_G5_of_fHasO T cov h

/-- When fHasO is false and k=0, classifier is G1. -/
theorem k0_noF_is_G1 (T : TargetMids) (cov : Covering)
    (hk : (flagsOfTarget T cov).k = ⟨0, by decide⟩)
    (hf : (flagsOfTarget T cov).fHasO = false) :
    classify (flagsOfTarget T cov).toOwnership = TopClass.G1 :=
  classify_G1_of (flagsOfTarget T cov).toOwnership hf hk

end S6.AxisClassConstraints
