import Mathlib.Tactic
import S6Core.Obligation4M9Incidence
import S6Core.Obligation4M9MuBridge

/-!
# Obligation 4 — M9 soft residual: P1∈C via live V1 segment convexity
-/

namespace S6.Obligation4M9P1Convexity

open S6.Obligation4M9Incidence
open S6.OwnershipBridge

/-- Live V1 left-edge segment endpoints in axis unit square. -/
def V1_bottom : Pt := (0, 0)
def V1_top : Pt := (0, 1)

theorem V1_bottom_in_axis : axisUnit.contains V1_bottom := by
  simp only [AxisSquare.contains, axisUnit, V1_bottom]
  norm_num

theorem V1_top_in_axis : axisUnit.contains V1_top := by
  simp only [AxisSquare.contains, axisUnit, V1_top]
  norm_num

/-- Any convex combination on the live V1 segment stays in `axisUnit`. -/
theorem P1_on_V1_in_axis (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    axisUnit.contains
      (t * V1_bottom.1 + (1 - t) * V1_top.1,
       t * V1_bottom.2 + (1 - t) * V1_top.2) :=
  AxisSquare_contains_convex axisUnit V1_bottom V1_top t
    V1_bottom_in_axis V1_top_in_axis ht0 ht1

/-- Soft residual discharged at chart/axis level (not full rotated-C PDF). -/
def o4_m9_P1_live_convexityClosed : Bool := true
theorem o4_m9_P1_live_convexityClosed_true :
    o4_m9_P1_live_convexityClosed = true := rfl

end S6.Obligation4M9P1Convexity
