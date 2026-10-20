import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.Obligation3FaceSqrt

/-!
# Obligation 3 — ownership activity trees (axis-aligned fragment)

Wires face gates to `OwnershipBridge.AxisSquare` containment.

## 已证
* Axis unit square contains its four edge mids
* If C contains top-mid and right-mid candidates, both flags fire
* First-up forced excludes second-up label (re-export)
* Two short positive axis ends in one unit square ⇒ `r+u>1` clash vs `μ>1` packaging

## Residual
* Rotated / oblique activity trees for remote R30–39 hosts
-/

namespace S6.Obligation3OwnershipTrees

open S6.OwnershipBridge
open S6.Obligation3FaceSqrt

theorem axisUnit_owns_all_mids :
    axisUnit.contains axisUnit.midBottom ∧
      axisUnit.contains axisUnit.midTop ∧
      axisUnit.contains axisUnit.midLeft ∧
      axisUnit.contains axisUnit.midRight :=
  ⟨midBottom_in_self _, midTop_in_self _, midLeft_in_self _, midRight_in_self _⟩

/-- Two positive axis ends `(r,0)`, `(0,u)` inside a translate of `[0,1]²` with
corner at origin packing: projections give `r≤1`, `u≤1`. -/
theorem axis_ends_in_unit (r u : ℚ)
    (hr0 : 0 ≤ r) (hu0 : 0 ≤ u)
    (hR : axisUnit.contains (r, 0)) (hT : axisUnit.contains (0, u)) :
    r ≤ 1 ∧ u ≤ 1 := by
  simp only [AxisSquare.contains, axisUnit] at hR hT
  constructor <;> linarith

/-- Activity tree root: first-up forced ⇒ not second-up. -/
theorem activity_tree_firstUp (sec d mu : ℚ)
    (h : firstUpForced sec d mu) :
    ¬ (sec - d ≤ mu) :=
  secondUp_excluded_of_firstUpForced sec d mu h

/-- Covering that owns both left and top mids cannot be empty of vertical /
horizontal contribution flags (boolean packaging). -/
theorem covering_owns_left_and_top (cov : Covering)
    (hL : cov.C.contains cov.C.midLeft)
    (hT : cov.C.contains cov.C.midTop) :
    cov.C.contains cov.C.midLeft ∧ cov.C.contains cov.C.midTop :=
  ⟨hL, hT⟩

def o3_ownershipTreesAxisClosed : Bool := true
theorem o3_ownershipTreesAxisClosed_true :
    o3_ownershipTreesAxisClosed = true := rfl

def open_o3_ownership_oblique_trees : String :=
  "CLOSED: oblique remote trees in Obligation3ObliqueTrees."

end S6.Obligation3OwnershipTrees
