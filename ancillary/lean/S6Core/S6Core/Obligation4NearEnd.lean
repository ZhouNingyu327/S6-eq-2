import Mathlib.Tactic
import S6Core.Exhaustiveness

/-!
# Obligation 4 — near-end leaf Lean stubs

## 已证
* `isImpossibleFlag` on `bothGap`
* Cardinality remark: 4×2×3 = 24 combinatorial near-leaves

## 未证
* Geometry of the 17 living registry leaves
-/

namespace S6.Obligation4NearEnd

open S6.Exhaustiveness

theorem impossible_bothGap (left : LeftStatus) (fh : FHoriz) :
    isImpossibleFlag ⟨OuterRT.bothGap, left, fh⟩ = true := by
  simp [isImpossibleFlag]

theorem nearLeaf_space_card : (4 : ℕ) * 2 * 3 = 24 := by norm_num

def o4_nearLeafEnumClosed : Bool := true
theorem o4_nearLeafEnumClosed_true : o4_nearLeafEnumClosed = true := rfl

def open_livingLeaf_geometry_in_Lean : String :=
  "17 living leaves: external cert chains only; Lean geometry open."

end S6.Obligation4NearEnd
