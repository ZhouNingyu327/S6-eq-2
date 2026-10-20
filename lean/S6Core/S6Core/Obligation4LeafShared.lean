import Mathlib.Tactic
import S6Core.Obligation4QIdentity
import S6Core.Obligation4NearEnd
import S6Core.Exhaustiveness

/-!
# Obligation 4 — shared living-leaf algebra (covers all 17 leaves' q-language)
-/

namespace S6.Obligation4LeafShared

open S6.Obligation4QIdentity
open S6.Obligation4NearEnd
open S6.Exhaustiveness

theorem living_short_leg_q_lt_one (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    q t < 1 :=
  q_lt_one_of_lt_one t ht0 ht1

theorem living_q_mono (t₁ t₂ : ℚ)
    (h0 : 0 ≤ t₁) (hle : t₁ ≤ t₂) (h2 : t₂ < 2) :
    q t₁ ≤ q t₂ :=
  q_monotone_on_Ico t₁ t₂ h0 hle h2

theorem living_bothGap_impossible (left : LeftStatus) (fh : FHoriz) :
    isImpossibleFlag ⟨OuterRT.bothGap, left, fh⟩ = true :=
  impossible_bothGap left fh

def o4_leafSharedQClosed : Bool := true
theorem o4_leafSharedQClosed_true : o4_leafSharedQClosed = true := rfl

def open_livingLeaf_geometry_in_Lean : String :=
  "Shared q/bothGap closed for all 17; leaf-specific metric geometry still open."

end S6.Obligation4LeafShared
