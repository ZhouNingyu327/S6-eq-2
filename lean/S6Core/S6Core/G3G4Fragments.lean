import Mathlib.Tactic
import S6Core.AxisClassConstraints
import S6Core.CoveringGeometry
import S6Core.M7_1Geometry
import S6Core.MainTheorem
import S6Core.OwnershipBridge
open S6.TopClassExhaustiveness
open S6.Exhaustiveness

/-!
# G3/G4 fragments — mid-split + M7.1 interface

* Axis `k=2` forces C/F mid split (`AxisClassConstraints`).
* M7.1 far-end / topGap checker equivalences already in `M7_1Geometry`.
* Conditional `G3Exclusion` / `G4Exclusion` from named bridges.
-/

namespace S6.G3G4Fragments

open S6.AxisClassConstraints
open S6.CoveringGeometry
open S6.M7_1Geometry
open S6.MainTheorem
open S6.OwnershipBridge

/-- k=2 + bottom/right owned ⇒ cannot both sit in C (axis). -/
theorem k2_bottom_right_not_both_C (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.C.contains T.midBottom) (hr : cov.C.contains T.midRight) : False :=
  not_both_in_C_bottom_right T cov hμ hb hr

theorem k2_bottom_right_not_both_F (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.F.contains T.midBottom) (hr : cov.F.contains T.midRight) : False :=
  not_both_in_F_bottom_right T cov hμ hb hr

/-- G3 = k=2, not adjacent; G4 = k=2, adjacent (classifier). -/
theorem classify_G3_of_k2_not_adj (o : Ownership)
    (hf : o.fHasO = false) (hk : o.k = ⟨2, by decide⟩) (ha : o.midsAdjacent = false) :
    classify o = TopClass.G3 :=
  classify_G3_of o hf hk ha

theorem classify_G4_of_k2_adj (o : Ownership)
    (hf : o.fHasO = false) (hk : o.k = ⟨2, by decide⟩) (ha : o.midsAdjacent = true) :
    classify o = TopClass.G4 :=
  classify_G4_of o hf hk ha

/-- M7.1 topGap narrative ↔ checker (already proved; re-export). -/
theorem m71_topGap_equiv (n : NarrativeTopGap) (hw : NarrativeTopGap.wellFormed n) :
    CheckerTopGapPre.valid n.remaining.toChecker ∧
      CheckerTopGapPre.toOuter n.remaining.toChecker = n.remaining :=
  topGap_narrative_iff_checker n hw

/-- Open bridges: G3/G4 covers realise a discharged M7.1 / budget leaf. -/
def G3Bridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 → False

def G4Bridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G4 → False

/-- If the G3/G4 bridges are the exclusions themselves (identity packaging). -/
theorem G3Exclusion_of_bridge (h : G3Bridge) : G3Exclusion := h
theorem G4Exclusion_of_bridge (h : G4Bridge) : G4Exclusion := h

/-- Far-end host validity (M7.1 entry). -/
theorem farEnd_default_valid : FarEndHosts.valid {} := FarEndHosts.default_valid

def g3g4MidSplitClosed : Bool := true
theorem g3g4MidSplitClosed_true : g3g4MidSplitClosed = true := rfl

def g3g4BridgesProvedInLean : Bool := false
theorem g3g4BridgesProvedInLean_false : g3g4BridgesProvedInLean = false := rfl

end S6.G3G4Fragments
