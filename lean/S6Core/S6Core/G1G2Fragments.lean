import Mathlib.Tactic
import S6Core.NearEndGeometry
import S6Core.Exhaustiveness
import S6Core.MainTheorem
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.TopClassExhaustiveness

/-!
# G1/G2 near-end fragments

* 7 table-impossible leaves ⇒ `LivingLeafExcluded` (proved).
* Conditional: `AllLivingLeavesExcluded` ⇒ near-end closed; G1/G2 exclusions
  still need living-leaf geometry / certificates for the 17 living leaves.
-/

namespace S6.G1G2Fragments

open S6.NearEndGeometry
open S6.Exhaustiveness
open S6.MainTheorem
open S6.TopClassExhaustiveness

theorem seven_impossible_excluded :
    ∀ ℓ : NearLeaf, impossible ℓ → LivingLeafExcluded ℓ :=
  all_impossible_leaves_excluded

/-- Count check from the near-end table. -/
theorem near_end_counts :
    impossibleLeavesExcludedCount = 7 ∧ livingLeavesStillOpenCount = 17 :=
  ⟨impossibleLeavesExcludedCount_eq, livingLeavesStillOpenCount_eq⟩

/-- Named bothGap family is table-impossible for every left/fh. -/
theorem bothGap_family_excluded (left : LeftStatus) (fh : FHoriz) :
    LivingLeafExcluded ⟨OuterRT.bothGap, left, fh⟩ :=
  LivingLeafExcluded_of_impossible _ (bothGap_impossible left fh)

theorem topGap_leftGap_pos_excluded :
    LivingLeafExcluded ⟨OuterRT.topGap, LeftStatus.gap, FHoriz.pos⟩ :=
  LivingLeafExcluded_of_impossible _ topGap_leftGap_pos_impossible

/-- If all living leaves are excluded, near-end reduction closes. -/
theorem near_end_closed_of_all_living (h : AllLivingLeavesExcluded) :
    ∀ ℓ : NearLeaf, impossible ℓ ∨ ¬ living ℓ :=
  near_end_closed_of_living_excluded h

/-- Open bridges: G1 / G2c / G2f covers realise a discharged living leaf. -/
def G1LivingBridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G1 → False

def G2cLivingBridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G2_centerMid → False

def G2fLivingBridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G2_farF → False

theorem G1Exclusion_of_bridge (h : G1LivingBridge) : G1Exclusion := h
theorem G2cExclusion_of_bridge (h : G2cLivingBridge) : G2cExclusion := h
theorem G2fExclusion_of_bridge (h : G2fLivingBridge) : G2fExclusion := h

def g1g2TableFragmentClosed : Bool := true
theorem g1g2TableFragmentClosed_true : g1g2TableFragmentClosed = true := rfl

def g1g2LivingGeometryProved : Bool := false
theorem g1g2LivingGeometryProved_false : g1g2LivingGeometryProved = false := rfl

def openG1G2Bridges : List String :=
  ["G1LivingBridge", "G2cLivingBridge", "G2fLivingBridge",
   "AllLivingLeavesExcluded (17 living)"]

end S6.G1G2Fragments
