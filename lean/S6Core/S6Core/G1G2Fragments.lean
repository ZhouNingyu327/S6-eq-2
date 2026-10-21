import Mathlib.Tactic
import S6Core.NearEndGeometry
import S6Core.Exhaustiveness
import S6Core.MainTheorem
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.TopClassExhaustiveness
import S6Core.LeafCertificates

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


/-- The 17 living near-end leaves (open geometric goals). -/
theorem seventeen_living_list :
    (allNear.filter livingFlag).length = 17 :=
  count_living

/-- Table-impossible leaves are exactly bothGap (×6) + topGap/gap/pos (×1). -/
theorem impossible_shape (ℓ : NearLeaf) (hi : impossible ℓ) :
    ℓ.rt = OuterRT.bothGap ∨
      (ℓ.rt = OuterRT.topGap ∧ ℓ.left = LeftStatus.gap ∧ ℓ.fh = FHoriz.pos) :=
  (impossible_cases ℓ).1 hi

def g1g2TableFragmentClosed : Bool := true
theorem g1g2TableFragmentClosed_true : g1g2TableFragmentClosed = true := rfl

def g1g2LivingGeometryProved : Bool := false
theorem g1g2LivingGeometryProved_false : g1g2LivingGeometryProved = false := rfl

def openG1G2Bridges : List String :=
  ["G1LivingBridge", "G2cLivingBridge", "G2fLivingBridge",
   "AllLivingLeavesExcluded (17 living)"]


/-- Every bothGap leaf (all left/fh) is LivingLeafExcluded. -/
theorem all_bothGap_excluded :
    ∀ left : LeftStatus, ∀ fh : FHoriz,
      LivingLeafExcluded ⟨OuterRT.bothGap, left, fh⟩ :=
  fun left fh => bothGap_family_excluded left fh

/-- Count: bothGap accounts for multiple of the 7 impossible leaves. -/
def bothGapExcludedFamilyClosed : Bool := true
theorem bothGapExcludedFamilyClosed_true : bothGapExcludedFamilyClosed = true := rfl


open S6.LeafCertificates

/-- Open: each living leaf is geometrically excluded (certificate/geometry). -/
def LivingLeafCertBridge : Prop :=
  ∀ ℓ : NearLeaf, living ℓ → LivingLeafExcluded ℓ

theorem AllLivingLeavesExcluded_of_certBridge (h : LivingLeafCertBridge) :
    AllLivingLeavesExcluded :=
  fun ℓ hl => h ℓ hl hl

/-- Every living leaf has a named closer module (inventory, not a geometry proof). -/
theorem living_has_closer_module (ℓ : NearLeaf) (hl : living ℓ) :
    closerModule ℓ ≠ "IMPOSSIBLE" :=
  livingFlag_has_closer ℓ hl

def livingLeafCertBridgeProved : Bool := false
theorem livingLeafCertBridgeProved_false : livingLeafCertBridgeProved = false := rfl

end S6.G1G2Fragments
