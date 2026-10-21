import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.NearEndGeometry
import S6Core.LivingLeafCertDischarge

/-!
# LivingLeafGeomExcluded via OuterRT junction (no cert_open)

Discharges full `LivingLeafGeomExcluded` for priority closers R14 / R17 / R27–R28
using SE(2) OuterRT junction residuals — **not** `LeafCloserCertDischarged`.
Remaining closers R13/R16/R18/R19/R26 open. Combinatorial `LivingLeafExcluded`
untouched. Not PrincipalClaim.
-/

namespace S6.LivingLeafGeomDischarge

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.NearEndGeometry
open S6.LivingLeafCertDischarge

def leaf_R14 : NearLeaf := ⟨.bothMeet, .gap, .empty⟩
def leaf_R17 : NearLeaf := ⟨.bothMeet, .gap, .neg⟩
def leaf_R27_meet_empty : NearLeaf := ⟨.rightGap, .meet, .empty⟩
def leaf_R27_meet_pos : NearLeaf := ⟨.rightGap, .meet, .pos⟩
def leaf_R27_meet_neg : NearLeaf := ⟨.rightGap, .meet, .neg⟩
def leaf_R27_gap_empty : NearLeaf := ⟨.rightGap, .gap, .empty⟩
def leaf_R27_gap_pos : NearLeaf := ⟨.rightGap, .gap, .pos⟩
def leaf_R27_gap_neg : NearLeaf := ⟨.rightGap, .gap, .neg⟩

theorem livingLeafGeomExcluded_R14 : LivingLeafGeomExcluded leaf_R14 :=
  not_realised_of_priority_junction leaf_R14 priorityJunction_R14

theorem livingLeafGeomExcluded_R17 : LivingLeafGeomExcluded leaf_R17 :=
  not_realised_of_priority_junction leaf_R17 priorityJunction_R17

theorem livingLeafGeomExcluded_R27_of_closer (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R27/R28") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_priority_junction ℓ (priorityJunction_R27_28 ℓ hc)

theorem livingLeafGeomExcluded_R27_meet_empty :
    LivingLeafGeomExcluded leaf_R27_meet_empty :=
  livingLeafGeomExcluded_R27_of_closer _ (by native_decide)
theorem livingLeafGeomExcluded_R27_meet_pos :
    LivingLeafGeomExcluded leaf_R27_meet_pos :=
  livingLeafGeomExcluded_R27_of_closer _ (by native_decide)
theorem livingLeafGeomExcluded_R27_meet_neg :
    LivingLeafGeomExcluded leaf_R27_meet_neg :=
  livingLeafGeomExcluded_R27_of_closer _ (by native_decide)
theorem livingLeafGeomExcluded_R27_gap_empty :
    LivingLeafGeomExcluded leaf_R27_gap_empty :=
  livingLeafGeomExcluded_R27_of_closer _ (by native_decide)
theorem livingLeafGeomExcluded_R27_gap_pos :
    LivingLeafGeomExcluded leaf_R27_gap_pos :=
  livingLeafGeomExcluded_R27_of_closer _ (by native_decide)
theorem livingLeafGeomExcluded_R27_gap_neg :
    LivingLeafGeomExcluded leaf_R27_gap_neg :=
  livingLeafGeomExcluded_R27_of_closer _ (by native_decide)

theorem priority_fullGeom_R14_R17_R27_28 :
    LivingLeafGeomExcluded leaf_R14 ∧
      LivingLeafGeomExcluded leaf_R17 ∧
        LivingLeafGeomExcluded leaf_R27_meet_empty ∧
          LivingLeafGeomExcluded leaf_R27_meet_pos ∧
            LivingLeafGeomExcluded leaf_R27_meet_neg ∧
              LivingLeafGeomExcluded leaf_R27_gap_empty ∧
                LivingLeafGeomExcluded leaf_R27_gap_pos ∧
                  LivingLeafGeomExcluded leaf_R27_gap_neg :=
  ⟨livingLeafGeomExcluded_R14, livingLeafGeomExcluded_R17,
    livingLeafGeomExcluded_R27_meet_empty, livingLeafGeomExcluded_R27_meet_pos,
    livingLeafGeomExcluded_R27_meet_neg, livingLeafGeomExcluded_R27_gap_empty,
    livingLeafGeomExcluded_R27_gap_pos, livingLeafGeomExcluded_R27_gap_neg⟩

def CloserGeomDischarged (label : String) : Prop :=
  ∀ ℓ : NearLeaf, closerModule ℓ = label → LivingLeafGeomExcluded ℓ

theorem closerGeomDischarged_R14 : CloserGeomDischarged "R14" :=
  fun ℓ hc => not_realised_of_priority_junction ℓ (Or.inl hc)
theorem closerGeomDischarged_R17 : CloserGeomDischarged "R17" :=
  fun ℓ hc => not_realised_of_priority_junction ℓ (Or.inr (Or.inl hc))
theorem closerGeomDischarged_R27_28 : CloserGeomDischarged "R27/R28" :=
  fun ℓ hc => livingLeafGeomExcluded_R27_of_closer ℓ hc

/-- Priority three closer labels fully GeomExcluded via junction. -/
def AllPriorityCloserGeomDischarged : Prop :=
  CloserGeomDischarged "R14" ∧ CloserGeomDischarged "R17" ∧
    CloserGeomDischarged "R27/R28"

theorem allPriorityCloserGeomDischarged : AllPriorityCloserGeomDischarged :=
  ⟨closerGeomDischarged_R14, closerGeomDischarged_R17, closerGeomDischarged_R27_28⟩

def CloserGeomBridge (label : String) : Prop :=
  CloserCertDischarged label → CloserGeomDischarged label

theorem closerGeomBridge_R14 : CloserGeomBridge "R14" := fun _ => closerGeomDischarged_R14
theorem closerGeomBridge_R17 : CloserGeomBridge "R17" := fun _ => closerGeomDischarged_R17
theorem closerGeomBridge_R27_28 : CloserGeomBridge "R27/R28" := fun _ => closerGeomDischarged_R27_28

def priorityFullGeomExcludedCount : ℕ := 8
theorem priorityFullGeomExcludedCount_eq : priorityFullGeomExcludedCount = 8 := rfl

/-- Only priority 3 of 8 named closers have GeomExcluded. -/
def inhabitedFullGeomCloserCount : ℕ := 3
theorem inhabitedFullGeomCloserCount_eq : inhabitedFullGeomCloserCount = 3 := rfl

def closerFullGeomDischargedProved_priority : Bool := true
theorem closerFullGeomDischargedProved_priority_true :
    closerFullGeomDischargedProved_priority = true := rfl

def closerFullGeomDischargedProved : Bool := false
theorem closerFullGeomDischargedProved_false : closerFullGeomDischargedProved = false := rfl

def manuscriptRayGeometryComplete_priority : Bool := true
theorem manuscriptRayGeometryComplete_priority_true :
    manuscriptRayGeometryComplete_priority = true := rfl

def manuscriptRayGeometryComplete : Bool := false
theorem manuscriptRayGeometryComplete_false : manuscriptRayGeometryComplete = false := rfl

def certOpenDependencyRemoved : Bool := true
theorem certOpenDependencyRemoved_true : certOpenDependencyRemoved = true := rfl

def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false : namedClosersDischargedProved = false := rfl

theorem fullGeom_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    LivingLeafGeomExcluded ℓ := LivingLeafGeomExcluded_of_impossible ℓ hi

def openStatus : String :=
  "CLOSED: OuterRT SE(2) hit/miss; LivingLeafGeomExcluded R14/R17/R27–28 via junction \
   (no LeafCloserCertDischarged / cert_open). \
   OPEN: R13/R16/R18/R19/R26 GeomExcluded; combinatorial CloserDischarged. Not PrincipalClaim."

end S6.LivingLeafGeomDischarge
