import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.NearEndGeometry
import S6Core.LivingLeafCertDischarge

/-!
# Full LivingLeafGeomExcluded (OuterRT + cert barrier)

Discharges full `LivingLeafGeomExcluded` for R14 / R17 / R27–R28 first, then all
eight living closers. Uses OuterRT rays on `NearEndSE2` plus closer-cert barrier
(not pending-only). Combinatorial `LivingLeafExcluded` untouched. Not PrincipalClaim.
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
  not_realised_of_leafCloserCert leaf_R14 leafCloserCert_R14

theorem livingLeafGeomExcluded_R17 : LivingLeafGeomExcluded leaf_R17 :=
  not_realised_of_leafCloserCert leaf_R17 leafCloserCert_R17

theorem livingLeafGeomExcluded_R27_of_closer (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R27/R28") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R27_28 ℓ hc)

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

theorem livingLeafGeomExcluded_of_closer_R13 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R13") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R13 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R14 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R14") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R14 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R16 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R16") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R16 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R17 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R17") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R17 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R18 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R18") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R18 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R19 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R19") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R19 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R26 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R26") : LivingLeafGeomExcluded ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R26 ℓ hc)

def CloserGeomDischarged (label : String) : Prop :=
  ∀ ℓ : NearLeaf, closerModule ℓ = label → LivingLeafGeomExcluded ℓ

theorem closerGeomDischarged_R14 : CloserGeomDischarged "R14" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R14 ℓ hc
theorem closerGeomDischarged_R17 : CloserGeomDischarged "R17" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R17 ℓ hc
theorem closerGeomDischarged_R27_28 : CloserGeomDischarged "R27/R28" :=
  fun ℓ hc => livingLeafGeomExcluded_R27_of_closer ℓ hc
theorem closerGeomDischarged_R13 : CloserGeomDischarged "R13" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R13 ℓ hc
theorem closerGeomDischarged_R16 : CloserGeomDischarged "R16" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R16 ℓ hc
theorem closerGeomDischarged_R18 : CloserGeomDischarged "R18" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R18 ℓ hc
theorem closerGeomDischarged_R19 : CloserGeomDischarged "R19" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R19 ℓ hc
theorem closerGeomDischarged_R26 : CloserGeomDischarged "R26" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R26 ℓ hc

def AllNamedCloserGeomDischarged : Prop :=
  CloserGeomDischarged "R13" ∧ CloserGeomDischarged "R14" ∧
    CloserGeomDischarged "R16" ∧ CloserGeomDischarged "R17" ∧
      CloserGeomDischarged "R18" ∧ CloserGeomDischarged "R19" ∧
        CloserGeomDischarged "R26" ∧ CloserGeomDischarged "R27/R28"

theorem allNamedCloserGeomDischarged : AllNamedCloserGeomDischarged :=
  ⟨closerGeomDischarged_R13, closerGeomDischarged_R14, closerGeomDischarged_R16,
    closerGeomDischarged_R17, closerGeomDischarged_R18, closerGeomDischarged_R19,
    closerGeomDischarged_R26, closerGeomDischarged_R27_28⟩

def CloserGeomBridge (label : String) : Prop :=
  CloserCertDischarged label → CloserGeomDischarged label

theorem closerGeomBridge_R14 : CloserGeomBridge "R14" := fun _ => closerGeomDischarged_R14
theorem closerGeomBridge_R17 : CloserGeomBridge "R17" := fun _ => closerGeomDischarged_R17
theorem closerGeomBridge_R27_28 : CloserGeomBridge "R27/R28" := fun _ => closerGeomDischarged_R27_28

def priorityFullGeomExcludedCount : ℕ := 8
theorem priorityFullGeomExcludedCount_eq : priorityFullGeomExcludedCount = 8 := rfl

def inhabitedFullGeomCloserCount : ℕ := 8
theorem inhabitedFullGeomCloserCount_eq : inhabitedFullGeomCloserCount = 8 := rfl

def closerFullGeomDischargedProved : Bool := true
theorem closerFullGeomDischargedProved_true : closerFullGeomDischargedProved = true := rfl

def manuscriptRayGeometryComplete : Bool := false
theorem manuscriptRayGeometryComplete_false : manuscriptRayGeometryComplete = false := rfl

def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false : namedClosersDischargedProved = false := rfl

theorem fullGeom_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    LivingLeafGeomExcluded ℓ := LivingLeafGeomExcluded_of_impossible ℓ hi

def openStatus : String :=
  "CLOSED: OuterRT on NearEndSE2; full LivingLeafGeomExcluded for R14/R17/R27–28 and all 8 closers. \
   OPEN: manuscript ray geometry beyond d≤1/1<d; combinatorial CloserDischarged. Not PrincipalClaim."

end S6.LivingLeafGeomDischarge
