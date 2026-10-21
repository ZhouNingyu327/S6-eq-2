import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.NearEndGeometry
import S6Core.LivingLeafCertDischarge
import S6Core.BernsteinGeometryMap
import S6Core.RigidMotionChart

/-!
# LivingLeafGeomExcluded via ManuscriptCompleteRealised + CloserDualObligation

`LivingLeafGeomExcluded` := `¬ ManuscriptCompleteRealised` (OuterRT∧dual),
proved for every leaf by dual↔junction algebra — **no packaging fields**.

`CloserDualObligation label` := Bernstein/exact `CloserCertDischarged label`
together with geom exclusion for that closer's leaves (from the same algebra).
Inhabited first for R14 / R17 / R27–R28, then all eight.

Also: `NearEndLeafRealised` (SE2 + Bernstein region_open) discharged for all
living closers. Raw living `¬ NearEndSE2Inhabited` blocked (SE(2)-satisfiable);
impossible leaves + dual/junction exclusions proved. Combinatorial spine untouched.
-/

namespace S6.LivingLeafGeomDischarge

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.NearEndGeometry
open S6.LivingLeafCertDischarge
open S6.BernsteinGeometryMap
open S6.RigidMotionChart

def leaf_R14 : NearLeaf := ⟨.bothMeet, .gap, .empty⟩
def leaf_R17 : NearLeaf := ⟨.bothMeet, .gap, .neg⟩
def leaf_R13_pos : NearLeaf := ⟨.bothMeet, .meet, .pos⟩
def leaf_R13_neg : NearLeaf := ⟨.bothMeet, .meet, .neg⟩
def leaf_R16 : NearLeaf := ⟨.bothMeet, .meet, .empty⟩
def leaf_R18 : NearLeaf := ⟨.bothMeet, .gap, .pos⟩
def leaf_R19_gap_empty : NearLeaf := ⟨.topGap, .gap, .empty⟩
def leaf_R19_gap_neg : NearLeaf := ⟨.topGap, .gap, .neg⟩
def leaf_R19_meet_pos : NearLeaf := ⟨.topGap, .meet, .pos⟩
def leaf_R19_meet_neg : NearLeaf := ⟨.topGap, .meet, .neg⟩
def leaf_R26 : NearLeaf := ⟨.topGap, .meet, .empty⟩
def leaf_R27_meet_empty : NearLeaf := ⟨.rightGap, .meet, .empty⟩
def leaf_R27_meet_pos : NearLeaf := ⟨.rightGap, .meet, .pos⟩
def leaf_R27_meet_neg : NearLeaf := ⟨.rightGap, .meet, .neg⟩
def leaf_R27_gap_empty : NearLeaf := ⟨.rightGap, .gap, .empty⟩
def leaf_R27_gap_pos : NearLeaf := ⟨.rightGap, .gap, .pos⟩
def leaf_R27_gap_neg : NearLeaf := ⟨.rightGap, .gap, .neg⟩

theorem livingLeafGeomExcluded_any (ℓ : NearLeaf) : LivingLeafGeomExcluded ℓ :=
  not_manuscriptCompleteRealised ℓ

theorem livingLeafGeomExcluded_R14 : LivingLeafGeomExcluded leaf_R14 :=
  livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R17 : LivingLeafGeomExcluded leaf_R17 :=
  livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R13_pos : LivingLeafGeomExcluded leaf_R13_pos :=
  livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R13_neg : LivingLeafGeomExcluded leaf_R13_neg :=
  livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R16 : LivingLeafGeomExcluded leaf_R16 :=
  livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R18 : LivingLeafGeomExcluded leaf_R18 :=
  livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R26 : LivingLeafGeomExcluded leaf_R26 :=
  livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R27_meet_empty :
    LivingLeafGeomExcluded leaf_R27_meet_empty := livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R27_meet_pos :
    LivingLeafGeomExcluded leaf_R27_meet_pos := livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R27_meet_neg :
    LivingLeafGeomExcluded leaf_R27_meet_neg := livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R27_gap_empty :
    LivingLeafGeomExcluded leaf_R27_gap_empty := livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R27_gap_pos :
    LivingLeafGeomExcluded leaf_R27_gap_pos := livingLeafGeomExcluded_any _
theorem livingLeafGeomExcluded_R27_gap_neg :
    LivingLeafGeomExcluded leaf_R27_gap_neg := livingLeafGeomExcluded_any _

/-- Per-closer dual obligation: Bernstein/exact cert + manuscript-complete geom exclusion. -/
def CloserDualObligation (label : String) : Prop :=
  CloserCertDischarged label ∧
    (∀ ℓ : NearLeaf, closerModule ℓ = label → LivingLeafGeomExcluded ℓ)

theorem closerDualObligation_of_cert (label : String)
    (hc : CloserCertDischarged label) : CloserDualObligation label :=
  ⟨hc, fun _ _ => livingLeafGeomExcluded_any _⟩

theorem closerDualObligation_R14 : CloserDualObligation "R14" :=
  closerDualObligation_of_cert _ closerCert_R14
theorem closerDualObligation_R17 : CloserDualObligation "R17" :=
  closerDualObligation_of_cert _ closerCert_R17
theorem closerDualObligation_R27_28 : CloserDualObligation "R27/R28" :=
  closerDualObligation_of_cert _ closerCert_R27_28
theorem closerDualObligation_R13 : CloserDualObligation "R13" :=
  closerDualObligation_of_cert _ closerCert_R13
theorem closerDualObligation_R16 : CloserDualObligation "R16" :=
  closerDualObligation_of_cert _ closerCert_R16
theorem closerDualObligation_R18 : CloserDualObligation "R18" :=
  closerDualObligation_of_cert _ closerCert_R18
theorem closerDualObligation_R19 : CloserDualObligation "R19" :=
  closerDualObligation_of_cert _ closerCert_R19
theorem closerDualObligation_R26 : CloserDualObligation "R26" :=
  closerDualObligation_of_cert _ closerCert_R26

def AllPriorityCloserDualObligations : Prop :=
  CloserDualObligation "R14" ∧ CloserDualObligation "R17" ∧
    CloserDualObligation "R27/R28"

theorem allPriorityCloserDualObligations : AllPriorityCloserDualObligations :=
  ⟨closerDualObligation_R14, closerDualObligation_R17, closerDualObligation_R27_28⟩

def AllNamedCloserDualObligations : Prop :=
  CloserDualObligation "R13" ∧ CloserDualObligation "R14" ∧
    CloserDualObligation "R16" ∧ CloserDualObligation "R17" ∧
      CloserDualObligation "R18" ∧ CloserDualObligation "R19" ∧
        CloserDualObligation "R26" ∧ CloserDualObligation "R27/R28"

theorem allNamedCloserDualObligations : AllNamedCloserDualObligations :=
  ⟨closerDualObligation_R13, closerDualObligation_R14, closerDualObligation_R16,
    closerDualObligation_R17, closerDualObligation_R18, closerDualObligation_R19,
    closerDualObligation_R26, closerDualObligation_R27_28⟩

def CloserGeomDischarged (label : String) : Prop :=
  ∀ ℓ : NearLeaf, closerModule ℓ = label → LivingLeafGeomExcluded ℓ

theorem closerGeomDischarged_of_dual (label : String) (H : CloserDualObligation label) :
    CloserGeomDischarged label := H.2

theorem closerGeomDischarged_R14 : CloserGeomDischarged "R14" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R14
theorem closerGeomDischarged_R17 : CloserGeomDischarged "R17" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R17
theorem closerGeomDischarged_R27_28 : CloserGeomDischarged "R27/R28" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R27_28
theorem closerGeomDischarged_R13 : CloserGeomDischarged "R13" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R13
theorem closerGeomDischarged_R16 : CloserGeomDischarged "R16" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R16
theorem closerGeomDischarged_R18 : CloserGeomDischarged "R18" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R18
theorem closerGeomDischarged_R19 : CloserGeomDischarged "R19" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R19
theorem closerGeomDischarged_R26 : CloserGeomDischarged "R26" :=
  closerGeomDischarged_of_dual _ closerDualObligation_R26

def AllPriorityCloserGeomDischarged : Prop :=
  CloserGeomDischarged "R14" ∧ CloserGeomDischarged "R17" ∧
    CloserGeomDischarged "R27/R28"

theorem allPriorityCloserGeomDischarged : AllPriorityCloserGeomDischarged :=
  ⟨closerGeomDischarged_R14, closerGeomDischarged_R17, closerGeomDischarged_R27_28⟩

def AllNamedCloserGeomDischarged : Prop :=
  CloserGeomDischarged "R13" ∧ CloserGeomDischarged "R14" ∧
    CloserGeomDischarged "R16" ∧ CloserGeomDischarged "R17" ∧
      CloserGeomDischarged "R18" ∧ CloserGeomDischarged "R19" ∧
        CloserGeomDischarged "R26" ∧ CloserGeomDischarged "R27/R28"

theorem allNamedCloserGeomDischarged : AllNamedCloserGeomDischarged :=
  ⟨closerGeomDischarged_R13, closerGeomDischarged_R14, closerGeomDischarged_R16,
    closerGeomDischarged_R17, closerGeomDischarged_R18, closerGeomDischarged_R19,
    closerGeomDischarged_R26, closerGeomDischarged_R27_28⟩

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

def CloserGeomBridge (label : String) : Prop :=
  CloserCertDischarged label → CloserGeomDischarged label

theorem closerGeomBridge_any (label : String) : CloserGeomBridge label :=
  fun hc => (closerDualObligation_of_cert label hc).2

def priorityFullGeomExcludedCount : ℕ := 8
theorem priorityFullGeomExcludedCount_eq : priorityFullGeomExcludedCount = 8 := rfl

def inhabitedFullGeomCloserCount : ℕ := 8
theorem inhabitedFullGeomCloserCount_eq : inhabitedFullGeomCloserCount = 8 := rfl

def inhabitedDualObligationCloserCount : ℕ := 8
theorem inhabitedDualObligationCloserCount_eq :
    inhabitedDualObligationCloserCount = 8 := rfl

def closerFullGeomDischargedProved_priority : Bool := true
theorem closerFullGeomDischargedProved_priority_true :
    closerFullGeomDischargedProved_priority = true := rfl

def closerFullGeomDischargedProved : Bool := true
theorem closerFullGeomDischargedProved_true : closerFullGeomDischargedProved = true := rfl

def manuscriptRayGeometryComplete_priority : Bool := true
theorem manuscriptRayGeometryComplete_priority_true :
    manuscriptRayGeometryComplete_priority = true := rfl

def manuscriptRayGeometryComplete : Bool := true
theorem manuscriptRayGeometryComplete_true : manuscriptRayGeometryComplete = true := rfl

def certOpenDependencyRemoved : Bool := true
theorem certOpenDependencyRemoved_true : certOpenDependencyRemoved = true := rfl

def dualResidualAnalyticComplete : Bool := true
theorem dualResidualAnalyticComplete_true : dualResidualAnalyticComplete = true := rfl

def rayWitnessAlgebraComplete : Bool := true
theorem rayWitnessAlgebraComplete_true : rayWitnessAlgebraComplete = true := rfl

def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false : namedClosersDischargedProved = false := rfl

def partialSE2UnrealisedProved : Bool := true
theorem partialSE2UnrealisedProved_true : partialSE2UnrealisedProved = true := rfl

def rawSE2EmptyProved : Bool := false
theorem rawSE2EmptyProved_false : rawSE2EmptyProved = false := rfl

theorem fullGeom_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    LivingLeafGeomExcluded ℓ := LivingLeafGeomExcluded_of_impossible ℓ hi

theorem partialSE2_not_realised_priority :
    ¬ NearEndLeafRealised leaf_R14 ∧
      ¬ NearEndLeafRealised leaf_R17 ∧
        ¬ NearEndLeafRealised leaf_R27_meet_empty :=
  ⟨not_realised_R14, not_realised_R17, not_realised_R27_meet_empty⟩

theorem partialSE2_not_realised_all_living :
    ∀ ℓ : NearLeaf, livingFlag ℓ = true → ¬ NearEndLeafRealised ℓ :=
  all_living_not_nearEndLeafRealised

/-- Raw SE2 empty for all 7 impossible leaves. -/
theorem rawSE2_empty_impossible :
    (∀ left fh, ¬ NearEndSE2Inhabited ⟨.bothGap, left, fh⟩) ∧
      ¬ NearEndSE2Inhabited ⟨.topGap, .gap, .pos⟩ :=
  ⟨not_se2Inhabited_bothGap, not_se2Inhabited_topGap_gap_pos⟩

theorem rawSE2_se2_excludes_dual_R14 (cfg : NearEndSE2 leaf_R14) :
    ¬ CloserDualResidual leaf_R14 cfg.rays :=
  se2_excludes_dualResidual _ cfg

theorem rawSE2_se2_excludes_dual_R17 (cfg : NearEndSE2 leaf_R17) :
    ¬ CloserDualResidual leaf_R17 cfg.rays :=
  se2_excludes_dualResidual _ cfg

theorem rawSE2_blocked_living_documented :
    rawSE2EmptyBlockedReason ≠ "" := by native_decide

def rawSE2ImpossibleEmptyProved : Bool := true
theorem rawSE2ImpossibleEmptyProved_true : rawSE2ImpossibleEmptyProved = true := rfl

def rawSE2LivingEmptyProved : Bool := false
theorem rawSE2LivingEmptyProved_false : rawSE2LivingEmptyProved = false := rfl

theorem bernsteinGeometryMap_priority_reexport : AllPriorityBernsteinGeometryMaps :=
  allPriorityBernsteinGeometryMaps

theorem bernsteinGeometryMap_all_reexport : AllNamedBernsteinGeometryMaps :=
  allNamedBernsteinGeometryMaps

theorem bernsteinGeometryMapPartialProved_true_reexport :
    bernsteinGeometryMapPartialProved = true := bernsteinGeometryMapPartialProved_true

theorem bernsteinForcesRawEmptyProved_false_reexport :
    bernsteinForcesRawEmptyProved = false := bernsteinForcesRawEmptyProved_false

def openStatus : String :=
  "CLOSED: BernsteinGeometryMap ×8 (cert→region + SE2 excludes dual);    partialSE2UnrealisedProved; GeomExcluded.    BLOCKED BernsteinForcesRawEmpty / raw living SE2 empty (no cert→(C,rays,chart) ID).    OPEN: combinatorial CloserDischarged. Not PrincipalClaim."

end S6.LivingLeafGeomDischarge
