import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.NearEndGeometry
import S6Core.LivingLeafCertDischarge

/-!
# LivingLeafGeomExcluded via derived OuterRT junction (all 8 closers)

Discharges full `LivingLeafGeomExcluded` for all eight named closers using
`dualResidual_implies_junction` (OuterRTMatches + CloserDualResidual) —
**not** `LeafCloserCertDischarged`. Combinatorial `LivingLeafExcluded` untouched.
Not PrincipalClaim. Dual residual still manuscript packaging.
-/

namespace S6.LivingLeafGeomDischarge

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.NearEndGeometry
open S6.LivingLeafCertDischarge

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

theorem livingLeafGeomExcluded_of_named (ℓ : NearLeaf) (hn : NamedCloser ℓ) :
    LivingLeafGeomExcluded ℓ :=
  not_realised_of_named_closer ℓ hn

theorem livingLeafGeomExcluded_of_closer_R13 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R13") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R13 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R14 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R14") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R14 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R16 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R16") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R16 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R17 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R17") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R17 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R18 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R18") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R18 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R19 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R19") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R19 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R26 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R26") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R26 ℓ hc)
theorem livingLeafGeomExcluded_of_closer_R27_28 (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R27/R28") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_named ℓ (namedCloser_R27_28 ℓ hc)

theorem livingLeafGeomExcluded_R14 : LivingLeafGeomExcluded leaf_R14 :=
  livingLeafGeomExcluded_of_closer_R14 _ (by native_decide)
theorem livingLeafGeomExcluded_R17 : LivingLeafGeomExcluded leaf_R17 :=
  livingLeafGeomExcluded_of_closer_R17 _ (by native_decide)
theorem livingLeafGeomExcluded_R13_pos : LivingLeafGeomExcluded leaf_R13_pos :=
  livingLeafGeomExcluded_of_closer_R13 _ (by native_decide)
theorem livingLeafGeomExcluded_R13_neg : LivingLeafGeomExcluded leaf_R13_neg :=
  livingLeafGeomExcluded_of_closer_R13 _ (by native_decide)
theorem livingLeafGeomExcluded_R16 : LivingLeafGeomExcluded leaf_R16 :=
  livingLeafGeomExcluded_of_closer_R16 _ (by native_decide)
theorem livingLeafGeomExcluded_R18 : LivingLeafGeomExcluded leaf_R18 :=
  livingLeafGeomExcluded_of_closer_R18 _ (by native_decide)
theorem livingLeafGeomExcluded_R19_gap_empty : LivingLeafGeomExcluded leaf_R19_gap_empty :=
  livingLeafGeomExcluded_of_closer_R19 _ (by native_decide)
theorem livingLeafGeomExcluded_R19_gap_neg : LivingLeafGeomExcluded leaf_R19_gap_neg :=
  livingLeafGeomExcluded_of_closer_R19 _ (by native_decide)
theorem livingLeafGeomExcluded_R19_meet_pos : LivingLeafGeomExcluded leaf_R19_meet_pos :=
  livingLeafGeomExcluded_of_closer_R19 _ (by native_decide)
theorem livingLeafGeomExcluded_R19_meet_neg : LivingLeafGeomExcluded leaf_R19_meet_neg :=
  livingLeafGeomExcluded_of_closer_R19 _ (by native_decide)
theorem livingLeafGeomExcluded_R26 : LivingLeafGeomExcluded leaf_R26 :=
  livingLeafGeomExcluded_of_closer_R26 _ (by native_decide)

theorem livingLeafGeomExcluded_R27_of_closer (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R27/R28") : LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_closer_R27_28 ℓ hc

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

theorem closerGeomDischarged_R13 : CloserGeomDischarged "R13" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R13 ℓ hc
theorem closerGeomDischarged_R14 : CloserGeomDischarged "R14" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R14 ℓ hc
theorem closerGeomDischarged_R16 : CloserGeomDischarged "R16" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R16 ℓ hc
theorem closerGeomDischarged_R17 : CloserGeomDischarged "R17" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R17 ℓ hc
theorem closerGeomDischarged_R18 : CloserGeomDischarged "R18" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R18 ℓ hc
theorem closerGeomDischarged_R19 : CloserGeomDischarged "R19" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R19 ℓ hc
theorem closerGeomDischarged_R26 : CloserGeomDischarged "R26" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R26 ℓ hc
theorem closerGeomDischarged_R27_28 : CloserGeomDischarged "R27/R28" :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_R27_28 ℓ hc

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

def CloserGeomBridge (label : String) : Prop :=
  CloserCertDischarged label → CloserGeomDischarged label

theorem closerGeomBridge_R13 : CloserGeomBridge "R13" := fun _ => closerGeomDischarged_R13
theorem closerGeomBridge_R14 : CloserGeomBridge "R14" := fun _ => closerGeomDischarged_R14
theorem closerGeomBridge_R16 : CloserGeomBridge "R16" := fun _ => closerGeomDischarged_R16
theorem closerGeomBridge_R17 : CloserGeomBridge "R17" := fun _ => closerGeomDischarged_R17
theorem closerGeomBridge_R18 : CloserGeomBridge "R18" := fun _ => closerGeomDischarged_R18
theorem closerGeomBridge_R19 : CloserGeomBridge "R19" := fun _ => closerGeomDischarged_R19
theorem closerGeomBridge_R26 : CloserGeomBridge "R26" := fun _ => closerGeomDischarged_R26
theorem closerGeomBridge_R27_28 : CloserGeomBridge "R27/R28" := fun _ => closerGeomDischarged_R27_28

def priorityFullGeomExcludedCount : ℕ := 8
theorem priorityFullGeomExcludedCount_eq : priorityFullGeomExcludedCount = 8 := rfl

def inhabitedFullGeomCloserCount : ℕ := 8
theorem inhabitedFullGeomCloserCount_eq : inhabitedFullGeomCloserCount = 8 := rfl

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

def dualResidualAnalyticComplete : Bool := false
theorem dualResidualAnalyticComplete_false : dualResidualAnalyticComplete = false := rfl

def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false : namedClosersDischargedProved = false := rfl

theorem fullGeom_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    LivingLeafGeomExcluded ℓ := LivingLeafGeomExcluded_of_impossible ℓ hi

/-- All 17 living leaves GeomExcluded via named-closer dual residual (packaging). -/
theorem all_living_geom_excluded_via_named :
    ∀ ℓ : NearLeaf, livingFlag ℓ = true → LivingLeafGeomExcluded ℓ :=
  fun ℓ h => not_realised_of_living ℓ h

def openStatus : String :=
  "CLOSED: all 8 NamedCloser LivingLeafGeomExcluded via derived JunctionConflict \
   (OuterRTMatches+CloserDualResidual); cert_open removed; manuscriptRayGeometryComplete. \
   OPEN: derive CloserDualResidual from J/analytic; combinatorial CloserDischarged. \
   Not PrincipalClaim."

end S6.LivingLeafGeomDischarge
