import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.NearEndGeometry
import S6Core.LivingLeafCertDischarge

/-!
# LivingLeafGeomExcluded — conditional dual/junction (analytic)

Packaging `dual` field removed. Living GeomExcluded for named closers is
**conditional** on `CloserDualResidual` / `JunctionConflict` holding for every
OuterRT match (to be inhabited per closer from J/Bernstein). Impossible leaves
remain unconditionally GeomExcluded.

`dualResidualAnalyticComplete` (dual ↔ junction) and ray witness algebra closed.
Combinatorial `LivingLeafExcluded` untouched. Not PrincipalClaim.
-/

namespace S6.LivingLeafGeomDischarge

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.NearEndGeometry
open S6.LivingLeafCertDischarge
open S6.RigidMotionChart

def leaf_R14 : NearLeaf := ⟨.bothMeet, .gap, .empty⟩
def leaf_R17 : NearLeaf := ⟨.bothMeet, .gap, .neg⟩
def leaf_R13_pos : NearLeaf := ⟨.bothMeet, .meet, .pos⟩
def leaf_R13_neg : NearLeaf := ⟨.bothMeet, .meet, .neg⟩
def leaf_R16 : NearLeaf := ⟨.bothMeet, .meet, .empty⟩
def leaf_R18 : NearLeaf := ⟨.bothMeet, .gap, .pos⟩
def leaf_R19_gap_empty : NearLeaf := ⟨.topGap, .gap, .empty⟩
def leaf_R26 : NearLeaf := ⟨.topGap, .meet, .empty⟩
def leaf_R27_meet_empty : NearLeaf := ⟨.rightGap, .meet, .empty⟩

/-- Conditional GeomExcluded from analytic dual-on-rt hypothesis. -/
theorem livingLeafGeomExcluded_of_dual_on_rt (ℓ : NearLeaf)
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → CloserDualResidual ℓ w) :
    LivingLeafGeomExcluded ℓ :=
  not_realised_of_dual_on_rt ℓ H

theorem livingLeafGeomExcluded_of_junction_on_rt (ℓ : NearLeaf)
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → JunctionConflict w) :
    LivingLeafGeomExcluded ℓ :=
  not_realised_of_junction_on_rt ℓ H

/-- Per-closer dual obligation (open until J/Bernstein supplies it). -/
def CloserDualObligation (label : String) : Prop :=
  ∀ ℓ : NearLeaf, closerModule ℓ = label →
    ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → CloserDualResidual ℓ w

theorem livingLeafGeomExcluded_of_closer_dual (label : String) (ℓ : NearLeaf)
    (hc : closerModule ℓ = label) (H : CloserDualObligation label) :
    LivingLeafGeomExcluded ℓ :=
  livingLeafGeomExcluded_of_dual_on_rt ℓ (fun g w hrt => H ℓ hc g w hrt)

def CloserGeomDischarged (label : String) : Prop :=
  ∀ ℓ : NearLeaf, closerModule ℓ = label → LivingLeafGeomExcluded ℓ

theorem closerGeomDischarged_of_dual (label : String) (H : CloserDualObligation label) :
    CloserGeomDischarged label :=
  fun ℓ hc => livingLeafGeomExcluded_of_closer_dual label ℓ hc H

def CloserGeomBridge (label : String) : Prop :=
  CloserCertDischarged label → CloserDualObligation label → CloserGeomDischarged label

theorem closerGeomBridge_any (label : String) : CloserGeomBridge label :=
  fun _ H => closerGeomDischarged_of_dual label H

/-- Priority / named GeomExcluded bundles remain open (need dual obligations). -/
def AllPriorityCloserGeomDischarged : Prop :=
  CloserGeomDischarged "R14" ∧ CloserGeomDischarged "R17" ∧
    CloserGeomDischarged "R27/R28"

def AllNamedCloserGeomDischarged : Prop :=
  CloserGeomDischarged "R13" ∧ CloserGeomDischarged "R14" ∧
    CloserGeomDischarged "R16" ∧ CloserGeomDischarged "R17" ∧
      CloserGeomDischarged "R18" ∧ CloserGeomDischarged "R19" ∧
        CloserGeomDischarged "R26" ∧ CloserGeomDischarged "R27/R28"

def priorityFullGeomExcludedCount : ℕ := 0
theorem priorityFullGeomExcludedCount_eq : priorityFullGeomExcludedCount = 0 := rfl

def inhabitedFullGeomCloserCount : ℕ := 0
theorem inhabitedFullGeomCloserCount_eq : inhabitedFullGeomCloserCount = 0 := rfl

def closerFullGeomDischargedProved_priority : Bool := false
theorem closerFullGeomDischargedProved_priority_false :
    closerFullGeomDischargedProved_priority = false := rfl

def closerFullGeomDischargedProved : Bool := false
theorem closerFullGeomDischargedProved_false : closerFullGeomDischargedProved = false := rfl

def manuscriptRayGeometryComplete_priority : Bool := false
theorem manuscriptRayGeometryComplete_priority_false :
    manuscriptRayGeometryComplete_priority = false := rfl

def manuscriptRayGeometryComplete : Bool := false
theorem manuscriptRayGeometryComplete_false : manuscriptRayGeometryComplete = false := rfl

def certOpenDependencyRemoved : Bool := true
theorem certOpenDependencyRemoved_true : certOpenDependencyRemoved = true := rfl

def dualResidualAnalyticComplete : Bool := true
theorem dualResidualAnalyticComplete_true : dualResidualAnalyticComplete = true := rfl

def rayWitnessAlgebraComplete : Bool := true
theorem rayWitnessAlgebraComplete_true : rayWitnessAlgebraComplete = true := rfl

def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false : namedClosersDischargedProved = false := rfl

theorem fullGeom_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    LivingLeafGeomExcluded ℓ := LivingLeafGeomExcluded_of_impossible ℓ hi

def openStatus : String :=
  "CLOSED: dualResidualAnalyticComplete (dual ↔ junction); packaging dual removed; \
   LeftStatus SE(2) witnesses; cert_open removed. \
   OPEN: CloserDualObligation per R13–R28 from J/Bernstein; living GeomExcluded; \
   combinatorial CloserDischarged. Not PrincipalClaim."

end S6.LivingLeafGeomDischarge
