import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.LivingLeafCertDischarge
import S6Core.RigidMotionChart

/-!
# Partial J/Bernstein → geometry maps (R14 / R17 / R27–R28 first)

## Proved (honest)
* Cert bundle discharged ⇒ `¬ NearEndLeafRealised` (Bernstein region_open wrapper).
* Any inhabited `NearEndSE2` excludes `CloserDualResidual` / `JunctionConflict`
  on its outer rays (SE(2) dual↔junction algebra) — independent of cert, but
  recorded here as the geometry half of the map.
* Combined `BernsteinGeometryMap` for R14, R17, R27/R28 (then all 8).

## Blocked
* `BernsteinForcesRawEmpty`: cert positivity ⇏ `¬ NearEndSE2Inhabited`.
  Certs are ℚ/Bernstein inequalities with no Lean identification to
  `(C, rays, leftRays, chart, fProj)`. That identification is the residual J step.

No packaging fields on `NearEndSE2`. Not PrincipalClaim / namedClosersDischarged.
-/

namespace S6.BernsteinGeometryMap

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.LivingLeafCertDischarge
open S6.RigidMotionChart

/-- Partial Bernstein→geometry map for one closer label. -/
structure BernsteinGeometryMap (label : String) : Prop where
  cert : CloserCertDischarged label
  closes_region :
    ∀ ℓ : NearLeaf, closerModule ℓ = label → ¬ NearEndLeafRealised ℓ
  excludes_dual_on_se2 :
    ∀ ℓ : NearLeaf, closerModule ℓ = label →
      ∀ cfg : NearEndSE2 ℓ, ¬ CloserDualResidual ℓ cfg.rays
  excludes_junction_on_se2 :
    ∀ ℓ : NearLeaf, closerModule ℓ = label →
      ∀ cfg : NearEndSE2 ℓ, ¬ JunctionConflict cfg.rays

theorem bernsteinGeometryMap_of_closer (label : String)
    (hc : CloserCertDischarged label)
    (hnot : ∀ ℓ : NearLeaf, closerModule ℓ = label → ¬ NearEndLeafRealised ℓ) :
    BernsteinGeometryMap label where
  cert := hc
  closes_region := hnot
  excludes_dual_on_se2 := fun _ _ cfg => se2_excludes_dualResidual _ cfg
  excludes_junction_on_se2 := fun _ _ cfg => se2_excludes_junction _ cfg

theorem bernsteinGeometryMap_R14 : BernsteinGeometryMap "R14" :=
  bernsteinGeometryMap_of_closer _ closerCert_R14 not_realised_of_closer_R14

theorem bernsteinGeometryMap_R17 : BernsteinGeometryMap "R17" :=
  bernsteinGeometryMap_of_closer _ closerCert_R17 not_realised_of_closer_R17

theorem bernsteinGeometryMap_R27_28 : BernsteinGeometryMap "R27/R28" :=
  bernsteinGeometryMap_of_closer _ closerCert_R27_28 not_realised_of_closer_R27_28

theorem bernsteinGeometryMap_R13 : BernsteinGeometryMap "R13" :=
  bernsteinGeometryMap_of_closer _ closerCert_R13 not_realised_of_closer_R13

theorem bernsteinGeometryMap_R16 : BernsteinGeometryMap "R16" :=
  bernsteinGeometryMap_of_closer _ closerCert_R16 not_realised_of_closer_R16

theorem bernsteinGeometryMap_R18 : BernsteinGeometryMap "R18" :=
  bernsteinGeometryMap_of_closer _ closerCert_R18 not_realised_of_closer_R18

theorem bernsteinGeometryMap_R19 : BernsteinGeometryMap "R19" :=
  bernsteinGeometryMap_of_closer _ closerCert_R19 not_realised_of_closer_R19

theorem bernsteinGeometryMap_R26 : BernsteinGeometryMap "R26" :=
  bernsteinGeometryMap_of_closer _ closerCert_R26 not_realised_of_closer_R26

def AllPriorityBernsteinGeometryMaps : Prop :=
  BernsteinGeometryMap "R14" ∧ BernsteinGeometryMap "R17" ∧
    BernsteinGeometryMap "R27/R28"

theorem allPriorityBernsteinGeometryMaps : AllPriorityBernsteinGeometryMaps :=
  ⟨bernsteinGeometryMap_R14, bernsteinGeometryMap_R17, bernsteinGeometryMap_R27_28⟩

def AllNamedBernsteinGeometryMaps : Prop :=
  BernsteinGeometryMap "R13" ∧ BernsteinGeometryMap "R14" ∧
    BernsteinGeometryMap "R16" ∧ BernsteinGeometryMap "R17" ∧
      BernsteinGeometryMap "R18" ∧ BernsteinGeometryMap "R19" ∧
        BernsteinGeometryMap "R26" ∧ BernsteinGeometryMap "R27/R28"

theorem allNamedBernsteinGeometryMaps : AllNamedBernsteinGeometryMaps :=
  ⟨bernsteinGeometryMap_R13, bernsteinGeometryMap_R14, bernsteinGeometryMap_R16,
    bernsteinGeometryMap_R17, bernsteinGeometryMap_R18, bernsteinGeometryMap_R19,
    bernsteinGeometryMap_R26, bernsteinGeometryMap_R27_28⟩

/-! ## Cert positivity cores (exported for future chart/ray identification) -/

def R14CertPositivityCore : Prop := R14CertBundle
theorem r14_cert_positivity_core : R14CertPositivityCore := r14_certBundle

def R17CertPositivityCore : Prop := R17CertBundle
theorem r17_cert_positivity_core : R17CertPositivityCore := r17_certBundle

def R27_28CertPositivityCore : Prop := R27_28CertBundle
theorem r27_28_cert_positivity_core : R27_28CertPositivityCore := r27_28_certBundle

/-- Leaf anchors for priority maps. -/
def leaf_R14 : NearLeaf := ⟨.bothMeet, .gap, .empty⟩
def leaf_R17 : NearLeaf := ⟨.bothMeet, .gap, .neg⟩
def leaf_R27_meet_empty : NearLeaf := ⟨.rightGap, .meet, .empty⟩

theorem r14_map_closes_region :
    ¬ NearEndLeafRealised leaf_R14 :=
  bernsteinGeometryMap_R14.closes_region _ (by native_decide)

theorem r17_map_closes_region :
    ¬ NearEndLeafRealised leaf_R17 :=
  bernsteinGeometryMap_R17.closes_region _ (by native_decide)

theorem r27_map_closes_region :
    ¬ NearEndLeafRealised leaf_R27_meet_empty :=
  bernsteinGeometryMap_R27_28.closes_region _ (by native_decide)

theorem r14_map_excludes_dual (cfg : NearEndSE2 leaf_R14) :
    ¬ CloserDualResidual leaf_R14 cfg.rays :=
  bernsteinGeometryMap_R14.excludes_dual_on_se2 _ (by native_decide) cfg

theorem r17_map_excludes_dual (cfg : NearEndSE2 leaf_R17) :
    ¬ CloserDualResidual leaf_R17 cfg.rays :=
  bernsteinGeometryMap_R17.excludes_dual_on_se2 _ (by native_decide) cfg

theorem r27_map_excludes_dual (cfg : NearEndSE2 leaf_R27_meet_empty) :
    ¬ CloserDualResidual leaf_R27_meet_empty cfg.rays :=
  bernsteinGeometryMap_R27_28.excludes_dual_on_se2 _ (by native_decide) cfg

/-! ## Open residual: cert ⇒ raw SE2 empty (not inhabited) -/

/-- Missing J step: discharged cert forces `¬ NearEndSE2Inhabited`. -/
def BernsteinForcesRawEmpty (label : String) : Prop :=
  CloserCertDischarged label →
    ∀ ℓ : NearLeaf, closerModule ℓ = label → ¬ NearEndSE2Inhabited ℓ

def AllPriorityBernsteinForcesRawEmpty : Prop :=
  BernsteinForcesRawEmpty "R14" ∧ BernsteinForcesRawEmpty "R17" ∧
    BernsteinForcesRawEmpty "R27/R28"

/-- OPEN: would close living raw SE2 emptiness for priority closers. -/
def bernsteinForcesRawEmptyProved : Bool := false
theorem bernsteinForcesRawEmptyProved_false :
    bernsteinForcesRawEmptyProved = false := rfl

/-- Partial maps inhabited for all 8; raw-empty force still open. -/
def bernsteinGeometryMapPartialProved : Bool := true
theorem bernsteinGeometryMapPartialProved_true :
    bernsteinGeometryMapPartialProved = true := rfl

def bernsteinGeometryMapPriorityProved : Bool := true
theorem bernsteinGeometryMapPriorityProved_true :
    bernsteinGeometryMapPriorityProved = true := rfl

def rawSE2EmptyProved : Bool := false
theorem rawSE2EmptyProved_false : rawSE2EmptyProved = false := rfl

def blockedReason : String :=
  "Partial map CLOSED: cert→¬NearEndLeafRealised + SE2 excludes dual/junction. \
   BLOCKED BernsteinForcesRawEmpty: no Lean ID from ℚ/Bernstein positivity to \
   contradiction on (C, rays, leftRays, chart, fProj)."

def openStatus : String :=
  "CLOSED: BernsteinGeometryMap ×8; positivity cores; CertGeometryIdPartial (SE2⇒hyps/chart/thresholds). \
   OPEN: BernsteinForcesRawEmpty (full J ID); combinatorial LivingLeafExcluded. \
   Not PrincipalClaim / namedClosersDischarged."

end S6.BernsteinGeometryMap
