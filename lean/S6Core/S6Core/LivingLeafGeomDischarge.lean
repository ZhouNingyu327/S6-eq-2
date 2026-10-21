import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.NearEndGeometry
import S6Core.LivingLeafCertDischarge

/-!
# Geometric closer discharge (SE(2) + cert-pending bridge)

`NearEndRealisation.NearEndLeafRealised` is the concrete SE(2)/chart witness.
Full `LivingLeafGeomExcluded` (`¬ NearEndLeafRealised`) remains open for living leaves.

**Cert-pending bridge (inhabited for all 8; R14/R17/R27–R28 first):**
`NearEndSE2Pending` extends SE(2) with `residual_open : ¬ certBundle(closer)`.
When the Lean cert bundle is inhabited, pending realisation is impossible, so
`CloserGeomDischarged` holds. This is a cert→Prop bridge on an SE(2) substrate,
**not** full manuscript `¬ NearEndLeafRealised`, and **not** PrincipalClaim.
-/

namespace S6.LivingLeafGeomDischarge

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.NearEndGeometry
open S6.LivingLeafCertDischarge

/-- SE(2) realisation that still claims the closer residual (cert) is open. -/
structure NearEndSE2Pending (ℓ : NearLeaf) extends NearEndSE2 ℓ where
  residual_open : ¬ CloserCertDischarged (closerModule ℓ)

def NearEndLeafRealisedPending (ℓ : NearLeaf) : Prop :=
  Nonempty (NearEndSE2Pending ℓ)

theorem pending_implies_SE2 (ℓ : NearLeaf)
    (h : NearEndLeafRealisedPending ℓ) : NearEndLeafRealised ℓ := by
  obtain ⟨cfg⟩ := h
  exact ⟨cfg.toNearEndSE2⟩

def LivingLeafPendingExcluded (ℓ : NearLeaf) : Prop :=
  ¬ NearEndLeafRealisedPending ℓ

/-- Closer geom discharge via cert-pending SE(2) bridge. -/
def CloserGeomDischarged (label : String) : Prop :=
  ∀ ℓ : NearLeaf, closerModule ℓ = label → LivingLeafPendingExcluded ℓ

theorem closerGeomDischarged_of_cert (label : String)
    (h : CloserCertDischarged label) : CloserGeomDischarged label := by
  intro ℓ hc ⟨cfg⟩
  have hclosed : CloserCertDischarged (closerModule ℓ) := by
    rw [hc]; exact h
  exact cfg.residual_open hclosed

def CloserGeomBridge (label : String) : Prop :=
  CloserCertDischarged label → CloserGeomDischarged label

theorem closerGeomBridge_holds (label : String) : CloserGeomBridge label :=
  closerGeomDischarged_of_cert label

/-! ## R14 J / R17 analytic / R27–R28 harness first -/

theorem closerGeomDischarged_R14 : CloserGeomDischarged "R14" :=
  closerGeomDischarged_of_cert "R14" closerCert_R14
theorem closerGeomBridge_R14 : CloserGeomBridge "R14" := closerGeomBridge_holds "R14"

theorem closerGeomDischarged_R17 : CloserGeomDischarged "R17" :=
  closerGeomDischarged_of_cert "R17" closerCert_R17
theorem closerGeomBridge_R17 : CloserGeomBridge "R17" := closerGeomBridge_holds "R17"

theorem closerGeomDischarged_R27_28 : CloserGeomDischarged "R27/R28" :=
  closerGeomDischarged_of_cert "R27/R28" closerCert_R27_28
theorem closerGeomBridge_R27_28 : CloserGeomBridge "R27/R28" :=
  closerGeomBridge_holds "R27/R28"

/-! ## Remaining five -/

theorem closerGeomDischarged_R13 : CloserGeomDischarged "R13" :=
  closerGeomDischarged_of_cert "R13" closerCert_R13
theorem closerGeomDischarged_R16 : CloserGeomDischarged "R16" :=
  closerGeomDischarged_of_cert "R16" closerCert_R16
theorem closerGeomDischarged_R18 : CloserGeomDischarged "R18" :=
  closerGeomDischarged_of_cert "R18" closerCert_R18
theorem closerGeomDischarged_R19 : CloserGeomDischarged "R19" :=
  closerGeomDischarged_of_cert "R19" closerCert_R19
theorem closerGeomDischarged_R26 : CloserGeomDischarged "R26" :=
  closerGeomDischarged_of_cert "R26" closerCert_R26

def AllNamedCloserGeomDischarged : Prop :=
  CloserGeomDischarged "R13" ∧
    CloserGeomDischarged "R14" ∧
      CloserGeomDischarged "R16" ∧
        CloserGeomDischarged "R17" ∧
          CloserGeomDischarged "R18" ∧
            CloserGeomDischarged "R19" ∧
              CloserGeomDischarged "R26" ∧
                CloserGeomDischarged "R27/R28"

theorem allNamedCloserGeomDischarged : AllNamedCloserGeomDischarged :=
  ⟨closerGeomDischarged_R13, closerGeomDischarged_R14, closerGeomDischarged_R16,
    closerGeomDischarged_R17, closerGeomDischarged_R18, closerGeomDischarged_R19,
    closerGeomDischarged_R26, closerGeomDischarged_R27_28⟩

def inhabitedCloserGeomPendingCount : ℕ := 8
theorem inhabitedCloserGeomPendingCount_eq :
    inhabitedCloserGeomPendingCount = 8 := rfl

def closerGeomPendingBridgesProved : Bool := true
theorem closerGeomPendingBridgesProved_true :
    closerGeomPendingBridgesProved = true := rfl

/-- Full `¬ NearEndLeafRealised` (manuscript SE(2) exclusion) still open. -/
def closerFullGeomDischargedProved : Bool := false
theorem closerFullGeomDischargedProved_false :
    closerFullGeomDischargedProved = false := rfl

def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false :
    namedClosersDischargedProved = false := rfl

/-- Impossible leaves are full-geom excluded (SE(2)). -/
theorem fullGeom_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    S6.NearEndGeometry.LivingLeafGeomExcluded ℓ :=
  S6.NearEndGeometry.LivingLeafGeomExcluded_of_impossible ℓ hi

def openStatus : String :=
  "CLOSED: NearEndSE2 replaces opacity; CloserGeomDischarged pending×8 \
   (R14/R17/R27–28 first). \
   OPEN: full ¬NearEndLeafRealised; combinatorial CloserDischarged. \
   Not PrincipalClaim."

end S6.LivingLeafGeomDischarge
