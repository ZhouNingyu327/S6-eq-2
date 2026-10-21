import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.BernsteinGeometryMap
import S6Core.CertGeometryIdentification
import S6Core.CertJBoxIdentification
import S6Core.LivingLeafCertDischarge
import S6Core.NearEndRationalChecks
import S6Core.NearEndExactR24_28
import S6Core.BernsteinExactP1

/-!
# R17 / R27–R28 grid positivity packaging (honest partial)

Sources: `NearEndRationalChecks`, `NearEndExactR24_28`, `BernsteinExactP1`,
`LivingLeafCertDischarge` cert bundles; registry geometric hypotheses.

## Proved
* R17 analytic √2-sq / rational token bundle inhabited.
* R27/R28 Bernstein coeff-grid tokens inhabited (Exact + ExactP1).
* SE2 ⇒ registry hyps for R17 and R27 meet/empty (reexport).
* Combined `R17R27GridPosPartial`.

## Blocked
* No Lean map from these tokens onto `¬ NearEndSE2Inhabited` / raw-empty
  (same residual shape as R14 before Bernstein-form + bridge hyp).
* `BernsteinForcesRawEmpty` for R17 / R27–28 stays false.

Not PrincipalClaim / namedClosersDischarged. Bridge + BernsteinExact* untouched.
-/

namespace S6.CertR17R27GridPos

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.BernsteinGeometryMap
open S6.CertGeometryIdentification
open S6.CertJBoxIdentification
open S6.LivingLeafCertDischarge
open S6.NearEndRationalChecks
open S6.NearEndExactR24_28
open S6.BernsteinExactP1

/-! ## R17 -/

def R17GridPos : Prop := R17CertBundle

theorem r17GridPos : R17GridPos := r17_certBundle

theorem r17_se2_hyps (cfg : NearEndSE2 BernsteinGeometryMap.leaf_R17) :
    (cfg.rays.meetsR ∧ cfg.rays.meetsT) ∧ cfg.leftRays.gapsL ∧ cfg.fProj < 0 :=
  r17_hyp_from_se2 cfg

def R17GridPosPartial : Prop :=
  R17GridPos ∧
    (∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R17,
      (cfg.rays.meetsR ∧ cfg.rays.meetsT) ∧ cfg.leftRays.gapsL ∧ cfg.fProj < 0)

theorem r17GridPosPartial : R17GridPosPartial :=
  ⟨r17GridPos, fun cfg => r17_se2_hyps cfg⟩

/-! ## R27/R28 -/

def R27_28GridPos : Prop :=
  R27_28CertBundle ∧
    S6.BernsteinExactP1.nonnegList
      S6.BernsteinExactP1.check_round27_g2_two_branches_n4_ba4d19a580_numer = true ∧
      S6.NearEndExactR24_28.nonnegList
        S6.NearEndExactR24_28.check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs = true ∧
      S6.NearEndExactR24_28.nonnegList
        S6.NearEndExactR24_28.check_round27_g2_two_branches_n4_ba4d19a580_denom_coeffs = true

theorem r27_28GridPos : R27_28GridPos :=
  ⟨r27_28_certBundle,
    check_round27_g2_two_branches_n4_ba4d19a580_numer_nonneg,
    check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs_nonneg,
    check_round27_g2_two_branches_n4_ba4d19a580_denom_coeffs_nonneg⟩

theorem r27_se2_hyps (cfg : NearEndSE2 BernsteinGeometryMap.leaf_R27_meet_empty) :
    (cfg.rays.gapsR ∧ cfg.rays.meetsT) ∧ cfg.leftRays.meetsL ∧ cfg.fProj = 0 :=
  r27_hyp_from_se2 cfg

def R27_28GridPosPartial : Prop :=
  R27_28GridPos ∧
    (∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R27_meet_empty,
      (cfg.rays.gapsR ∧ cfg.rays.meetsT) ∧ cfg.leftRays.meetsL ∧ cfg.fProj = 0)

theorem r27_28GridPosPartial : R27_28GridPosPartial :=
  ⟨r27_28GridPos, fun cfg => r27_se2_hyps cfg⟩

def R17R27GridPosPartial : Prop := R17GridPosPartial ∧ R27_28GridPosPartial

theorem r17R27GridPosPartial : R17R27GridPosPartial :=
  ⟨r17GridPosPartial, r27_28GridPosPartial⟩

/-! ## Flags -/

def r17R27GridPosPartialProved : Bool := true
theorem r17R27GridPosPartialProved_true : r17R27GridPosPartialProved = true := rfl

def bernsteinForcesRawEmpty_R17_proved : Bool := false
theorem bernsteinForcesRawEmpty_R17_proved_false :
    bernsteinForcesRawEmpty_R17_proved = false := rfl

def bernsteinForcesRawEmpty_R27_proved : Bool := false
theorem bernsteinForcesRawEmpty_R27_proved_false :
    bernsteinForcesRawEmpty_R27_proved = false := rfl

def blockedReason : String :=
  "CLOSED: R17/R27–28 grid positivity tokens + SE2 hyp decode. \
   BLOCKED: cert/grid tokens ⇏ ¬NearEndSE2Inhabited (no SE2 field obstruction map)."

def openStatus : String :=
  "CLOSED: R17R27GridPosPartial. OPEN: BernsteinForcesRawEmpty R17/R27–28; \
   R14 ForcesBridgeJunction. Not PrincipalClaim / namedClosersDischarged."

end S6.CertR17R27GridPos
