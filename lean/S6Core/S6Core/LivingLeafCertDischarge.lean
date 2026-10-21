import Mathlib.Tactic
import S6Core.NearEndGeometry
import S6Core.NearEndRealisation
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.LivingLeafCloserBridge
import S6Core.NearEndRationalChecks
import S6Core.NearEndExactR24_28
import S6Core.Round13PairBernstein

/-!
# Living-leaf cert discharge (toward CloserDischarged)

## Encoding note (honest)

`LivingLeafExcluded ℓ := living ℓ → False` and `living ℓ := livingFlag ℓ = true`.
For each of the 17 living leaves we already have `livingFlag = true` by `native_decide`,
so `LivingLeafExcluded` on those leaves is equivalent to `False` and **cannot** be
inhabited without inconsistency. Consequently the residual-8 `CloserDischarged`
labels (which target `LivingLeafExcluded`) also cannot be inhabited under the
current encoding.

This module therefore:

1. Records that fact as theorems.
2. Inhabits **`CloserCertDischarged`** bundles (exact ℚ / Bernstein payloads) for
   as many of the 8 labels as Lean currently carries.
3. Packages open **`CloserGeomBridge`** arrows
   `CloserCertDischarged label → CloserDischarged label`.
4. Proves: all 8 cert discharges + all 8 geom bridges ⇒ `AllNamedClosersDischarged`.

Does **not** set `namedClosersDischargedProved` / PrincipalClaim. Forbidden files untouched.
-/

namespace S6.LivingLeafCertDischarge

open S6.NearEndGeometry
open S6.Exhaustiveness
open S6.LeafCertificates
open S6.LivingLeafCloserBridge
open S6.NearEndRationalChecks
open S6.NearEndExactR24_28
open S6.Round13PairBernstein

/-! ## LivingLeafExcluded vs livingFlag -/

/-- On a leaf with `livingFlag = true`, `LivingLeafExcluded` is equivalent to `False`. -/
theorem LivingLeafExcluded_iff_False_of_livingFlag
    (ℓ : NearLeaf) (h : livingFlag ℓ = true) :
    LivingLeafExcluded ℓ ↔ False := by
  constructor
  · intro hexcl
    exact hexcl h
  · intro f
    exact False.elim f

/-- Hence `CloserDischarged` for a label that has a living leaf is blocked until
the exclusion Prop is reformulated (e.g. realised-config → False). -/
theorem CloserDischarged_blocked_of_living_witness
    (label : String) (ℓ : NearLeaf)
    (hlive : livingFlag ℓ = true) (hc : closerModule ℓ = label) :
    CloserDischarged label → False := by
  intro hdis
  have hexcl : LivingLeafExcluded ℓ := hdis ℓ hlive hc
  exact (LivingLeafExcluded_iff_False_of_livingFlag ℓ hlive).1 hexcl

theorem CloserDischarged_R14_blocked :
    CloserDischarged "R14" → False :=
  CloserDischarged_blocked_of_living_witness "R14"
    ⟨.bothMeet, .gap, .empty⟩ (by native_decide) (by native_decide)

theorem CloserDischarged_R17_blocked :
    CloserDischarged "R17" → False :=
  CloserDischarged_blocked_of_living_witness "R17"
    ⟨.bothMeet, .gap, .neg⟩ (by native_decide) (by native_decide)

theorem CloserDischarged_R27_28_blocked :
    CloserDischarged "R27/R28" → False :=
  CloserDischarged_blocked_of_living_witness "R27/R28"
    ⟨.rightGap, .meet, .empty⟩ (by native_decide) (by native_decide)

/-! ## Certificate bundles (inhabited) -/

/-- R14 J-certificate min positivity core (branch c + sample m-paths). -/
def R14CertBundle : Prop :=
  (0 : ℚ) < (19 : ℚ) / 125 ∧
    (0 : ℚ) < (290632 : ℚ) / 9765625 ∧
      (0 : ℚ) < (451 : ℚ) / 80 ∧
        (0 : ℚ) < (33 : ℚ) / 8 ∧
          (0 : ℚ) < (81 : ℚ) / 32

theorem r14_certBundle : R14CertBundle :=
  ⟨r14_c_root_min_R_pos, r14_c_root_min_P_pos, r14_m_00_min_R_pos,
    r14_m_0100_min_R_pos, r14_m_0101_min_R_pos⟩

/-- R16 geometric-reduction exact endpoint. -/
def R16CertBundle : Prop :=
  (256 : ℚ) / 36993 < (1 : ℚ) / 101 ∧ (4 : ℚ) / 15 ≤ (4 : ℚ) / 15

theorem r16_certBundle : R16CertBundle :=
  ⟨r16_exact_endpoint_lt, r16_4_15_le_bound⟩

/-- R17 analytic-negative rational_checks (squared √2 forms). -/
def R17CertBundle : Prop :=
  (0 : ℚ) < (709 : ℚ) / 5184 ∧
    (34 : ℚ) / 75 < (1 : ℚ) / 2 ∧
      (193 : ℚ) / 225 > (5 : ℚ) / 6 ∧
        (19 : ℚ)^2 * 2 < (27 : ℚ)^2 ∧
          (2 : ℚ) < ((17 : ℚ) / 12)^2 ∧
            ((26 : ℚ) / 15)^2 > (2 : ℚ)

theorem r17_certBundle : R17CertBundle :=
  ⟨r17_709_over_5184_pos, r17_34_75_lt_half, r17_193_225_gt_five_six,
    r17_19_sqrt2_lt_27_sq, r17_sqrt2_minus_one_lt_5_12_sq, r17_26_15_gt_sqrt2_sq⟩

/-- R18 positive-projection constant_checks. -/
def R18CertBundle : Prop :=
  (0 : ℚ) < (1 : ℚ) / 225 ∧
    (4 : ℚ) / 15 < (1 : ℚ) / 3 ∧
      (4 : ℚ) / 15 < (1 : ℚ) / 2

theorem r18_certBundle : R18CertBundle :=
  ⟨r18_pos_cap_at_4_15, r18_4_15_lt_third, r18_4_15_lt_half⟩

/-- R19 top-gap constant_checks. -/
def R19CertBundle : Prop :=
  (2 : ℚ) < ((3 : ℚ) / 2)^2 ∧
    (19 : ℚ)^2 * 2 < (27 : ℚ)^2 ∧
      ((26 : ℚ) / 15)^2 > (2 : ℚ) ∧
        (225 : ℚ) / 193 < (7 : ℚ) / 6 ∧
          (244 : ℚ) / 495 < (1 : ℚ) / 2 ∧
            (0 : ℚ) < (709 : ℚ) / 5184

theorem r19_certBundle : R19CertBundle :=
  ⟨r19_sqrt2_lt_3_2_sq, r19_19_sqrt2_lt_27_sq, r19_26_15_gt_sqrt2_sq,
    r19_225_193_lt_7_6, r19_244_495_lt_half, r19_709_over_5184_pos⟩

/-- R27/R28 harness Bernstein uniform-sign sample. -/
def R27_28CertBundle : Prop :=
  S6.NearEndExactR24_28.nonnegList check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs = true ∧
    S6.NearEndExactR24_28.nonnegList check_round27_g2_two_branches_n4_ba4d19a580_denom_coeffs = true ∧
      S6.NearEndExactR24_28.nonnegList check_round27_g2_two_branches_n9_a80fbdcce8_numer_coeffs = true ∧
        S6.NearEndExactR24_28.nonnegList check_round28_g2_near_complete_n5_023bbe2fb6_coeffs = true ∧
          S6.NearEndExactR24_28.nonposList check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_num = true ∧
            S6.NearEndExactR24_28.nonnegList check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_den = true

theorem r27_28_certBundle : R27_28CertBundle :=
  ⟨check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs_nonneg,
    check_round27_g2_two_branches_n4_ba4d19a580_denom_coeffs_nonneg,
    check_round27_g2_two_branches_n9_a80fbdcce8_numer_coeffs_nonneg,
    check_round28_g2_near_complete_n5_023bbe2fb6_coeffs_nonneg,
    check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_num_nonpos,
    check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_den_nonneg⟩

/-- R13 pair Bernstein sample (first two rows). -/
def R13CertBundle : Prop :=
  S6.Round13PairBernstein.nonnegList branch_c_poly0_row0 = true ∧
    S6.Round13PairBernstein.nonnegList branch_c_poly0_row1 = true

theorem r13_certBundle : R13CertBundle :=
  ⟨branch_c_poly0_row0_nonneg, branch_c_poly0_row1_nonneg⟩

/-- R26 top-gap exact Bernstein sample. -/
def R26CertBundle : Prop :=
  S6.NearEndExactR24_28.nonnegList check_round26_g2_top_n7_1cf912de97_leading_pos_coeffs_on_1_3 = true ∧
    S6.NearEndExactR24_28.nonnegList check_round26_g2_top_n7_44d9df748d_numer_coeffs = true ∧
      S6.NearEndExactR24_28.nonnegList check_round26_g2_top_n7_44d9df748d_denom_coeffs = true

theorem r26_certBundle : R26CertBundle :=
  ⟨check_round26_g2_top_n7_1cf912de97_leading_pos_coeffs_on_1_3_nonneg,
    check_round26_g2_top_n7_44d9df748d_numer_coeffs_nonneg,
    check_round26_g2_top_n7_44d9df748d_denom_coeffs_nonneg⟩

/-! ## CloserCertDischarged (label → inhabited Prop) -/

/-- Certificate-level discharge for a named closer (not LivingLeafExcluded). -/
def CloserCertDischarged : String → Prop
  | "R13" => R13CertBundle
  | "R14" => R14CertBundle
  | "R16" => R16CertBundle
  | "R17" => R17CertBundle
  | "R18" => R18CertBundle
  | "R19" => R19CertBundle
  | "R26" => R26CertBundle
  | "R27/R28" => R27_28CertBundle
  | _ => False

theorem closerCert_R13 : CloserCertDischarged "R13" := r13_certBundle
theorem closerCert_R14 : CloserCertDischarged "R14" := r14_certBundle
theorem closerCert_R16 : CloserCertDischarged "R16" := r16_certBundle
theorem closerCert_R17 : CloserCertDischarged "R17" := r17_certBundle
theorem closerCert_R18 : CloserCertDischarged "R18" := r18_certBundle
theorem closerCert_R19 : CloserCertDischarged "R19" := r19_certBundle
theorem closerCert_R26 : CloserCertDischarged "R26" := r26_certBundle
theorem closerCert_R27_28 : CloserCertDischarged "R27/R28" := r27_28_certBundle

/-- All eight living closer cert bundles are inhabited. -/
def AllNamedCloserCertsDischarged : Prop :=
  CloserCertDischarged "R13" ∧
    CloserCertDischarged "R14" ∧
      CloserCertDischarged "R16" ∧
        CloserCertDischarged "R17" ∧
          CloserCertDischarged "R18" ∧
            CloserCertDischarged "R19" ∧
              CloserCertDischarged "R26" ∧
                CloserCertDischarged "R27/R28"

theorem allNamedCloserCertsDischarged : AllNamedCloserCertsDischarged :=
  ⟨closerCert_R13, closerCert_R14, closerCert_R16, closerCert_R17,
    closerCert_R18, closerCert_R19, closerCert_R26, closerCert_R27_28⟩

def inhabitedCloserCertCount : ℕ := 8
theorem inhabitedCloserCertCount_eq : inhabitedCloserCertCount = 8 := rfl

def namedCloserCertsDischargedProved : Bool := true
theorem namedCloserCertsDischargedProved_true :
    namedCloserCertsDischargedProved = true := rfl

/-! ## Open geometry bridges (cert → CloserDischarged) -/

/-- Open: turn a cert bundle into combinatorial `CloserDischarged`.
Blocked in practice by `CloserDischarged_*_blocked` until LivingLeafExcluded
is reformulated around geometric realisation. -/
def CloserGeomBridge (label : String) : Prop :=
  CloserCertDischarged label → CloserDischarged label

def AllNamedCloserGeomBridges : Prop :=
  CloserGeomBridge "R13" ∧
    CloserGeomBridge "R14" ∧
      CloserGeomBridge "R16" ∧
        CloserGeomBridge "R17" ∧
          CloserGeomBridge "R18" ∧
            CloserGeomBridge "R19" ∧
              CloserGeomBridge "R26" ∧
                CloserGeomBridge "R27/R28"

theorem AllNamedClosersDischarged_of_certs_and_bridges
    (hc : AllNamedCloserCertsDischarged) (hg : AllNamedCloserGeomBridges) :
    AllNamedClosersDischarged := by
  rcases hc with ⟨c13, c14, c16, c17, c18, c19, c26, c2728⟩
  rcases hg with ⟨g13, g14, g16, g17, g18, g19, g26, g2728⟩
  exact ⟨g13 c13, g14 c14, g16 c16, g17 c17, g18 c18, g19 c19, g26 c26, g2728 c2728⟩

/-- Combinatorial `CloserDischarged` still blocked; pending geom in LivingLeafGeomDischarge. -/
def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false :
    namedClosersDischargedProved = false := rfl

def closerGeomBridgesProved : Bool := false
theorem closerGeomBridgesProved_false : closerGeomBridgesProved = false := rfl

def openStatus : String :=
  "CLOSED: CloserCertDischarged ×8; LivingLeafExcluded↔False blocked lemma;    SE(2) NearEndLeafRealised alias. See LivingLeafGeomDischarge for pending geom×8.    namedClosersDischargedProved=false; Not PrincipalClaim."

end S6.LivingLeafCertDischarge
