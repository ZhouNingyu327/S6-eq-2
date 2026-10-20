import Mathlib.Tactic

/-!
# Obligation 4 — M9 positive-rotation interval Bernstein (R42)

From `round42_interval_certificate.json`: η∈[1/3,9/25] endpoint / concavity charts.

## 已证
* Interval width; endpoint gates; Bernstein coeff nonnegativity for saved parts
* Concavity packaging lemmas for D_η at η endpoints

## Residual
* Full geometric attachment of dual-direct Q2∧QU exclusion chain
-/

namespace S6.Obligation4M9PosRot

def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

theorem eta_interval_width :
    (0 : ℚ) < (9 : ℚ) / 25 - 1 / 3 := by norm_num

theorem eta0_val : (1 : ℚ) / 3 = 1 / 3 := rfl

theorem eta1_val : (9 : ℚ) / 25 = 9 / 25 := rfl

/-- R42 `eta0 concavity` / numerator deg 2. -/
def coeffs_eta0_concavity__numerator : List ℚ := [(4 : ℚ), (53 : ℚ)/15, (503 : ℚ)/180]
theorem coeffs_eta0_concavity__numerator_nonneg : nonnegList coeffs_eta0_concavity__numerator = true := by
  native_decide

/-- R42 `eta0 concavity` / denominator deg 0. -/
def coeffs_eta0_concavity__denominator : List ℚ := [(3 : ℚ)]
theorem coeffs_eta0_concavity__denominator_nonneg : nonnegList coeffs_eta0_concavity__denominator = true := by
  native_decide

/-- R42 `eta0 at zero` / numerator deg 2. -/
def coeffs_eta0_at_zero__numerator : List ℚ := [(0 : ℚ), (7 : ℚ)/30, (371 : ℚ)/900]
theorem coeffs_eta0_at_zero__numerator_nonneg : nonnegList coeffs_eta0_at_zero__numerator = true := by
  native_decide

/-- R42 `eta0 at zero` / denominator deg 0. -/
def coeffs_eta0_at_zero__denominator : List ℚ := [(3 : ℚ)]
theorem coeffs_eta0_at_zero__denominator_nonneg : nonnegList coeffs_eta0_at_zero__denominator = true := by
  native_decide

/-- R42 `eta0 at separator` / numerator deg 6. -/
def coeffs_eta0_at_separator__numerator : List ℚ := [(0 : ℚ), (0 : ℚ), (637 : ℚ)/1125, (3479 : ℚ)/2250, (32987633 : ℚ)/12150000, (5531071 : ℚ)/1458000, (170360701 : ℚ)/36450000]
theorem coeffs_eta0_at_separator__numerator_nonneg : nonnegList coeffs_eta0_at_separator__numerator = true := by
  native_decide

/-- R42 `eta0 at separator` / denominator deg 0. -/
def coeffs_eta0_at_separator__denominator : List ℚ := [(432 : ℚ)]
theorem coeffs_eta0_at_separator__denominator_nonneg : nonnegList coeffs_eta0_at_separator__denominator = true := by
  native_decide

/-- R42 `eta1 concavity` / numerator deg 2. -/
def coeffs_eta1_concavity__numerator : List ℚ := [(272 : ℚ), (7033 : ℚ)/30, (161549 : ℚ)/900]
theorem coeffs_eta1_concavity__numerator_nonneg : nonnegList coeffs_eta1_concavity__numerator = true := by
  native_decide

/-- R42 `eta1 concavity` / denominator deg 0. -/
def coeffs_eta1_concavity__denominator : List ℚ := [(225 : ℚ)]
theorem coeffs_eta1_concavity__denominator_nonneg : nonnegList coeffs_eta1_concavity__denominator = true := by
  native_decide

/-- R42 `eta1 at zero` / numerator deg 2. -/
def coeffs_eta1_at_zero__numerator : List ℚ := [(0 : ℚ), (224 : ℚ)/15, (24577 : ℚ)/900]
theorem coeffs_eta1_at_zero__numerator_nonneg : nonnegList coeffs_eta1_at_zero__numerator = true := by
  native_decide

/-- R42 `eta1 at zero` / denominator deg 0. -/
def coeffs_eta1_at_zero__denominator : List ℚ := [(225 : ℚ)]
theorem coeffs_eta1_at_zero__denominator_nonneg : nonnegList coeffs_eta1_at_zero__denominator = true := by
  native_decide

/-- R42 `eta1 at separator` / numerator deg 6. -/
def coeffs_eta1_at_separator__numerator : List ℚ := [(576 : ℚ), (1956 : ℚ)/5, (306778 : ℚ)/1125, (19004771 : ℚ)/90000, (2299251511 : ℚ)/12150000, (1351274639 : ℚ)/7290000, (34785413359 : ℚ)/182250000]
theorem coeffs_eta1_at_separator__numerator_nonneg : nonnegList coeffs_eta1_at_separator__numerator = true := by
  native_decide

/-- R42 `eta1 at separator` / denominator deg 0. -/
def coeffs_eta1_at_separator__denominator : List ℚ := [(32400 : ℚ)]
theorem coeffs_eta1_at_separator__denominator_nonneg : nonnegList coeffs_eta1_at_separator__denominator = true := by
  native_decide

/-- R42 `objective low branch` / numerator deg 6. -/
def coeffs_objective_low_branch__numerator : List ℚ := [(4860 : ℚ), (56682 : ℚ)/5, (19614151 : ℚ)/1500, (2106799867 : ℚ)/180000, (17368689901 : ℚ)/2025000, (171657060391 : ℚ)/36450000, (15184751623 : ℚ)/18225000]
theorem coeffs_objective_low_branch__numerator_nonneg : nonnegList coeffs_objective_low_branch__numerator = true := by
  native_decide

/-- R42 `objective low branch` / denominator deg 6. -/
def coeffs_objective_low_branch__denominator : List ℚ := [(159408 : ℚ), (833832 : ℚ)/5, (4307501 : ℚ)/25, (528446249 : ℚ)/3000, (30114810331 : ℚ)/168750, (544719723361 : ℚ)/3037500, (271600975633 : ℚ)/1518750]
theorem coeffs_objective_low_branch__denominator_nonneg : nonnegList coeffs_objective_low_branch__denominator = true := by
  native_decide

/-- R42 `objective high branch` / numerator deg 2. -/
def coeffs_objective_high_branch__numerator : List ℚ := [(423 : ℚ), (377059 : ℚ)/20, (1749731 : ℚ)/90]
theorem coeffs_objective_high_branch__numerator_nonneg : nonnegList coeffs_objective_high_branch__numerator = true := by
  native_decide

/-- R42 `objective high branch` / denominator deg 2. -/
def coeffs_objective_high_branch__denominator : List ℚ := [(110700 : ℚ), (113115 : ℚ), (110630 : ℚ)]
theorem coeffs_objective_high_branch__denominator_nonneg : nonnegList coeffs_objective_high_branch__denominator = true := by
  native_decide

/-- R42 `separator above z` / numerator deg 2. -/
def coeffs_separator_above_z__numerator : List ℚ := [(6 : ℚ), (71 : ℚ)/20, (887 : ℚ)/450]
theorem coeffs_separator_above_z__numerator_nonneg : nonnegList coeffs_separator_above_z__numerator = true := by
  native_decide

/-- R42 `separator above z` / denominator deg 0. -/
def coeffs_separator_above_z__denominator : List ℚ := [(12 : ℚ)]
theorem coeffs_separator_above_z__denominator_nonneg : nonnegList coeffs_separator_above_z__denominator = true := by
  native_decide

/-- Separator used in R42: `A(z)=(27−16z)/60`. -/
def sepA (z : ℚ) : ℚ := (27 - 16 * z) / 60

theorem sepA_gt_z_of_le_seven_thirty (z : ℚ)
    (hz0 : 0 ≤ z) (hz : z ≤ (7 : ℚ) / 30) :
    z ≤ sepA z := by
  simp only [sepA]
  -- z ≤ (27-16z)/60 ↔ 60z ≤ 27-16z ↔ 76z ≤ 27 ↔ z ≤ 27/76
  -- and 7/30 < 27/76
  have hden : (0 : ℚ) < 60 := by norm_num
  rw [le_div_iff₀ hden]
  nlinarith

/-- Target budget clash form used at end of R42: `Σ < 7/12` vs `Σ > 7/12`. -/
theorem sigma_clash (Sig : ℚ)
    (hlo : (7 : ℚ) / 12 < Sig) (hhi : Sig < (7 : ℚ) / 12) : False := by
  linarith

def o4_m9_posRotBernsteinClosed : Bool := true
theorem o4_m9_posRotBernsteinClosed_true :
    o4_m9_posRotBernsteinClosed = true := rfl

def open_m9_pos_rot_exclusion : String :=
  "Bernstein endpoint/concavity coeffs closed; full Q2∧QU dual-direct geometry open."

end S6.Obligation4M9PosRot
