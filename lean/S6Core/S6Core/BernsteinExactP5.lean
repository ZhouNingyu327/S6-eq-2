import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

/-!
# Exact-cert lifts — P5 (budget / Or / opposite / cascade hands)

Lifts numeric coefficient payloads from P5 hand certificates and records
elementary rational lemmas used by AM-GM / Bernstein budget arguments.

Honest: payload + elementary lemmas ≠ PrincipalClaim unconditional.
-/

namespace S6.BernsteinExactP5

def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

def nonposList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (c ≤ 0) && nonposList cs

def posList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 < c) && posList cs

/-- AM-GM kernel: `(c - s)² ≥ 0` ⇒ `c/s + s/c ≥ 2` for `c,s > 0`. Cleared form. -/
theorem amgm_cleared (c s : ℚ) : 0 ≤ (c - s) * (c - s) :=
  mul_self_nonneg (c - s)

theorem amgm_cs_sum_sq (c s : ℚ) :
    c * c + s * s ≥ 2 * c * s := by
  nlinarith [amgm_cleared c s]

/-- Bernstein numer for `4 - 5h - h²` on `[0,1/2]` (g25 U-t casesplit). -/
def bernstein_4_5h_h2 : List ℚ :=
  [(4 : ℚ), (11 : ℚ)/4, (5 : ℚ)/4]

theorem bernstein_4_5h_h2_nonneg : nonnegList bernstein_4_5h_h2 = true := by
  native_decide


/-- P5 `check_round24_g3_cside__n9__b12141227f.json` / exact-hand-both-axis-disc / leading_pos_coeffs_on_[1,3] -/
def check_round24_g3_cside_n9_b12141227f_leading_pos_coeffs_on_1_3 : List ℚ :=
  [(0 : ℚ), (16 : ℚ)]
theorem check_round24_g3_cside_n9_b12141227f_leading_pos_coeffs_on_1_3_nonneg : nonnegList check_round24_g3_cside_n9_b12141227f_leading_pos_coeffs_on_1_3 = true := by native_decide

/-- P5 `check_round25_g3_complete__n12__35a3a52b42.json` / exact-hand-g25-U-t-casesplit / bernstein_4_5h_h2 -/
def check_round25_g3_complete_n12_35a3a52b42_bernstein_4_5h_h2 : List ℚ :=
  [(4 : ℚ), (11 : ℚ)/4, (5 : ℚ)/4]
theorem check_round25_g3_complete_n12_35a3a52b42_bernstein_4_5h_h2_nonneg : nonnegList check_round25_g3_complete_n12_35a3a52b42_bernstein_4_5h_h2 = true := by native_decide

/-- P5 `check_round26_g2_top__n7__1cf912de97.json` / exact-hand-both-axis-disc / leading_pos_coeffs_on_[1,3] -/
def check_round26_g2_top_n7_1cf912de97_leading_pos_coeffs_on_1_3 : List ℚ :=
  [(0 : ℚ), (16 : ℚ)]
theorem check_round26_g2_top_n7_1cf912de97_leading_pos_coeffs_on_1_3_nonneg : nonnegList check_round26_g2_top_n7_1cf912de97_leading_pos_coeffs_on_1_3 = true := by native_decide

/-- P5 `check_round28_g2_near_complete__n6__4094708312.json` / exact-hand-r28-ld-2w / gap_coeffs -/
def check_round28_g2_near_complete_n6_4094708312_gap_coeffs : List ℚ :=
  [(0 : ℚ), (-2 : ℚ), (0 : ℚ)]
theorem check_round28_g2_near_complete_n6_4094708312_gap_coeffs_nonpos : nonposList check_round28_g2_near_complete_n6_4094708312_gap_coeffs = true := by native_decide

def p5CatalogCount : ℕ := 60
theorem p5CatalogCount_eq : p5CatalogCount = 60 := rfl
def p5NumericLiftCount : ℕ := 4
theorem p5NumericLiftCount_eq : p5NumericLiftCount = 4 := rfl
def bernsteinExactP5Closed : Bool := true
theorem bernsteinExactP5Closed_true : bernsteinExactP5Closed = true := rfl
def openStatus : String :=
  "CLOSED: P5 numeric coeff payloads + AM-GM cleared form. Not PrincipalClaim."
end S6.BernsteinExactP5
