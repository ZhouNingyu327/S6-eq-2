import S6Core.Obligation4M9Incidence
import S6Core.Obligation4M9Ownership
import S6Core.Obligation4M9PosRot
import Mathlib.Tactic
import S6Core.Obligation4M8

/-!
# Obligation 4 — M9 / R42 simplest fragments

Round 42: normalised seam point (μ-free) + positive-rotation interval exclusion.

## 已证
* Shared bottom budget `Σ > 7/12` from `Σ > 2−√2` surrogate comparison
* Weierstrass/Ka/Ba/gZ symbols reused from M8
* Interval gate `1/3 ≤ η ≤ 9/25` width positive

## Residual
* Full positive-rotation η∈[1/3,9/25] exclusion geometry
* μ-free seam point incidence
-/

namespace S6.Obligation4M9

open S6.Obligation4M8

/-- Rational lower bound used throughout R39–R42: `2−√2 > 7/12`. -/
theorem two_sub_sqrt2_gt_seven_twelfths (s : ℚ) (hs2 : s * s = 2) (hs0 : 0 < s) :
    (7 : ℚ) / 12 < 2 - s := by
  -- Equivalent: s < 2 - 7/12 = 17/12, and (17/12)² > 2 already proved
  have h : s < (17 : ℚ) / 12 := by
    have : s * s < ((17 : ℚ) / 12) ^ 2 := by
      have := seventeen_twelfths_sq_gt_two
      nlinarith [hs2]
    nlinarith [hs0]
  linarith

theorem sigma_gt_seven_twelfths_of_diameter (mu Sig s : ℚ)
    (hmu : 1 < mu) (hs2 : s * s = 2) (hs0 : 0 < s)
    (hbud : 2 * mu - Sig ≤ s) :
    (7 : ℚ) / 12 < Sig := by
  have h1 : 2 - s < Sig := by
    have : 2 * mu - s ≤ Sig := by linarith
    have : 2 - s < 2 * mu - s := by linarith
    linarith
  have h2 := two_sub_sqrt2_gt_seven_twelfths s hs2 hs0
  linarith

/-- Positive-rotation exclusion interval has positive length. -/
theorem pos_rot_eta_interval_width :
    (0 : ℚ) < (9 : ℚ) / 25 - 1 / 3 := by norm_num

/-- Small-angle box from R41/R42 input. -/
theorem r42_z_box_nonempty :
    (0 : ℚ) < (4 : ℚ) / 15 := by norm_num

def o4_m9_budgetGatesClosed : Bool := true
theorem o4_m9_budgetGatesClosed_true : o4_m9_budgetGatesClosed = true := rfl

def open_m9_pos_rot_exclusion : String :=
  "Dual-direct algebra+normalized incidence closed; residual: μ-world bridge."

end S6.Obligation4M9
