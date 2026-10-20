import Mathlib.Tactic

/-!
# Obligation 4 — M10 / R43 small-angle dual-direct (η≤1/8)

Bernstein certificate from `round43_certificate.json` (map a=v/3).

## 已证
* Numerator/denominator Bernstein coeffs nonnegative
* Interval gate `0 ≤ η ≤ 1/8`

## Residual
* Full geometric dual-direct exclusion on η∈[0,1/8] for both rotations
-/

namespace S6.Obligation4M10

def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

theorem eta_small_interval_width :
    (0 : ℚ) < (1 : ℚ) / 8 - 0 := by norm_num

theorem eta_small_le_one_third :
    (1 : ℚ) / 8 < 1 / 3 := by norm_num

/-- R43 numerator Bernstein coeffs (deg 9). -/
def coeffs_numerator : List ℚ := [(34 : ℚ), (731 : ℚ)/27, (1661 : ℚ)/81, (16613 : ℚ)/1134, (16607 : ℚ)/1701, (60997 : ℚ)/10206, (50317 : ℚ)/15309, (10325 : ℚ)/6561, (12608 : ℚ)/19683, (5200 : ℚ)/19683]
theorem coeffs_numerator_nonneg : nonnegList coeffs_numerator = true := by
  native_decide

/-- R43 denominator Bernstein coeffs (deg 9). -/
def coeffs_denominator : List ℚ := [(40 : ℚ), (1060 : ℚ)/27, (340 : ℚ)/9, (6730 : ℚ)/189, (167660 : ℚ)/5103, (454130 : ℚ)/15309, (14860 : ℚ)/567, (148700 : ℚ)/6561, (1133440 : ℚ)/59049, (313600 : ℚ)/19683]
theorem coeffs_denominator_nonneg : nonnegList coeffs_denominator = true := by
  native_decide

def o4_m10_bernsteinClosed : Bool := true
theorem o4_m10_bernsteinClosed_true : o4_m10_bernsteinClosed = true := rfl

def open_m10_small_angle_exclusion : String :=
  "Bernstein coeffs closed; full η≤1/8 dual-direct geometry open."

end S6.Obligation4M10
