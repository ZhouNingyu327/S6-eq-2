import Mathlib.Tactic
import S6Core.GridContribution
import S6Core.CornerBudget
import S6Core.Obligation4M8ShortCap

/-!
# E-tier style lifts — grid numerator + short-cap Bernstein charts

1. **Proved:** on `t ∈ (0,1/2)`, `g2_alg t < 2` via cleared Weierstrass identity.
2. E-tier M8 short-cap Bernstein coefficient vectors nonnegative (`native_decide`).
-/

namespace S6.BernsteinGridLift

open S6.GridContribution
open S6.CornerBudget
open S6.Obligation4M8ShortCap

/-- Helper: `cW` and `sW` clear against `1+t²`. -/
theorem cW_mul (t : ℚ) (h : 1 + t * t ≠ 0) :
    cW t * (1 + t * t) = 1 - t * t := by
  simp only [cW]; field_simp [h]

theorem sW_mul (t : ℚ) (h : 1 + t * t ≠ 0) :
    sW t * (1 + t * t) = 2 * t := by
  simp only [sW]; field_simp [h]

theorem cW_sq_mul (t : ℚ) (h : 1 + t * t ≠ 0) :
    cW t * cW t * (1 + t * t) ^ 2 = (1 - t * t) ^ 2 := by
  have hc := cW_mul t h
  have : cW t * cW t * ((1 + t * t) * (1 + t * t)) =
      (cW t * (1 + t * t)) * (cW t * (1 + t * t)) := by ring
  simpa [pow_two, hc] using this

/-- Cleared identity used by the bridge. -/
theorem g2_alg_bridge_cleared (t : ℚ) (hden : 1 - t * t ≠ 0)
    (hden2 : 1 + t * t ≠ 0) :
    (2 - g2_alg t) * (1 - t * t) ^ 2 = two_minus_g2_num t := by
  -- Write g2_alg = (2 cW - sW)/cW² + t and clear dens by multiplying with cW² (1+t²)²
  have hc := cW_mul t hden2
  have hs := sW_mul t hden2
  have hcsq := cW_sq_mul t hden2
  have hc0 : cW t ≠ 0 := by
    intro h0
    have : 1 - t * t = 0 := by
      calc 1 - t * t = cW t * (1 + t * t) := hc.symm
        _ = 0 := by simp [h0]
    exact hden this
  -- (2c - s)/c² = ((2c-s)*(1+t²)²) / ((1-t²)²) after clearing
  have hquot :
      (2 * cW t - sW t) / (cW t * cW t) =
        ((2 * (1 - t * t) - 2 * t) * (1 + t * t)) / (1 - t * t) ^ 2 := by
    have hnum : (2 * cW t - sW t) * (1 + t * t) ^ 2 =
        (2 * (1 - t * t) - 2 * t) * (1 + t * t) := by
      calc
        (2 * cW t - sW t) * (1 + t * t) ^ 2
            = 2 * (cW t * (1 + t * t)) * (1 + t * t) -
                (sW t * (1 + t * t)) * (1 + t * t) := by ring
        _ = 2 * (1 - t * t) * (1 + t * t) - (2 * t) * (1 + t * t) := by
              simp [hc, hs]
        _ = (2 * (1 - t * t) - 2 * t) * (1 + t * t) := by ring
    have hden' : cW t * cW t * (1 + t * t) ^ 2 = (1 - t * t) ^ 2 := hcsq
    -- a/b = c/d from a*d = c*b after clearing with (1+t²)²
    have hb0 : cW t * cW t ≠ 0 := mul_ne_zero hc0 hc0
    have hd0 : (1 - t * t) ^ 2 ≠ 0 := pow_ne_zero 2 hden
    have hscale : (1 + t * t) ^ 2 ≠ 0 := pow_ne_zero 2 hden2
    -- (2c-s)/c² = [ (2c-s)(1+t²)² ] / [ c² (1+t²)² ] = num' / (1-t²)²
    calc
      (2 * cW t - sW t) / (cW t * cW t)
          = ((2 * cW t - sW t) * (1 + t * t) ^ 2) /
              (cW t * cW t * (1 + t * t) ^ 2) := by
            field_simp [hb0, hscale]
      _ = ((2 * (1 - t * t) - 2 * t) * (1 + t * t)) / (1 - t * t) ^ 2 := by
            rw [hnum, hden']
  -- Now g2_alg = that + t
  have hg : g2_alg t =
      ((2 * (1 - t * t) - 2 * t) * (1 + t * t)) / (1 - t * t) ^ 2 + t := by
    simp only [g2_alg]
    simpa using hquot
  -- Finish: (2 - (A/(1-t²)² + t)) * (1-t²)² = 2(1-t²)² - A - t(1-t²)²
  set A : ℚ := (2 * (1 - t * t) - 2 * t) * (1 + t * t)
  set D : ℚ := (1 - t * t) ^ 2
  have hD : D ≠ 0 := pow_ne_zero 2 hden
  have hg' : g2_alg t = A / D + t := by simpa [A, D] using hg
  rw [hg']
  have hclear : (2 - (A / D + t)) * D = 2 * D - A - t * D := by
    field_simp [hD]; ring
  rw [hclear]
  simp only [two_minus_g2_num, g2_num, A, D]
  ring

theorem g2_alg_bridge_identity (t : ℚ) (hden : 1 - t * t ≠ 0)
    (hden2 : 1 + t * t ≠ 0) :
    2 - g2_alg t = two_minus_g2_num t / (1 - t * t) ^ 2 := by
  have hclr := g2_alg_bridge_cleared t hden hden2
  exact (eq_div_iff (pow_ne_zero 2 hden)).2 hclr

def G2AlgBridge (t : ℚ) : Prop :=
  (1 - t * t) ≠ 0 →
    2 - g2_alg t = two_minus_g2_num t / (1 - t * t) ^ 2

theorem G2AlgBridge_holds (t : ℚ) (hden2 : 1 + t * t ≠ 0) : G2AlgBridge t :=
  fun hden => g2_alg_bridge_identity t hden hden2

theorem g2_alg_lt_two (t : ℚ) (ht0 : 0 < t) (ht : t < 1 / 2) :
    g2_alg t < 2 := by
  have ht1 : t < 1 := lt_trans ht (by norm_num : (1:ℚ)/2 < 1)
  have ht0' : 0 ≤ t := le_of_lt ht0
  have habs : |t| < 1 := by simpa [abs_of_nonneg ht0'] using ht1
  have hden_pos := one_minus_t_sq_pos t habs
  have htt : t * t < 1 := by nlinarith [ht0, ht]
  have hden_ne : (1 - t * t) ≠ 0 := ne_of_gt (by linarith [htt])
  have hden2 : 1 + t * t ≠ 0 := by nlinarith [mul_self_nonneg t]
  have hid := g2_alg_bridge_identity t hden_ne hden2
  have hnum := two_minus_g2_num_pos t ht0 ht
  have hpos : 0 < 2 - g2_alg t := by
    rw [hid]; exact div_pos hnum hden_pos
  linarith

theorem g2_alg_lt_two_of_bridge (t : ℚ) (ht0 : 0 < t) (ht : t < 1 / 2)
    (_hbr : G2AlgBridge t) :
    g2_alg t < 2 :=
  g2_alg_lt_two t ht0 ht

theorem g2_num_pos_two_fifths' : 0 < g2_num (2 / 5) := g2_num_pos_two_fifths

theorem e_tier_small_a_cosine_nonneg :
    nonnegList coeffs_small_a_cosine_envelope = true :=
  coeffs_small_a_cosine_envelope_nonneg

theorem e_tier_Ka_le_1_short_leg_nonneg :
    nonnegList coeffs_Ka_le_1_short_leg_envelope = true :=
  coeffs_Ka_le_1_short_leg_envelope_nonneg

theorem bernstein_weight_nonneg (u : ℚ) (i k : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ u ^ i * (1 - u) ^ k :=
  pow_basis_nonneg u i k hu0 hu1

def gridLiftClosed : Bool := true
theorem gridLiftClosed_true : gridLiftClosed = true := rfl

def openG2AlgGeometryBridge : String :=
  "CLOSED algebraically: g2_alg_bridge_identity / g2_alg_lt_two. \
   Geometric reading of g2_alg as Euclidean two-axis chord sum is modelling."

end S6.BernsteinGridLift
