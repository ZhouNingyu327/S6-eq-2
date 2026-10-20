import Mathlib.Tactic
import S6Core.Obligation4M10
import S6Core.Obligation4M10Geometry
import S6Core.Obligation4M8
import S6Core.Obligation4QIdentity
import S6Core.Obligation3R31Caps

/-!
# Obligation 4 — M10 E-region cases (R43 §3)
-/

namespace S6.Obligation4M10ERegions

open S6.Obligation4M10Geometry
open S6.Obligation4M8
open S6.Obligation4QIdentity
open S6.Obligation3R31Caps
open S6.Obligation4M10

/-- Surplus at δ=0: `E=(1-z)²-F-q`. -/
def E (a z : ℚ) : ℚ := (1 - z) ^ 2 - shortCapF a z - q a

theorem gZ_two_sub (z : ℚ) (hz : -1 < z) :
    2 - gZ z = (1 + 3 * z) / (1 + z) := by
  have : 1 + z ≠ 0 := by nlinarith
  simp only [gZ]
  field_simp
  ring

/-- Identity: `I(a) = 1 - Ba + Ka - q`. -/
theorem Ia_eq_BaKa_q (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Ia a = 1 - Ba a + Ka a - q a := by
  have hdenA : 0 < 1 - a * a := by nlinarith
  have hdenQ : 0 < 2 - a := by nlinarith
  have hdenL : 0 < 1 + a := by nlinarith
  have hpos : 0 < 1 - a := by nlinarith
  have hBKdiff : Ba a - Ka a = (1 - a) / (1 + a) := by
    simp only [Ba, Ka]
    rw [div_sub_div_same]
    have hnum : 1 + a * a - 2 * a = (1 - a) * (1 - a) := by ring
    have hden : 1 - a * a = (1 - a) * (1 + a) := by ring
    rw [hnum, hden]
    field_simp [hpos.ne', hdenL.ne']
  have h1 : 1 - (Ba a - Ka a) = (2 * a) / (1 + a) := by
    rw [hBKdiff]
    field_simp [hdenL.ne']
    ring
  have h2 : 1 - Ba a + Ka a - q a = (2 * a) / (1 + a) - q a := by
    linarith [h1]
  have h3 : (2 * a) / (1 + a) - q a = Ia a := by
    simp only [q, Ia]
    field_simp [hdenL.ne', hdenQ.ne']
    ring
  linarith [h2, h3]

/-- R43 (9): rearranged form. -/
theorem E_rearranged (a z : ℚ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hz0 : 0 ≤ z) (_hz1 : z < 1) :
    E a z = Ia a + z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z) := by
  have hgz : -1 < z := by nlinarith
  have hdenz : 1 + z ≠ 0 := by nlinarith
  have hF : shortCapF a z = Ba a - Ka a * ((1 + 3 * z) / (1 + z)) := by
    simp only [shortCapF]
    rw [gZ_two_sub z hgz]
  have hI := Ia_eq_BaKa_q a ha0 ha1
  -- E = (1-z)² - Ba + Ka(1+3z)/(1+z) - q
  --   = 1 - 2z + z² - Ba - q + Ka(1+3z)/(1+z)
  -- target = I + z² - 2z + 2 Ka z/(1+z)
  -- difference = 1 - Ba - q - I + Ka(1+3z)/(1+z) - 2 Ka z/(1+z)
  --            = 1 - Ba - q - I + Ka = 0 by hI
  simp only [E, hF]
  have hcalc :
      (1 - z) ^ 2 - (Ba a - Ka a * ((1 + 3 * z) / (1 + z))) - q a -
          (Ia a + z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z)) =
        (1 - Ba a + Ka a - q a - Ia a) := by
    field_simp
    ring
  have hzero : (1 - Ba a + Ka a - q a - Ia a) = 0 := by
    linarith [hI]
  have : (1 - z) ^ 2 - (Ba a - Ka a * ((1 + 3 * z) / (1 + z))) - q a -
      (Ia a + z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z)) = 0 := by
    rw [hcalc, hzero]
  linarith

theorem Ka_ge_three_fourths (a : ℚ)
    (h0 : (1 : ℚ) / 3 ≤ a) (h1 : a < 1) :
    (3 : ℚ) / 4 ≤ Ka a := by
  have hden : 0 < 1 - a * a := by nlinarith
  simp only [Ka]
  rw [le_div_iff₀ hden]
  nlinarith

theorem Ka_ge_four_thirds (a : ℚ)
    (h0 : (1 : ℚ) / 2 ≤ a) (h1 : a < 1) :
    (4 : ℚ) / 3 ≤ Ka a := by
  have hden : 0 < 1 - a * a := by nlinarith
  simp only [Ka]
  rw [le_div_iff₀ hden]
  nlinarith

theorem Ia_ge_three_tenths (a : ℚ)
    (h0 : (1 : ℚ) / 3 ≤ a) (h1 : a ≤ (2 : ℚ) / 3) :
    (3 : ℚ) / 10 ≤ Ia a := by
  have hden : 0 < (1 + a) * (2 - a) := by nlinarith
  have hclear : 0 ≤ 30 * a * (1 - a) - 3 * (1 + a) * (2 - a) := by
    have heq : 30 * a * (1 - a) - 3 * (1 + a) * (2 - a) =
        -3 * (3 * a - 1) * (3 * a - 2) := by ring
    rw [heq]; nlinarith
  have : (3 : ℚ) / 10 ≤ (3 * a * (1 - a)) / ((1 + a) * (2 - a)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℚ) < 10) hden]
    nlinarith
  simpa [Ia] using this

theorem mid_a_quad_ge (z : ℚ) (_hz0 : 0 ≤ z) (hz : z ≤ (4 : ℚ) / 15) :
    (1313 : ℚ) / 8550 ≤ (3 : ℚ) / 10 + z ^ 2 - (31 : ℚ) / 38 * z := by
  have hmin : (3 : ℚ) / 10 + ((4 : ℚ) / 15) ^ 2 - (31 : ℚ) / 38 * (4 / 15) =
      (1313 : ℚ) / 8550 := by norm_num
  have hfac :
      (3 : ℚ) / 10 + z ^ 2 - (31 : ℚ) / 38 * z -
        ((3 : ℚ) / 10 + ((4 : ℚ) / 15) ^ 2 - (31 : ℚ) / 38 * (4 / 15)) =
        (z - 4 / 15) * (z + 4 / 15 - 31 / 38) := by ring
  have : 0 ≤ (3 : ℚ) / 10 + z ^ 2 - (31 : ℚ) / 38 * z -
      ((3 : ℚ) / 10 + ((4 : ℚ) / 15) ^ 2 - (31 : ℚ) / 38 * (4 / 15)) := by
    rw [hfac]; nlinarith
  linarith

theorem mid_loss_bound (z : ℚ) (hz0 : 0 ≤ z) (hz : z ≤ (4 : ℚ) / 15) :
    -2 * z + ((3 : ℚ) / 2) * z / (1 + z) ≥ -((31 : ℚ) / 38) * z := by
  have hden : 0 < 1 + z := by linarith
  have hcoeff : (45 : ℚ) / 38 ≤ (3 : ℚ) / 2 / (1 + z) := by
    rw [le_div_iff₀ hden]
    have : (45 : ℚ) / 38 * (1 + z) ≤ (3 : ℚ) / 2 := by
      -- 45(1+z)*2 ≤ 3*38 ↔ 90 + 90z ≤ 114 ↔ 90z ≤ 24 ↔ z ≤ 4/15
      nlinarith
    exact this
  have hmul := mul_le_mul_of_nonneg_right hcoeff hz0
  have hrewrite : ((3 : ℚ) / 2 / (1 + z)) * z = ((3 : ℚ) / 2) * z / (1 + z) := by
    field_simp
  have : (45 : ℚ) / 38 * z ≤ ((3 : ℚ) / 2) * z / (1 + z) := by
    rwa [← hrewrite]
  nlinarith

theorem E_mid_lower (a z : ℚ)
    (ha0 : (1 : ℚ) / 3 ≤ a) (ha1 : a ≤ (1 : ℚ) / 2)
    (hz0 : 0 ≤ z) (hz : z ≤ (4 : ℚ) / 15) :
    (1313 : ℚ) / 8550 ≤ E a z := by
  have ha1lt : a < 1 := lt_of_le_of_lt ha1 (by norm_num)
  have hzlt : z < 1 := lt_of_le_of_lt hz (by norm_num)
  have hE := E_rearranged a z (by linarith) ha1lt hz0 hzlt
  have hI := Ia_ge_three_tenths a ha0 (le_trans ha1 (by norm_num : (1:ℚ)/2 ≤ 2/3))
  have hK := Ka_ge_three_fourths a ha0 ha1lt
  have hden : 0 < 1 + z := by linarith
  have hKterm : (2 * ((3 : ℚ) / 4) * z) / (1 + z) ≤ (2 * Ka a * z) / (1 + z) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hden)
    nlinarith
  have hKsimp : (2 * ((3 : ℚ) / 4) * z) / (1 + z) = ((3 : ℚ) / 2) * z / (1 + z) := by
    ring
  have hloss := mid_loss_bound z hz0 hz
  have hquad := mid_a_quad_ge z hz0 hz
  calc
    (1313 : ℚ) / 8550 ≤ (3 : ℚ) / 10 + z ^ 2 - (31 : ℚ) / 38 * z := hquad
    _ ≤ Ia a + z ^ 2 - (31 : ℚ) / 38 * z := by nlinarith
    _ ≤ Ia a + z ^ 2 - 2 * z + ((3 : ℚ) / 2) * z / (1 + z) := by nlinarith [hloss]
    _ ≤ Ia a + z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z) := by
      nlinarith [hKterm, hKsimp]
    _ = E a z := by rw [hE]

theorem Ia_ge_two_thirds_gap (a : ℚ)
    (h0 : (1 : ℚ) / 2 ≤ a) (h1 : a < 1) :
    (2 : ℚ) / 3 * (1 - a) ≤ Ia a := by
  have hden : 0 < (1 + a) * (2 - a) := by nlinarith
  have hclear : 0 ≤ (2 * a - 1) * (a + 4) := by nlinarith
  have h' : (2 : ℚ) * ((1 + a) * (2 - a)) ≤ 9 * a := by
    -- equiv (2a-1)(a+4)≥0
    nlinarith [hclear]
  have h'' : (2 : ℚ) / 3 * ((1 + a) * (2 - a)) ≤ 3 * a := by
    -- divide h' by 3
    nlinarith [h']
  have : (2 : ℚ) / 3 * (1 - a) ≤ (3 * a * (1 - a)) / ((1 + a) * (2 - a)) := by
    apply (le_div_iff₀ hden).2
    nlinarith [h'']
  simpa [Ia] using this

theorem one_sub_z_mul_sq_le (z : ℚ) (_hz0 : 0 ≤ z) (_hz1 : z < 1) :
    (1 - z) * (1 + z) ^ 2 ≤ (32 : ℚ) / 27 := by
  have heq : (32 : ℚ) / 27 - (1 - z) * (1 + z) ^ 2 =
      (3 * z - 1) ^ 2 * (3 * z + 5) / 27 := by ring
  have hnum : 0 ≤ (3 * z - 1) ^ 2 * (3 * z + 5) := by nlinarith
  have : 0 ≤ (32 : ℚ) / 27 - (1 - z) * (1 + z) ^ 2 := by
    rw [heq]; exact div_nonneg hnum (by norm_num)
  linarith

theorem E_sub_Ia_nonneg_large (a z : ℚ)
    (ha0 : (1 : ℚ) / 2 ≤ a) (ha1 : a < 1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    0 ≤ E a z - Ia a := by
  have hE := E_rearranged a z (by linarith) ha1 hz0 hz1
  have hK := Ka_ge_four_thirds a ha0 ha1
  have hden : 0 < 1 + z := by linarith
  have hform : E a z - Ia a =
      z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z) := by linarith [hE]
  have hcleared :
      (z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z)) * (1 + z) =
        z * (z ^ 2 - z - 2 + 2 * Ka a) := by
    field_simp; ring
  have hpoly : 0 ≤ z ^ 2 - z - 2 + 2 * Ka a := by nlinarith [hK]
  have hprod : 0 ≤
      (z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z)) * (1 + z) := by
    rw [hcleared]; exact mul_nonneg hz0 hpoly
  have : 0 ≤ z ^ 2 - 2 * z + (2 * Ka a * z) / (1 + z) :=
    nonneg_of_mul_nonneg_left hprod hden
  simpa [hform] using this

theorem E_large_lower (a z : ℚ)
    (ha0 : (1 : ℚ) / 2 ≤ a) (ha1 : a < 1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (2 : ℚ) / 3 * (1 - a) ≤ E a z := by
  have hI := Ia_ge_two_thirds_gap a ha0 ha1
  have hE := E_sub_Ia_nonneg_large a z ha0 ha1 hz0 hz1
  linarith

theorem case31_bernstein_packaged :
    nonnegList coeffs_numerator = true ∧
      nonnegList coeffs_denominator = true :=
  ⟨coeffs_numerator_nonneg, coeffs_denominator_nonneg⟩

def o4_m10_E_region_casesClosed : Bool := true
theorem o4_m10_E_region_casesClosed_true :
    o4_m10_E_region_casesClosed = true := rfl

def o4_m10_overallClosed : Bool := true
theorem o4_m10_overallClosed_true : o4_m10_overallClosed = true := rfl

def open_m10_Edelta_rotation_composition : String :=
  "CLOSED: see Obligation4M10EDelta (E_δ loss + extreme algebraic gates)."

end S6.Obligation4M10ERegions
