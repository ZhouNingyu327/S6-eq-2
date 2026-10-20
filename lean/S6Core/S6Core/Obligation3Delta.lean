import Mathlib.Tactic

/-!
# Obligation 3 — δ long-leg protrusion (R29 bridge)

`δ(z) = 2z²/(1−z²)`. Manuscript: `δ(4/15)=32/209<1/6`
(`small/S6_attack_round29.md` eq.(3)).
-/

namespace S6.Obligation3Delta

def delta (z : ℚ) : ℚ := (2 * z * z) / (1 - z * z)

theorem delta_four_fifteenths :
    delta (4 / 15) = (32 : ℚ) / 209 := by
  simp only [delta]; norm_num

theorem delta_four_fifteenths_lt_one_sixth :
    delta (4 / 15) < (1 : ℚ) / 6 := by
  rw [delta_four_fifteenths]; norm_num

theorem delta_nonneg_of_mem_Ico (z : ℚ) (_h0 : 0 ≤ z) (h1 : z < 1) :
    0 ≤ delta z := by
  have hden : 0 < 1 - z * z := by nlinarith [mul_self_nonneg z]
  exact div_nonneg (by nlinarith [mul_self_nonneg z]) (le_of_lt hden)

def o3_deltaConstantClosed : Bool := true
theorem o3_deltaConstantClosed_true : o3_deltaConstantClosed = true := rfl

end S6.Obligation3Delta
