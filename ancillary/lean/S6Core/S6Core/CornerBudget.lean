import Mathlib.Tactic

/-!
# Corner grid budget algebraic core (lemma 3 Weierstrass form)
-/

namespace S6.CornerBudget

def g2_num (t : ℚ) : ℚ := (1 - 2 * t) ^ 2 + t ^ 3 * (4 - t)

theorem g2_num_expand (t : ℚ) :
    g2_num t = 1 - 4 * t + 4 * t ^ 2 + 4 * t ^ 3 - t ^ 4 := by
  simp only [g2_num]; ring

theorem g2_num_pos_of_lt_half (t : ℚ) (ht0 : 0 < t) (ht : t < 1/2) :
    0 < g2_num t := by
  have h1 : 0 < 1 - 2 * t := by linarith
  have hsq : 0 < (1 - 2 * t) ^ 2 := sq_pos_of_pos h1
  have ht3 : 0 < t ^ 3 := pow_pos ht0 3
  have h2 : 0 < t ^ 3 * (4 - t) := mul_pos ht3 (by linarith)
  simpa [g2_num] using add_pos hsq h2

theorem five_sqrt2_gt_seven_via_squares : (50 : ℚ) > 49 := by norm_num

theorem g2_num_pos_sample : 0 < g2_num (2/5) := by native_decide

end S6.CornerBudget
