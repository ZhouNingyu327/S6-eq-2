import Mathlib.Tactic

namespace S6.QIdentity

def q (u : ℚ) : ℚ := u / (2 - u)

def numer (a x : ℚ) : ℚ :=
  a * (2 - a + x) * (2 - x)
    - (a - x) * (2 - a) * (2 - x)
    - x * (2 - a) * (2 - a + x)

theorem numer_factor (a x : ℚ) : numer a x = x * (a - x) * (4 - a) := by
  simp only [numer]; ring

theorem numer_nonneg (a x : ℚ) (hx0 : 0 ≤ x) (hxa : x ≤ a) (ha1 : a ≤ 1) :
    0 ≤ numer a x := by
  rw [numer_factor]
  have h1 : 0 ≤ a - x := sub_nonneg.mpr hxa
  have h2 : 0 ≤ (4 : ℚ) - a := by
    have : a ≤ (4 : ℚ) := le_trans ha1 (by norm_num)
    exact sub_nonneg.mpr this
  exact mul_nonneg (mul_nonneg hx0 h1) h2

theorem numer_factor_decide :
    numer (1/2) (1/3) = (1/3) * (1/2 - 1/3) * (4 - 1/2) := by
  native_decide

end S6.QIdentity
