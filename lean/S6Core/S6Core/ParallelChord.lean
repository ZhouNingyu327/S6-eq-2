import Mathlib.Tactic

/-!
# B(d) < 1 — algebraic cores of (M4)

Geometric maximisation producing B is not formalised here.
-/

namespace S6.ParallelChord

/-- Case 1: `d - y < 1` given `y² = d² - 1`, `d > 1`, `y ≥ 0`. -/
theorem B_case1_lt_one (d y : ℚ) (hd : 1 < d)
    (hy2 : y * y = d * d - 1) (_hy : 0 ≤ y) :
    d - y < 1 := by
  have hpos : 0 < d - 1 := sub_pos.mpr hd
  have hy2'' : y * y = (d - 1) * (d + 1) := by
    calc y * y = d * d - 1 := hy2
      _ = (d - 1) * (d + 1) := by ring
  -- Both sides of (d-1)² < y² are nonnegative; compare after expanding.
  have hypos : 0 < y := by
    have : 0 < (d - 1) * (d + 1) := mul_pos hpos (by linarith)
    nlinarith [hy2'']
  have hsq : (d - 1) ^ 2 < y ^ 2 := by
    have : (d - 1) ^ 2 < (d - 1) * (d + 1) := by
      nlinarith
    simpa [pow_two, hy2''] using this
  have hlt : d - 1 < y := by
    exact (sq_lt_sq₀ (le_of_lt hpos) (le_of_lt hypos)).1 hsq
  linarith

/-- Case 2 cleared: `s² = 2`, `2ds ≥ 3` ⇒ `2(s-d) < 1`. -/
theorem B_case2_lt_one_cleared (d s : ℚ)
    (hs2 : s * s = 2) (hs : 0 < s) (hd : (3 : ℚ) ≤ 2 * d * s) :
    2 * (s - d) < 1 := by
  -- Goal ↔ 2s - 1 < 2d.
  -- From hd: 2d ≥ 3/s. With s²=2, 1/s = s/2, hence 3/s = 3s/2.
  have hinv : s⁻¹ = s / 2 := by
    have hsne : s ≠ 0 := ne_of_gt hs
    field_simp [hsne]
    -- s * s = 2 ⇒ 1 = s * (s/2)? Wait: field_simp goal is 1 = s*(s/2) after clearing
    nlinarith [hs2]
  have thr : (3 : ℚ) / s = (3 : ℚ) / 2 * s := by
    calc (3:ℚ)/s = 3 * s⁻¹ := by ring
      _ = 3 * (s / 2) := by rw [hinv]
      _ = (3:ℚ)/2 * s := by ring
  have lower : (3 : ℚ) / 2 * s ≤ 2 * d := by
    have : (3 : ℚ) / s ≤ 2 * d := (div_le_iff₀ hs).2 (by linarith)
    simpa [thr] using this
  -- 3s/2 > 2s - 1 ↔ 1 > s/2 ↔ s < 2, from s²=2<4
  have hs_lt_two : s < 2 := by
    have h4 : (2 : ℚ) < 4 := by norm_num
    have : s ^ 2 < 2 ^ 2 := by
      simpa [pow_two, hs2] using h4
    exact (sq_lt_sq₀ (le_of_lt hs) (by norm_num : (0:ℚ) ≤ 2)).1 this
  have gap : (3 : ℚ) / 2 * s > 2 * s - 1 := by nlinarith
  linarith

/-- Concrete rational check used in hand audits: 50>49 ⇒ 5√2>7. -/
theorem fifty_gt_forty_nine : (50 : ℚ) > 49 := by norm_num

end S6.ParallelChord
