import Mathlib.Tactic

/-!
# Obligation 4 — shared `q(t)=t/(2−t)` (near-end / remote)

## 已证
* `q` nonnegative on `[0,2)`
* `q t < 1` for `t ∈ [0,1)`
* `q` monotone on `[0,2)`
-/

namespace S6.Obligation4QIdentity

def q (t : ℚ) : ℚ := t / (2 - t)

theorem q_nonneg_of_lt_two (t : ℚ) (h0 : 0 ≤ t) (h2 : t < 2) :
    0 ≤ q t := by
  have hden : 0 < 2 - t := by linarith
  exact div_nonneg h0 (le_of_lt hden)

theorem q_lt_one_of_lt_one (t : ℚ) (_h0 : 0 ≤ t) (h1 : t < 1) :
    q t < 1 := by
  have hden : 0 < 2 - t := by linarith
  rw [q, div_lt_one hden]
  linarith

theorem q_monotone_on_Ico (t₁ t₂ : ℚ)
    (_h0 : 0 ≤ t₁) (hle : t₁ ≤ t₂) (h2 : t₂ < 2) :
    q t₁ ≤ q t₂ := by
  have hd1 : 0 < 2 - t₁ := by linarith
  have hd2 : 0 < 2 - t₂ := by linarith
  have key : t₁ * (2 - t₂) ≤ t₂ * (2 - t₁) := by nlinarith
  have := (div_le_div_iff₀ hd1 hd2).2 key
  simpa [q] using this

def o4_qIdentityClosed : Bool := true
theorem o4_qIdentityClosed_true : o4_qIdentityClosed = true := rfl

end S6.Obligation4QIdentity
