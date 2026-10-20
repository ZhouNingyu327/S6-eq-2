import Mathlib.Tactic
import S6Core.Obligation4QIdentity

/-!
# Obligation 4 — leaf metric `Δ(t)=t²/(2(1−t))`
-/

namespace S6.Obligation4LeafDelta

def Delta (t : ℚ) : ℚ := (t * t) / (2 * (1 - t))

theorem Delta_nonneg (t : ℚ) (h0 : 0 ≤ t) (h1 : t < 1) :
    0 ≤ Delta t := by
  have hden : 0 < 2 * (1 - t) := by nlinarith
  exact div_nonneg (mul_nonneg h0 h0) (le_of_lt hden)

theorem Delta_le_sq (t : ℚ) (h0 : 0 ≤ t) (h : t ≤ (1 : ℚ) / 2) :
    Delta t ≤ t * t := by
  have h1 : t < 1 := lt_of_le_of_lt h (by norm_num)
  have hden : 0 < 2 * (1 - t) := by nlinarith
  simp only [Delta]
  rw [div_le_iff₀ hden]
  nlinarith

theorem Delta_lt_sq (t : ℚ) (h0 : 0 < t) (h : t < (1 : ℚ) / 2) :
    Delta t < t * t := by
  have hden : 0 < 2 * (1 - t) := by nlinarith
  have ht2 : 0 < t * t := mul_pos h0 h0
  have hfac : 1 < 2 * (1 - t) := by nlinarith
  simp only [Delta]
  rw [div_lt_iff₀ hden]
  nlinarith

/-- R39-style: `Δ(r) < r² ≤ u d` packaging uses `Δ ≤ r²` on `(0,1/2]`. -/
theorem Delta_le_ud_of_r_sq (r u d : ℚ)
    (hr0 : 0 ≤ r) (hr : r ≤ (1 : ℚ) / 2) (hsq : r * r ≤ u * d) :
    Delta r ≤ u * d :=
  le_trans (Delta_le_sq r hr0 hr) hsq

def o4_leafDeltaClosed : Bool := true
theorem o4_leafDeltaClosed_true : o4_leafDeltaClosed = true := rfl

end S6.Obligation4LeafDelta
