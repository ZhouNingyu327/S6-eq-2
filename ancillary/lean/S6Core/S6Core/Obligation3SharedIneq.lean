import Mathlib.Tactic

/-!
# Obligation 3 — shared R30–39 inequalities (high-leverage algebraic cores)

## 已证
* Unit-projection `h + u² ≤ 2` on `[0,1]²`
* Diameter budget ⇒ `Σ > 2 − √2` (with `s² = 2`)
* Same-F bottom LRA contradiction fragment
-/

namespace S6.Obligation3SharedIneq

theorem h_plus_u_sq_le_two (h u : ℚ)
    (_hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    h + u * u ≤ 2 := by
  have huu : u * u ≤ u := by nlinarith [hu0, hu1]
  nlinarith

theorem h_sq_plus_u_sq_le_two (h u : ℚ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    h * h + u * u ≤ 2 := by
  nlinarith

/-- `b ≤ √2`, `b ≥ 2μ − Σ`, `μ > 1` ⇒ `Σ > 2 − √2`. -/
theorem sigma_gt_two_sub_s_of_diameter (mu Sigma b s : ℚ)
    (hmu : 1 < mu) (_hs2 : s * s = 2) (_hs0 : 0 < s)
    (hb_le : b ≤ s) (hb_ge : 2 * mu - Sigma ≤ b) :
    2 - s < Sigma := by
  have hchain : 2 * mu - Sigma ≤ s := le_trans hb_ge hb_le
  have : 2 * mu - s ≤ Sigma := by linarith
  have : 2 - s < 2 * mu - s := by linarith
  linarith

theorem sigma_gt_two_sub_s (mu Sigma s : ℚ)
    (hmu : 1 < mu) (_hs2 : s * s = 2) (hbud : 2 * mu - Sigma ≤ s) :
    2 - s < Sigma := by
  have : 2 * mu - s ≤ Sigma := by linarith
  have : 2 - s < 2 * mu - s := by linarith
  linarith

theorem same_F_bottom_diameter_contradiction (S1 S2 Sigma qval : ℚ)
    (hSeq : Sigma = S1 + S2) (hbig : (7 : ℚ) / 12 < Sigma)
    (hS2 : S2 < qval) (hsum : S1 + qval ≤ (7 : ℚ) / 12) :
    False := by
  have : Sigma < S1 + qval := by linarith
  linarith

def o3_sharedIneqClosed : Bool := true
theorem o3_sharedIneqClosed_true : o3_sharedIneqClosed = true := rfl

def open_o3_lean_geometry_R30_39 : String :=
  "Shared diameter / unit-projection fragments closed; full per-frame \
   metric geometry (asymmetric chord faces, Phi-loss calculus, activity trees) open."

end S6.Obligation3SharedIneq
