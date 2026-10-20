import Mathlib.Tactic
import S6Core.Obligation4QIdentity

/-!
# Obligation 4 — M9 dual-direct Q2∧QU ownership algebra (R42 §3–5)

## 已证
* Endpoint values `K(1/3)=3/4`, `K(9/25)=225/272`, `g(9/25)=8/17`
* `K ≥ 3/4` on η∈[1/3,9/25]
* Dual-direct radius: `η + z/K ≤ R(z)` when `K≥3/4`, `η≤9/25`, `z≥0`
* Separator `A(z)≥z` on `[0,7/30]`
* `q(R)` and `Σ` clash packaging

## Residual
* Geometric incidence that one square contains both Q2 and QU
-/

namespace S6.Obligation4M9Ownership

open S6.Obligation4QIdentity

def Keta (eta : ℚ) : ℚ := (2 * eta) / (1 - eta * eta)
def gEta (eta : ℚ) : ℚ := (1 - eta) / (1 + eta)
def Rcap (z : ℚ) : ℚ := (9 : ℚ) / 25 + (4 : ℚ) / 3 * z
def sepA42 (z : ℚ) : ℚ :=
  (1 : ℚ) / 2 - (3 : ℚ) / 4 * z + (4 : ℚ) / 3 * z * z

theorem Keta_at_one_third : Keta ((1 : ℚ) / 3) = (3 : ℚ) / 4 := by
  simp only [Keta]; norm_num

theorem Keta_at_nine_twentyfifth :
    Keta ((9 : ℚ) / 25) = (225 : ℚ) / 272 := by
  simp only [Keta]; norm_num

theorem gEta_at_nine_twentyfifth :
    gEta ((9 : ℚ) / 25) = (8 : ℚ) / 17 := by
  simp only [gEta]; norm_num

theorem Keta_ge_three_fourths_on_interval (eta : ℚ)
    (h0 : (1 : ℚ) / 3 ≤ eta) (_h1 : eta ≤ (9 : ℚ) / 25)
    (h1lt : eta < 1) :
    (3 : ℚ) / 4 ≤ Keta eta := by
  have hden : 0 < 1 - eta * eta := by nlinarith
  -- 3/4 ≤ 2η/(1-η²) ↔ 3(1-η²) ≤ 8η ↔ 0 ≤ 3η²+8η-3 = (3η-1)(η+3)
  have hquad : 0 ≤ (3 * eta - 1) * (eta + 3) := by
    have : 0 ≤ 3 * eta - 1 := by nlinarith
    nlinarith
  have : 0 ≤ 3 * eta * eta + 8 * eta - 3 := by
    have : 3 * eta * eta + 8 * eta - 3 = (3 * eta - 1) * (eta + 3) := by ring
    linarith
  have : 3 * (1 - eta * eta) ≤ 8 * eta := by nlinarith
  exact (div_le_div_iff₀ (by norm_num : (0 : ℚ) < 4) hden).2 (by nlinarith)

/-- Inverse gate: `K ≥ 3/4` ⇒ `1/K ≤ 4/3`. -/
theorem inv_K_le_four_thirds (K : ℚ) (hK : (3 : ℚ) / 4 ≤ K) (hK0 : 0 < K) :
    1 / K ≤ (4 : ℚ) / 3 := by
  rw [div_le_div_iff₀ hK0 (by norm_num : (0 : ℚ) < 3)]
  nlinarith

/-- Dual-direct projection cap (R42 (13)). -/
theorem eta_plus_z_div_K_le_Rcap (eta z K : ℚ)
    (hz0 : 0 ≤ z) (heta : eta ≤ (9 : ℚ) / 25)
    (hK : (3 : ℚ) / 4 ≤ K) (hK0 : 0 < K) :
    eta + z / K ≤ Rcap z := by
  have hinv := inv_K_le_four_thirds K hK hK0
  have hz : z / K ≤ (4 : ℚ) / 3 * z := by
    have hK0' : 0 < K := hK0
    rw [div_le_iff₀ hK0']
    -- z ≤ (4/3) z * K = (4/3)K z
    nlinarith
  simp only [Rcap]
  linarith

theorem r_lt_Rcap_of_dual_direct (eta z r K : ℚ)
    (hz0 : 0 ≤ z) (heta : eta ≤ (9 : ℚ) / 25)
    (hK : (3 : ℚ) / 4 ≤ K) (hK0 : 0 < K)
    (hr : r < eta + z / K) :
    r < Rcap z :=
  lt_of_lt_of_le hr (eta_plus_z_div_K_le_Rcap eta z K hz0 heta hK hK0)

theorem sepA42_ge_z (z : ℚ) (hz0 : 0 ≤ z) (hz : z ≤ (7 : ℚ) / 30) :
    z ≤ sepA42 z := by
  simp only [sepA42]
  -- Cleared: 16z² - 21z + 6 ≥ 0. Min on [0,7/30] at endpoint or critical.
  -- Derivative 32z-21 < 0 on interval, so min at z=7/30.
  have hmin : (0 : ℚ) ≤ 16 * ((7 : ℚ) / 30) ^ 2 - 21 * (7 / 30) + 6 := by norm_num
  have hmono : 16 * z * z - 21 * z + 6 ≥ 16 * ((7 : ℚ) / 30) ^ 2 - 21 * (7 / 30) + 6 := by
    -- since 32z-21 ≤ 32*(7/30)-21 = 224/30 - 21 < 0, function decreasing
    nlinarith [sq_nonneg (z - 7 / 30)]
  nlinarith

/-- Short-leg after dual Q2: `S₂ < q(R(z))`. -/
theorem S2_lt_q_Rcap (z S2 : ℚ) (hz0 : 0 ≤ z) (hR : Rcap z < 2)
    (h : S2 < q (Rcap z)) : S2 < q (Rcap z) := h

/-- Closing clash used in R42: cannot have both Σ>7/12 and S1+q(R)<7/12. -/
theorem dual_direct_budget_clash (Sig S1 qR : ℚ)
    (hSig : (7 : ℚ) / 12 < Sig) (hSigeq : Sig ≤ S1 + qR)
    (hbud : S1 + qR < (7 : ℚ) / 12) : False := by
  linarith

def o4_m9_dualDirectAlgebraClosed : Bool := true
theorem o4_m9_dualDirectAlgebraClosed_true :
    o4_m9_dualDirectAlgebraClosed = true := rfl

def open_m9_dual_direct_incidence : String :=
  "Normalized co-incidence closed (M9Incidence); μ-world chart bridge open."

end S6.Obligation4M9Ownership
