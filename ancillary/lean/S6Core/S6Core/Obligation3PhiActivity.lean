import Mathlib.Tactic

/-!
# Obligation 3 — shared Φ-loss + activity algebra (R32–R39)

## 已证
* Strong Φ squared certificate (R33/R38/R39)
* Weak Φ squared certificate (R32)
* `K(η)` positivity and `K≤1` on `η≤2/5`
* Corner `ρ` positivity
-/

namespace S6.Obligation3PhiActivity

theorem phi_strong_loss_sq (v : ℚ) (_hv : 0 < v) :
    ((5 : ℚ) / 4 + v) ^ 2 < (1 + v ^ 2) ^ 2 * (2 + v ^ 2) := by
  have hrewrite :
      (1 + v ^ 2) ^ 2 * (2 + v ^ 2) - ((5 : ℚ) / 4 + v) ^ 2 =
        v ^ 6 + 4 * v ^ 4 + 4 * (v - (5 : ℚ) / 16) ^ 2 + (3 : ℚ) / 64 := by
    ring
  have hpos : 0 <
      v ^ 6 + 4 * v ^ 4 + 4 * (v - (5 : ℚ) / 16) ^ 2 + (3 : ℚ) / 64 := by
    have h3 : (0 : ℚ) < 3 / 64 := by norm_num
    have hsq : 0 ≤ 4 * (v - (5 : ℚ) / 16) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
    have hv4 : 0 ≤ v ^ 4 := by
      have : v ^ 4 = (v ^ 2) ^ 2 := by ring
      simpa [this] using sq_nonneg (v ^ 2)
    have hv6 : 0 ≤ v ^ 6 := by
      have : v ^ 6 = (v ^ 3) ^ 2 := by ring
      simpa [this] using sq_nonneg (v ^ 3)
    nlinarith
  have : 0 <
      (1 + v ^ 2) ^ 2 * (2 + v ^ 2) - ((5 : ℚ) / 4 + v) ^ 2 := by
    rw [hrewrite]; exact hpos
  linarith

theorem phi_weak_loss_sq (v : ℚ) (_hv : 0 < v) :
    (1 + v) ^ 2 < (1 + v ^ 2) ^ 2 * (2 + v ^ 2) := by
  have hrewrite :
      (1 + v ^ 2) ^ 2 * (2 + v ^ 2) - (1 + v) ^ 2 =
        v ^ 6 + 4 * v ^ 4 + 3 * v ^ 2 + (v - 1) ^ 2 := by
    ring
  have hpos : 0 <
      v ^ 6 + 4 * v ^ 4 + 3 * v ^ 2 + (v - 1) ^ 2 := by
    have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
    have hv4 : 0 ≤ v ^ 4 := by
      have : v ^ 4 = (v ^ 2) ^ 2 := by ring
      simpa [this] using sq_nonneg (v ^ 2)
    have hv6 : 0 ≤ v ^ 6 := by
      have : v ^ 6 = (v ^ 3) ^ 2 := by ring
      simpa [this] using sq_nonneg (v ^ 3)
    -- (v-1)² + 3v² ≥ 0, and if all zero then v=0 and v=1 impossible; use ≥ (v-1)² ≥ 0
    -- Strict: 3v² + (v-1)² = 4v² - 2v + 1 = (2v-1/2)² + 3/4 > 0
    have : 3 * v ^ 2 + (v - 1) ^ 2 = 4 * v ^ 2 - 2 * v + 1 := by ring
    have hstrict : 0 < 4 * v ^ 2 - 2 * v + 1 := by
      have : 4 * v ^ 2 - 2 * v + 1 = 4 * (v - (1 : ℚ) / 4) ^ 2 + (3 : ℚ) / 4 := by
        ring
      nlinarith [sq_nonneg (v - (1 : ℚ) / 4)]
    nlinarith
  have : 0 <
      (1 + v ^ 2) ^ 2 * (2 + v ^ 2) - (1 + v) ^ 2 := by
    rw [hrewrite]; exact hpos
  linarith

def Keta (eta : ℚ) : ℚ := (2 * eta) / (1 - eta * eta)

theorem Keta_pos (eta : ℚ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < Keta eta := by
  have hden : 0 < 1 - eta * eta := by nlinarith
  exact div_pos (by nlinarith) hden

theorem Keta_le_one_of_le_two_fifths (eta : ℚ)
    (h0 : 0 < eta) (h : eta ≤ (2 : ℚ) / 5) :
    Keta eta ≤ 1 := by
  have h1 : eta < 1 := lt_of_le_of_lt h (by norm_num)
  have hden : 0 < 1 - eta * eta := by nlinarith
  have : 2 * eta ≤ 1 - eta * eta := by nlinarith
  exact (div_le_one hden).2 this

def rhoCorner (a : ℚ) : ℚ := (1 - a) * a / (1 + a)

theorem rhoCorner_pos (a : ℚ) (h0 : 0 < a) (h1 : a < 1) :
    0 < rhoCorner a := by
  have hden : 0 < 1 + a := by linarith
  exact div_pos (mul_pos (by linarith) h0) hden

theorem eight_fifths_gt_one : (8 : ℚ) / 5 > 1 := by norm_num

def o3_phiStrongSqClosed : Bool := true
theorem o3_phiStrongSqClosed_true : o3_phiStrongSqClosed = true := rfl

def o3_KetaActivityAlgebraClosed : Bool := true
theorem o3_KetaActivityAlgebraClosed_true :
    o3_KetaActivityAlgebraClosed = true := rfl

def open_o3_phi_geometric_sqrt : String :=
  "Geometric Phi with Real.sqrt still outside Rat core; squared certificates closed."

def open_o3_face_activity_trees : String :=
  "Per-frame face-activity case trees need ownership geometry; K/rho gates closed."

end S6.Obligation3PhiActivity
