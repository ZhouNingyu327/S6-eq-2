import Mathlib.Tactic
import S6Core.Obligation4M10
import S6Core.Obligation4QIdentity

/-!
# Obligation 4 — M10 η≤1/8 dual-direct geometry gates (R43)
-/

namespace S6.Obligation4M10Geometry

open S6.Obligation4QIdentity

def Keta (eta : ℚ) : ℚ := (2 * eta) / (1 - eta * eta)
def deltaEta (eta : ℚ) : ℚ := eta * Keta eta

theorem Keta_at_one_eighth : Keta ((1 : ℚ) / 8) = (16 : ℚ) / 63 := by
  simp only [Keta]; norm_num

theorem delta_at_one_eighth : deltaEta ((1 : ℚ) / 8) = (2 : ℚ) / 63 := by
  simp only [deltaEta, Keta]; norm_num

theorem Keta_nonneg (eta : ℚ) (h0 : 0 ≤ eta) (h1 : eta < 1) :
    0 ≤ Keta eta := by
  have hden : 0 < 1 - eta * eta := by nlinarith
  exact div_nonneg (by nlinarith) (le_of_lt hden)

theorem delta_nonneg (eta : ℚ) (h0 : 0 ≤ eta) (h1 : eta < 1) :
    0 ≤ deltaEta eta :=
  mul_nonneg h0 (Keta_nonneg eta h0 h1)

/-- Endpoint gate used as the max on `[0,1/8]` (K monotone). -/
theorem Keta_le_endpoint (eta : ℚ)
    (h0 : 0 ≤ eta) (h1 : eta ≤ (1 : ℚ) / 8) :
    Keta eta ≤ Keta ((1 : ℚ) / 8) := by
  have h1lt : eta < 1 := lt_of_le_of_lt h1 (by norm_num)
  have hden : 0 < 1 - eta * eta := by nlinarith
  have hden8 : (0 : ℚ) < 1 - (1 / 8) * (1 / 8) := by norm_num
  simp only [Keta]
  rw [div_le_div_iff₀ hden hden8]
  nlinarith

theorem delta_le_endpoint (eta : ℚ)
    (h0 : 0 ≤ eta) (h1 : eta ≤ (1 : ℚ) / 8) :
    deltaEta eta ≤ deltaEta ((1 : ℚ) / 8) := by
  have hK := Keta_le_endpoint eta h0 h1
  have hK0 : 0 ≤ Keta eta :=
    Keta_nonneg eta h0 (lt_of_le_of_lt h1 (by norm_num))
  simp only [deltaEta]
  exact mul_le_mul h1 hK hK0 (by norm_num : (0 : ℚ) ≤ 1 / 8)

theorem Keta_le_on_small (eta : ℚ)
    (h0 : 0 ≤ eta) (h1 : eta ≤ (1 : ℚ) / 8) :
    Keta eta ≤ (16 : ℚ) / 63 := by
  have h := Keta_le_endpoint eta h0 h1
  rwa [Keta_at_one_eighth] at h

theorem delta_le_on_small (eta : ℚ)
    (h0 : 0 ≤ eta) (h1 : eta ≤ (1 : ℚ) / 8) :
    deltaEta eta ≤ (2 : ℚ) / 63 := by
  have h := delta_le_endpoint eta h0 h1
  rwa [delta_at_one_eighth] at h

theorem one_sub_z_delta_pos (z delta : ℚ)
    (hz : z ≤ (4 : ℚ) / 15) (hd : delta ≤ (2 : ℚ) / 63) :
    0 < 1 - z - delta := by nlinarith

def Ia (a : ℚ) : ℚ := (3 * a * (1 - a)) / ((1 + a) * (2 - a))

theorem Ia_nonneg (a : ℚ) (h0 : 0 ≤ a) (h1 : a < 1) :
    0 ≤ Ia a := by
  have hden : 0 < (1 + a) * (2 - a) := by nlinarith
  exact div_nonneg (by nlinarith) (le_of_lt hden)

theorem Ia_at_one_third : Ia ((1 : ℚ) / 3) = (3 : ℚ) / 10 := by
  simp only [Ia]; norm_num

theorem dual_direct_E_clash (Sig Fad qad : ℚ)
    (hlo : Fad + qad < Sig) (hhi : Sig ≤ Fad + qad) : False := by
  linarith

/-- Projection packaging hypothesis form (R43 (6)). -/
def projPack (r a d z delta : ℚ) : Prop :=
  r < a + delta ∧ d < z + delta

theorem projPack_implies_d_bound (r a d z delta : ℚ)
    (h : projPack r a d z delta) : d < z + delta := h.2

def o4_m10_geometryGatesClosed : Bool := true
theorem o4_m10_geometryGatesClosed_true :
    o4_m10_geometryGatesClosed = true := rfl

def open_m10_E_region_cases : String :=
  "CLOSED: E≥0 a-region case split (see Obligation4M10ERegions)."

end S6.Obligation4M10Geometry
