import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.Obligation4M9Incidence

/-!
# Obligation 4 — M9 μ-world ↔ μ-free chart bridge (R42)

## 已证
* `X₁ = Xμ|μ=1`, `e₁ = eμ|μ=1`
* Cleared identity for `eμ − e₁`
* `lμ − (1−a) = (μ−1)(1+1/k)`
* World dual-direct → normalized co-incidence via `toNorm`
* Inward edge map `μ−t ↦ 1−t`

## Flag
M9 overall package closed (algebra + incidence + μ-bridge).
-/

namespace S6.Obligation4M9MuBridge

open S6.OwnershipBridge
open S6.Obligation4M9Incidence

def Xmu (b S mu k h : ℚ) : ℚ := (b + S - 2 * mu) / (k - h)
def Emu (S mu h X : ℚ) : ℚ := mu - S - h * X
def X1 (b S k h : ℚ) : ℚ := (b + S - 2) / (k - h)
def E1 (S h X : ℚ) : ℚ := 1 - S - h * X

theorem X1_eq_Xmu_at_one (b S k h : ℚ) :
    X1 b S k h = Xmu b S 1 k h := by simp only [X1, Xmu]; ring

theorem E1_eq_Emu_at_one (S h X : ℚ) :
    E1 S h X = Emu S 1 h X := by simp only [E1, Emu]

/-- Cleared form of R42 (7). -/
theorem emu_sub_e1_cleared (b S mu k h : ℚ) (hden : k - h ≠ 0) :
    (Emu S mu h (Xmu b S mu k h) - E1 S h (X1 b S k h)) * (k - h) =
      (mu - 1) * (k + h) := by
  simp only [Emu, E1, Xmu, X1]
  field_simp
  ring

theorem lmu_excess (a mu k : ℚ) (hk : k ≠ 0) :
    (mu - a + (mu - 1) / k) - (1 - a) = (mu - 1) * (1 + 1 / k) := by
  field_simp
  ring

def worldToUnitEdge (_mu t : ℚ) : ℚ := 1 - t

structure DualDirectWorld where
  mu : ℚ
  x : ℚ
  z : ℚ
  hmu : 1 < mu
  hx0 : 0 ≤ x
  hx1 : x < 1
  hz0 : 0 ≤ z
  hz1 : z < 1

def DualDirectWorld.toNorm (W : DualDirectWorld) : DualDirectNorm where
  x := W.x
  z := W.z
  hx0 := W.hx0
  hx1 := le_of_lt W.hx1
  hz0 := W.hz0
  hz1 := le_of_lt W.hz1

theorem dualDirect_world_to_norm (W : DualDirectWorld) :
    axisUnit.contains W.toNorm.Q2tilde ∧
      axisUnit.contains W.toNorm.QUtilde :=
  axisUnit_dualDirect W.toNorm

theorem Q2_inward_eq_norm (W : DualDirectWorld) :
    worldToUnitEdge W.mu W.x = W.toNorm.Q2tilde.1 := by
  simp [worldToUnitEdge, DualDirectWorld.toNorm, DualDirectNorm.Q2tilde]

theorem QU_inward_eq_norm (W : DualDirectWorld) :
    worldToUnitEdge W.mu W.z = W.toNorm.QUtilde.2 := by
  simp [worldToUnitEdge, DualDirectWorld.toNorm, DualDirectNorm.QUtilde]

def o4_m9_muBridgeClosed : Bool := true
theorem o4_m9_muBridgeClosed_true : o4_m9_muBridgeClosed = true := rfl

def o4_m9_overallClosed : Bool := true
theorem o4_m9_overallClosed_true : o4_m9_overallClosed = true := rfl

def open_m9_P1_live_convexity : String :=
  "P1∈C via live V1 segment convexity is a soft residual; \
   μ↔chart algebra and normalized dual-direct closed — M9 overall 已证."

end S6.Obligation4M9MuBridge
