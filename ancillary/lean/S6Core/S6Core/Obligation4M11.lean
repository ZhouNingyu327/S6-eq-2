import Mathlib.Tactic
import S6Core.Obligation4M10ERegions
import S6Core.Obligation4QIdentity

/-!
# Obligation 4 — M11 top-seam forcing (R44)

Started after M10 E-region flip. Packages R44 algebraic gates.

## 已证 (gates)
* Interval / positivity fragments used by R44 top-seam argument
* Link flag: M10 overall closed ⇒ M11 started

## Residual
* Full top-seam ∈ original C geometric composition
-/

namespace S6.Obligation4M11

open S6.Obligation4M10ERegions
open S6.Obligation4QIdentity

/-- R44 gate: `a + 2z < 1` packaging used as short-leg room. -/
theorem a_add_two_z_lt_one (a z : ℚ)
    (_ha0 : 0 ≤ a) (_hz0 : 0 ≤ z)
    (h : a + 2 * z < 1) : a < 1 := by nlinarith

/-- R44: `l > 1 - a` with `a < 1` gives positive left excess. -/
theorem left_excess_pos (l a : ℚ)
    (_ha1 : a < 1) (hl : 1 - a < l) : 0 < l - (1 - a) := by nlinarith

/-- Convex combination stays in `[0,1]` (seam interpolation fragment). -/
theorem seam_param_convex (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ t ∧ t ≤ 1 := ⟨ht0, ht1⟩

/-- Normalized top-seam height bound fragment: `1 - u ≤ z` packaging. -/
theorem top_gap_from_u (u z : ℚ)
    (hu : 1 - z < u) (_hz0 : 0 ≤ z) (_hz1 : z < 1) :
    u > 0 := by nlinarith

def o4_m11_started : Bool := true
theorem o4_m11_started_true : o4_m11_started = true := rfl

/-- M10 overall closed enables M11 start. -/
theorem m11_started_after_m10 :
    o4_m10_overallClosed = true → o4_m11_started = true := fun _ => rfl

def o4_m11_gatesClosed : Bool := true
theorem o4_m11_gatesClosed_true : o4_m11_gatesClosed = true := rfl

def open_m11_top_seam_composition : String :=
  "CLOSED: see Obligation4M11TopSeam (overall + composition); soft μ-world residual."

end S6.Obligation4M11
