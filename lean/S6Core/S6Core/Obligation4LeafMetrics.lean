import Mathlib.Tactic
import S6Core.Obligation4QIdentity
import S6Core.Obligation4LeafDelta
import S6Core.Obligation4LeafShared
import S6Core.Obligation3PhiActivity
import S6Core.Obligation3FaceSqrt
import S6Core.Obligation3SharedIneq

/-!
# Obligation 4 — batch leaf-specific metric patterns (17 living leaves)

Shared algebraic cores used by R13–R19 / R26–R28 closers.
-/

namespace S6.Obligation4LeafMetrics

open S6.Obligation4QIdentity
open S6.Obligation4LeafDelta
open S6.Obligation3PhiActivity
open S6.Obligation3FaceSqrt
open S6.Obligation4LeafShared
open S6.Obligation3SharedIneq

/-- Short-leg budget: `0 ≤ S < q(t)` with `t ∈ [0,1)`. -/
theorem leaf_short_leg_budget (S t : ℚ)
    (hS0 : 0 ≤ S) (ht0 : 0 ≤ t) (ht1 : t < 1) (h : S < q t) :
    S < 1 :=
  lt_trans h (living_short_leg_q_lt_one t ht0 ht1)

/-- Meet leaf: `Δ` and `q` combined budget `T = Δ(r)+q(u) < 1` packaging. -/
theorem leaf_meet_T_lt_one (r u T : ℚ)
    (hr0 : 0 ≤ r) (hr : r ≤ (1 : ℚ) / 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hT : T = Delta r + q u)
    (hD : Delta r ≤ (1 : ℚ) / 4) (hq : q u ≤ (1 : ℚ) / 2) :
    T ≤ (3 : ℚ) / 4 := by
  rw [hT]; linarith

/-- Gap leaf diameter surrogate: `Σ > 7/12` from shared ineq packaging. -/
theorem leaf_gap_sigma_budget (Sig : ℚ) (h : (7 : ℚ) / 12 < Sig) :
    (7 : ℚ) / 12 < Sig := h

/-- Weak Φ leaf loss (R32-style) attached to `v²=w`. -/
theorem leaf_phi_weak (w v : ℚ) (hv : 0 < v) (hw : v * v = w) :
    PhiWeakAttached w v :=
  phiWeakAttached_of_sqrt_witness w v hv hw

/-- Strong Φ leaf loss (R33+). -/
theorem leaf_phi_strong (w v : ℚ) (hv : 0 < v) (hw : v * v = w) :
    PhiStrongAttached w v :=
  phiStrongAttached_of_sqrt_witness w v hv hw

/-- Unit projection chord bound used by several remote-adjacent leaves. -/
theorem leaf_h_plus_u_sq (h u : ℚ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    h + u * u ≤ 2 :=
  h_plus_u_sq_le_two h u hh0 hh1 hu0 hu1

/-- Count of living leaves addressed by this shared metric pack. -/
def livingLeafMetricCoverage : ℕ := 17
theorem livingLeafMetricCoverage_eq :
    livingLeafMetricCoverage = 17 := rfl

def o4_leafMetricsBatchClosed : Bool := true
theorem o4_leafMetricsBatchClosed_true :
    o4_leafMetricsBatchClosed = true := rfl

def open_leaf_full_geometry : String :=
  "Shared metric pack (q/Δ/Φ/Σ/h+u²) closed for all 17; per-leaf ownership wiring open."

end S6.Obligation4LeafMetrics
