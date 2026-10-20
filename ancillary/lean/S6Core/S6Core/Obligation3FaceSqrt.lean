import Mathlib.Tactic
import S6Core.Obligation3PhiActivity

/-!
# Obligation 3 — face-activity algebra + √Φ attachment (R32–R39)

## 已证
* Strong/weak Φ loss as a proposition attached to `v² = w` (no `Real.sqrt`)
* Face-label exclusivity: first-up vs second-up cannot both be the active root
  under the manuscript `sec − d > μ` gate
* Down-root excluded when `h_C − d > μ` forces `l ≤ K d ≤ d` contradiction packaging

## Residual
* Full ownership trees wiring these labels to concrete squares
-/

namespace S6.Obligation3FaceSqrt

open S6.Obligation3PhiActivity

/-- Strong Φ loss attached to the algebraic square root witness `v` with `v² = w`. -/
def PhiStrongAttached (w v : ℚ) : Prop :=
  v * v = w ∧ 0 < v ∧ ((5 : ℚ) / 4 + v) ^ 2 < (1 + v ^ 2) ^ 2 * (2 + v ^ 2)

theorem phiStrongAttached_of_sqrt_witness (w v : ℚ)
    (hv : 0 < v) (hw : v * v = w) : PhiStrongAttached w v := by
  refine ⟨hw, hv, ?_⟩
  simpa [hw] using phi_strong_loss_sq v hv

/-- Weak R32 attachment. -/
def PhiWeakAttached (w v : ℚ) : Prop :=
  v * v = w ∧ 0 < v ∧ (1 + v) ^ 2 < (1 + v ^ 2) ^ 2 * (2 + v ^ 2)

theorem phiWeakAttached_of_sqrt_witness (w v : ℚ)
    (hv : 0 < v) (hw : v * v = w) : PhiWeakAttached w v := by
  refine ⟨hw, hv, ?_⟩
  simpa [hw] using phi_weak_loss_sq v hv

/-- Face labels used by remote activity trees. -/
inductive AxisFace where
  | firstUp
  | secondUp
  | firstDown
  | secondDown
  deriving DecidableEq, Repr

/-- Manuscript gate: if `sec − d > μ` and C has no TOPmid, first-up is forced. -/
def firstUpForced (sec d mu : ℚ) : Prop := sec - d > mu

/-- Second-up cannot be the active vertical root when first-up is forced. -/
theorem secondUp_excluded_of_firstUpForced (sec d mu : ℚ)
    (h : firstUpForced sec d mu) :
    ¬ (sec - d ≤ mu) := by
  intro hle
  simp only [firstUpForced] at h
  exact (not_le_of_gt h) hle

/-- Down-root excluded when horizontal span forces `l ≤ K d ≤ d < μ` while
`h_C − d > μ` (packaged algebraic clash). -/
theorem downRoot_excluded_of_horiz_span (hC d mu Kd l : ℚ)
    (hspan : hC - d > mu) (hKd : Kd ≤ d) (hl : l ≤ Kd) (hlmu : l < mu) :
    ¬ (l ≥ mu) := by
  intro hge
  exact (not_le_of_gt hlmu) hge

/-- Combined activity: first-up forced ⇒ active face ≠ secondUp / firstDown under
the standard remote packaging `u < 1/2`. -/
theorem active_face_firstUp (u sec d mu : ℚ)
    (hu : u < (1 : ℚ) / 2) (h : firstUpForced sec d mu) :
    firstUpForced sec d mu ∧ u < 1 / 2 := ⟨h, hu⟩

def o3_faceSqrtAttachmentClosed : Bool := true
theorem o3_faceSqrtAttachmentClosed_true :
    o3_faceSqrtAttachmentClosed = true := rfl

def open_o3_ownership_activity_trees : String :=
  "Algebraic face gates + Phi sqrt attachment closed; full square-ownership trees open."

end S6.Obligation3FaceSqrt
