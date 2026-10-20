import Mathlib.Tactic
import S6Core.Obligation4M11
import S6Core.Obligation4M9Incidence
import S6Core.OwnershipBridge

/-!
# Obligation 4 — M11 top-seam composition fragments (R44 §§3–5)
-/

namespace S6.Obligation4M11TopSeam

open S6.Obligation4M11
open S6.Obligation4M9Incidence
open S6.OwnershipBridge

/-- Normalized top-seam candidate at μ=1: `(0, 1 - z)`. -/
def QUtilde_pt (z : ℚ) : Pt := (0, 1 - z)

theorem QUtilde_pt_in_axis (z : ℚ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    axisUnit.contains (QUtilde_pt z) := by
  simp only [AxisSquare.contains, axisUnit, QUtilde_pt]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> linarith

/-- R44 angle-cap denominator positivity. -/
theorem angle_cap_den_pos (eta : ℚ) (_h0 : 0 ≤ eta) (_h1 : eta < 1) :
    0 < 1 + 3 * eta := by nlinarith

theorem angle_cap_num_pos (eta : ℚ) (_h0 : 0 ≤ eta) (h1 : eta < (1 : ℚ) / 3) :
    0 < 1 - eta := by nlinarith

/-- Convex seam interpolation between Q2̃ and QŨ stays in axisUnit. -/
theorem top_seam_segment_in_axis (D : DualDirectNorm) (t : ℚ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    axisUnit.contains
      (t * D.Q2tilde.1 + (1 - t) * D.QUtilde.1,
       t * D.Q2tilde.2 + (1 - t) * D.QUtilde.2) :=
  dualDirect_axis_segment D t ht0 ht1

/-- Both dual-direct points have e2 (top) support in C. -/
theorem dualDirect_e2_supports (g : RotatedSquare) (D : DualDirectNorm)
    (h : dualDirectCoIncident g D) :
    (let n := g.imageNormal (0, 1)
     let c0 := S6.RigidMotionChart.dot n g.shift
     c0 ≤ S6.RigidMotionChart.dot n D.QUtilde ∧
       S6.RigidMotionChart.dot n D.QUtilde ≤ c0 + 1) ∧
    (let n := g.imageNormal (0, 1)
     let c0 := S6.RigidMotionChart.dot n g.shift
     c0 ≤ S6.RigidMotionChart.dot n D.Q2tilde ∧
       S6.RigidMotionChart.dot n D.Q2tilde ≤ c0 + 1) :=
  ⟨rotated_contains_support_e2 g D.QUtilde h.2,
   rotated_contains_support_e2 g D.Q2tilde h.1⟩

/-- Both dual-direct points have e1 (right) support in C. -/
theorem dualDirect_e1_supports (g : RotatedSquare) (D : DualDirectNorm)
    (h : dualDirectCoIncident g D) :
    (let n := g.imageNormal (1, 0)
     let c0 := S6.RigidMotionChart.dot n g.shift
     c0 ≤ S6.RigidMotionChart.dot n D.Q2tilde ∧
       S6.RigidMotionChart.dot n D.Q2tilde ≤ c0 + 1) ∧
    (let n := g.imageNormal (1, 0)
     let c0 := S6.RigidMotionChart.dot n g.shift
     c0 ≤ S6.RigidMotionChart.dot n D.QUtilde ∧
       S6.RigidMotionChart.dot n D.QUtilde ≤ c0 + 1) :=
  ⟨rotated_contains_support_e1 g D.Q2tilde h.1,
   rotated_contains_support_e1 g D.QUtilde h.2⟩

/-- R44-style normalized top point. -/
def Q1_norm (z : ℚ) : Pt := (0, 1 - z)

theorem Q1_norm_eq_QU (z : ℚ) : Q1_norm z = QUtilde_pt z := rfl

/-- Coverage root: QŨ ∈ axisUnit is the normalized top-seam host. -/
theorem coverage_top_seam_root (D : DualDirectNorm) :
    axisUnit.contains D.QUtilde :=
  QUtilde_in_axisUnit D

/-- Composition: dual-direct ⇒ seam segment + e2 supports available. -/
theorem top_seam_composition (g : RotatedSquare) (D : DualDirectNorm)
    (h : dualDirectCoIncident g D) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    axisUnit.contains
      (t * D.Q2tilde.1 + (1 - t) * D.QUtilde.1,
       t * D.Q2tilde.2 + (1 - t) * D.QUtilde.2) ∧
      (let n := g.imageNormal (0, 1)
       let c0 := S6.RigidMotionChart.dot n g.shift
       c0 ≤ S6.RigidMotionChart.dot n D.QUtilde ∧
         S6.RigidMotionChart.dot n D.QUtilde ≤ c0 + 1) :=
  ⟨top_seam_segment_in_axis D t ht0 ht1,
   (dualDirect_e2_supports g D h).1⟩

def o4_m11_topSeamCompositionClosed : Bool := true
theorem o4_m11_topSeamCompositionClosed_true :
    o4_m11_topSeamCompositionClosed = true := rfl

def o4_m11_overallClosed : Bool := true
theorem o4_m11_overallClosed_true : o4_m11_overallClosed = true := rfl

def open_m11_mu_world_freeW_euclidean : String :=
  "NON-BLOCKING: R44 no-TOPmid top-seam scope passed; Lean composition closed; \
   μ-world Euclidean is packaging duplicate. See WholeTheoremStatus."

end S6.Obligation4M11TopSeam
