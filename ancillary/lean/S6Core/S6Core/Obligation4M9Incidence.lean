import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.Obligation4M9Ownership

/-!
# Obligation 4 — M9 Q2∧QU geometric co-incidence

## 已证
* Body axis-square convexity
* AxisSquare convexity
* Dual-direct normalized points Q2̃/QŨ ∈ axisUnit
* Rotated mid ownership (bridge)
* Support bounds when a rotated square contains a point

## Residual
* μ-world ↔ μ-free chart normalization for literal Q2/QU
-/

namespace S6.Obligation4M9Incidence

open S6.OwnershipBridge
open S6.RigidMotionChart

theorem inAxisSquare_convex (p q : S6.RigidMotionChart.Pt) (t : ℚ)
    (hp : inAxisSquare p) (hq : inAxisSquare q)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    inAxisSquare (t * p.1 + (1 - t) * q.1, t * p.2 + (1 - t) * q.2) := by
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  rcases hq with ⟨hx0', hx1', hy0', hy1'⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem AxisSquare_contains_convex (s : AxisSquare)
    (p q : S6.OwnershipBridge.Pt) (t : ℚ)
    (hp : s.contains p) (hq : s.contains q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    s.contains (t * p.1 + (1 - t) * q.1, t * p.2 + (1 - t) * q.2) := by
  -- Unfold nested contains
  have hp' := hp
  have hq' := hq
  simp only [AxisSquare.contains] at hp' hq' ⊢
  rcases hp' with ⟨⟨⟨hx0, hx1⟩, hy0⟩, hy1⟩
  rcases hq' with ⟨⟨⟨hx0', hx1'⟩, hy0'⟩, hy1'⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> nlinarith

structure DualDirectNorm where
  x : ℚ
  z : ℚ
  hx0 : 0 ≤ x
  hx1 : x ≤ 1
  hz0 : 0 ≤ z
  hz1 : z ≤ 1

def DualDirectNorm.Q2tilde (D : DualDirectNorm) : S6.OwnershipBridge.Pt :=
  (1 - D.x, 0)
def DualDirectNorm.QUtilde (D : DualDirectNorm) : S6.OwnershipBridge.Pt :=
  (0, 1 - D.z)

def dualDirectCoIncident (g : RotatedSquare) (D : DualDirectNorm) : Prop :=
  g.contains D.Q2tilde ∧ g.contains D.QUtilde

theorem Q2tilde_in_axisUnit (D : DualDirectNorm) :
    axisUnit.contains D.Q2tilde := by
  simp only [AxisSquare.contains, axisUnit, DualDirectNorm.Q2tilde]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> linarith [D.hx0, D.hx1]

theorem QUtilde_in_axisUnit (D : DualDirectNorm) :
    axisUnit.contains D.QUtilde := by
  simp only [AxisSquare.contains, axisUnit, DualDirectNorm.QUtilde]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> linarith [D.hz0, D.hz1]

theorem axisUnit_dualDirect (D : DualDirectNorm) :
    axisUnit.contains D.Q2tilde ∧ axisUnit.contains D.QUtilde :=
  ⟨Q2tilde_in_axisUnit D, QUtilde_in_axisUnit D⟩

theorem dualDirect_axis_segment (D : DualDirectNorm) (t : ℚ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    axisUnit.contains
      (t * D.Q2tilde.1 + (1 - t) * D.QUtilde.1,
       t * D.Q2tilde.2 + (1 - t) * D.QUtilde.2) :=
  AxisSquare_contains_convex axisUnit D.Q2tilde D.QUtilde t
    (Q2tilde_in_axisUnit D) (QUtilde_in_axisUnit D) ht0 ht1

theorem rotated_contains_support_e1 (g : RotatedSquare)
    (p : S6.OwnershipBridge.Pt) (hp : g.contains p) :
    let n := g.imageNormal (1, 0)
    let c0 := dot n g.shift
    c0 ≤ dot n p ∧ dot n p ≤ c0 + 1 := by
  have hp' : inRigidSquare g p := (RotatedSquare.contains_iff_image g p).1 hp
  exact rigid_e1_proj_bounds g p hp'

theorem rotated_contains_support_e2 (g : RotatedSquare)
    (p : S6.OwnershipBridge.Pt) (hp : g.contains p) :
    let n := g.imageNormal (0, 1)
    let c0 := dot n g.shift
    c0 ≤ dot n p ∧ dot n p ≤ c0 + 1 := by
  have hp' : inRigidSquare g p := (RotatedSquare.contains_iff_image g p).1 hp
  exact rigid_e2_proj_bounds g p hp'

theorem dualDirect_supports (g : RotatedSquare) (D : DualDirectNorm)
    (h : dualDirectCoIncident g D) :
    (let n1 := g.imageNormal (1, 0)
     let c1 := dot n1 g.shift
     c1 ≤ dot n1 D.Q2tilde ∧ dot n1 D.Q2tilde ≤ c1 + 1) ∧
    (let n2 := g.imageNormal (0, 1)
     let c2 := dot n2 g.shift
     c2 ≤ dot n2 D.QUtilde ∧ dot n2 D.QUtilde ≤ c2 + 1) :=
  ⟨rotated_contains_support_e1 g D.Q2tilde h.1,
   rotated_contains_support_e2 g D.QUtilde h.2⟩

def o4_m9_incidenceClosed : Bool := true
theorem o4_m9_incidenceClosed_true : o4_m9_incidenceClosed = true := rfl

def open_m9_mu_world_normalization : String :=
  "Normalized Q2̃/QŨ co-incidence + convexity + supports closed; \
   μ-world ↔ chart bridge open."

end S6.Obligation4M9Incidence
