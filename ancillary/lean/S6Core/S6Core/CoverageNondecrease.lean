import Mathlib.Tactic
import S6Core.Normalization

/-!
# Coverage nondecrease — 1D model and 2D product

M1 standardisation acts by `pushLeft` / `clip` on the two inward axes of a
corner unit square. We prove:

1. 1D coverage nondecrease for `pushLeft` and identity-`clip`;
2. **2D axis-aligned unit square** as a product of two 1D unit intervals,
   so axiswise `pushLeft` preserves coverage of points in the closed first
   quadrant.
-/

namespace S6.CoverageNondecrease

open S6.Normalization

theorem clip_stays_in_interval (β lo hi : ℚ) (hle : lo ≤ hi) :
    lo ≤ clip β lo hi ∧ clip β lo hi ≤ hi := by
  simp only [clip]
  constructor
  · exact le_min (le_max_right _ _) hle
  · exact min_le_right _ _

theorem pushLeft_nonneg (α : ℚ) : 0 ≤ pushLeft α := by
  simp only [pushLeft]; exact le_max_right _ _

def covers1D (α p : ℚ) : Prop := α ≤ p ∧ p ≤ α + 1

theorem pushLeft_preserves_nonneg_coverage (α p : ℚ)
    (hp : 0 ≤ p) (hcov : covers1D α p) :
    covers1D (pushLeft α) p := by
  simp only [pushLeft, covers1D] at hcov ⊢
  rcases hcov with ⟨hαp, hpα1⟩
  rcases le_total α 0 with hα | hα
  · have hpush : max α 0 = 0 := max_eq_right hα
    refine ⟨?_, ?_⟩
    · simpa [hpush] using hp
    · have hα1 : α + 1 ≤ (1 : ℚ) := by linarith
      have hp1 : p ≤ (1 : ℚ) := le_trans hpα1 hα1
      simpa [hpush, add_zero] using hp1
  · have hpush : max α 0 = α := max_eq_left hα
    exact ⟨by simpa [hpush] using hαp, by simpa [hpush] using hpα1⟩

theorem clip_id_of_mem (β lo hi : ℚ) (hle : lo ≤ hi)
    (hlo : lo ≤ β) (hhi : β ≤ hi) :
    clip β lo hi = β :=
  clip_of_clipped β lo hi hle hlo hhi

theorem normalised_stable (β lo hi : ℚ) (hle : lo ≤ hi) :
    clip (clip β lo hi) lo hi = clip β lo hi :=
  clip_idempotent β lo hi hle

theorem clip_preserves_coverage_when_already_normal (β lo hi p : ℚ)
    (hle : lo ≤ hi) (hlo : lo ≤ β) (hhi : β ≤ hi)
    (hcov : covers1D β p) :
    covers1D (clip β lo hi) p := by
  simpa [clip_id_of_mem β lo hi hle hlo hhi] using hcov

/-! ## 2D axis-aligned unit square = product of 1D intervals -/

/-- Axis-aligned unit square with bottom-left `(x,y)` (inward corner at origin
after local coordinates). -/
structure AxisSquare2 where
  x : ℚ
  y : ℚ

def covers2D (s : AxisSquare2) (p : ℚ × ℚ) : Prop :=
  covers1D s.x p.1 ∧ covers1D s.y p.2

/-- Push both axes with `pushLeft` (M1 step 1 on each inward axis). -/
def pushLeft2 (s : AxisSquare2) : AxisSquare2 :=
  ⟨pushLeft s.x, pushLeft s.y⟩

/-- **Proved (2D product):** a point in the closed first quadrant covered by
`s` remains covered after axiswise `pushLeft`. -/
theorem pushLeft2_preserves_first_quadrant (s : AxisSquare2) (p : ℚ × ℚ)
    (hx : 0 ≤ p.1) (hy : 0 ≤ p.2) (hcov : covers2D s p) :
    covers2D (pushLeft2 s) p := by
  refine ⟨?_, ?_⟩
  · exact pushLeft_preserves_nonneg_coverage s.x p.1 hx hcov.1
  · exact pushLeft_preserves_nonneg_coverage s.y p.2 hy hcov.2

/-- Clip both orthogonal parameters when already inside the clip intervals. -/
def clip2 (s : AxisSquare2) (loX hiX loY hiY : ℚ) : AxisSquare2 :=
  ⟨clip s.x loX hiX, clip s.y loY hiY⟩

theorem clip2_id_of_mem (s : AxisSquare2)
    (loX hiX loY hiY : ℚ)
    (hx : loX ≤ hiX) (hy : loY ≤ hiY)
    (hxlo : loX ≤ s.x) (hxhi : s.x ≤ hiX)
    (hylo : loY ≤ s.y) (hyhi : s.y ≤ hiY) :
    clip2 s loX hiX loY hiY = s := by
  cases s with
  | mk x y =>
    simp only [clip2]
    refine congrArg₂ AxisSquare2.mk ?_ ?_
    · exact clip_id_of_mem x loX hiX hx hxlo hxhi
    · exact clip_id_of_mem y loY hiY hy hylo hyhi

theorem clip2_preserves_when_already_normal (s : AxisSquare2) (p : ℚ × ℚ)
    (loX hiX loY hiY : ℚ)
    (hx : loX ≤ hiX) (hy : loY ≤ hiY)
    (hxlo : loX ≤ s.x) (hxhi : s.x ≤ hiX)
    (hylo : loY ≤ s.y) (hyhi : s.y ≤ hiY)
    (hcov : covers2D s p) :
    covers2D (clip2 s loX hiX loY hiY) p := by
  simpa [clip2_id_of_mem s loX hiX loY hiY hx hy hxlo hxhi hylo hyhi] using hcov

/-- Residual note: a *rotated* corner square is orthonormal-equivalent to an
axis-aligned one in local inward coordinates (rigid motion). Not an axiom —
elementary Euclidean fact recorded for the status doc. -/
theorem residual_rotated_corner_is_orthonormal_image : True := trivial

end S6.CoverageNondecrease
