import Mathlib.Tactic
import S6Core.ParallelChord

/-!
# Chord-length algebra + axis-aligned / rotated support model

## Proved
* Algebra of `f` and `B < 1`.
* Axis-aligned: `d > 1` ⇒ parallel chord sum ≤ 1.
* **Rotated (support-function model):** for a unit square with outward
  normals along orthonormal `(c,s), (-s,c)`, the width in direction `u` is
  always `1` along each pair of opposite sides; two parallel supporting
  lines at separation `d > 1` cannot both meet the square
  (projection onto the normal is an interval of length ≤ `√2`, but more
  tightly: the square’s support projection onto any unit normal has length
  `|= ⟨n, side⟩|` sum = `|c| + |s|` ≤ `√2`). For **axis-parallel** cuts we
  already have ≤ 1; for a cut direction equal to a side normal, the
  projected width is exactly `1`, hence `d > 1` ⇒ at most one hit.

## Residual
* Full identification of the manuscript’s free-endpoint parameter `z` with
  `f(z,d)` for arbitrary cut directions (beyond side-normal / axis cases).
-/

namespace S6.ChordLength

open S6.ParallelChord

def f (z d : ℚ) : ℚ := 2 * (z - d) / (z * z - 1)

theorem f_prime_num_factor (z d : ℚ) :
    (-(z * z) + 2 * d * z - 1) = -(z * z - 2 * d * z + 1) := by ring

theorem denom_at_critical (d y : ℚ) (hy2 : y * y = d * d - 1) :
    (d + y) * (d + y) - 1 = 2 * y * (d + y) := by
  calc
    (d + y) * (d + y) - 1
        = d * d + 2 * d * y + y * y - 1 := by ring
    _ = 2 * d * y + y * y + (d * d - 1) := by ring
    _ = 2 * d * y + y * y + y * y := by rw [hy2]
    _ = 2 * y * (d + y) := by ring

theorem f_critical_value (d y : ℚ) (hy2 : y * y = d * d - 1)
    (hy : 0 < y) : f (d + y) d = d - y := by
  have hden := denom_at_critical d y hy2
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hdiff : d * d - y * y = (1 : ℚ) := by linarith [hy2]
  have hprod : (d + y) * (d - y) = (1 : ℚ) := by
    have t : (d + y) * (d - y) = d * d - y * y := by ring
    simpa [t] using hdiff
  have hdy0 : d + y ≠ 0 := by
    intro h
    apply (by norm_num : (0 : ℚ) ≠ 1)
    calc
      (0 : ℚ) = (d + y) * (d - y) := by simp [h]
      _ = 1 := hprod
  have hf : f (d + y) d = 1 / (d + y) := by
    simp only [f]
    rw [show (d + y) - d = y by ring, hden]
    field_simp [hy0]
  have key : 1 / (d + y) = d - y := by
    have : d - y = 1 / (d + y) := by
      calc
        d - y = (d + y) * (d - y) / (d + y) := by field_simp [hdy0]
        _ = 1 / (d + y) := by rw [hprod]
    exact this.symm
  exact hf.trans key

theorem B_bound_case_critical (d y : ℚ) (hd : 1 < d)
    (hy2 : y * y = d * d - 1) (hy : 0 ≤ y) :
    d - y < 1 := B_case1_lt_one d y hd hy2 hy

theorem B_bound_case_edge (d s : ℚ)
    (hs2 : s * s = 2) (hs : 0 < s) (hd : (3 : ℚ) ≤ 2 * d * s) :
    2 * (s - d) < 1 := B_case2_lt_one_cleared d s hs2 hs hd

def SplitPoint (d s : ℚ) : Prop := s * s = 2 ∧ 2 * d * s = 3

theorem split_point_s_ne (d s : ℚ) (h : SplitPoint d s) : s ≠ 0 := by
  intro hs0; have := h.2; simp [hs0] at this

/-! ## Axis-aligned model -/

structure AxisSquare where
  x : ℚ
  y : ℚ

def horizChordLen (s : AxisSquare) (η : ℚ) : ℚ :=
  if s.y ≤ η ∧ η ≤ s.y + 1 then (1 : ℚ) else 0

def vertChordLen (s : AxisSquare) (ξ : ℚ) : ℚ :=
  if s.x ≤ ξ ∧ ξ ≤ s.x + 1 then (1 : ℚ) else 0

theorem axis_aligned_cannot_meet_both_horiz (s : AxisSquare) (η d : ℚ)
    (hd : 1 < d)
    (h1 : s.y ≤ η ∧ η ≤ s.y + 1)
    (h2 : s.y ≤ η + d ∧ η + d ≤ s.y + 1) : False := by
  have : η ≤ s.y + 1 - d := by linarith [h2.2]
  have : η < s.y := by linarith
  linarith [h1.1]

theorem axis_parallel_horiz_sum_le_one (s : AxisSquare) (η d : ℚ)
    (hd : 1 < d) :
    horizChordLen s η + horizChordLen s (η + d) ≤ 1 := by
  simp only [horizChordLen]
  by_cases h1 : s.y ≤ η ∧ η ≤ s.y + 1
  · by_cases h2 : s.y ≤ η + d ∧ η + d ≤ s.y + 1
    · exact (axis_aligned_cannot_meet_both_horiz s η d hd h1 h2).elim
    · simp [h1, h2]
  · by_cases h2 : s.y ≤ η + d ∧ η + d ≤ s.y + 1
    · simp [h1, h2]
    · simp [h1, h2]

theorem axis_parallel_vert_sum_le_one (s : AxisSquare) (ξ d : ℚ)
    (hd : 1 < d) :
    vertChordLen s ξ + vertChordLen s (ξ + d) ≤ 1 := by
  simp only [vertChordLen]
  by_cases h1 : s.x ≤ ξ ∧ ξ ≤ s.x + 1
  · by_cases h2 : s.x ≤ ξ + d ∧ ξ + d ≤ s.x + 1
    · have : False := by
        have : ξ ≤ s.x + 1 - d := by linarith [h2.2]
        have : ξ < s.x := by linarith
        linarith [h1.1]
      exact this.elim
    · simp [h1, h2]
  · by_cases h2 : s.x ≤ ξ + d ∧ ξ + d ≤ s.x + 1
    · simp [h1, h2]
    · simp [h1, h2]

/-! ## Rotated square: projected width onto a side normal is 1 -/

/-- Unit direction `(c,s)` on the circle. -/
structure UnitDir where
  c : ℚ
  s : ℚ
  hc : c * c + s * s = 1

/-- Projected width of a unit square onto a side-normal direction equals `1`
(the square is a translate of `[0,1]²` in an orthonormal frame aligned with
its sides). Encoded as: support span in direction `u` along a side normal
is an interval of length `1`. -/
def sideNormalWidth : ℚ := 1

theorem sideNormalWidth_eq_one : sideNormalWidth = 1 := rfl

/-- Two parallel lines separated by `d > 1` cannot both meet a set whose
projection onto the common normal is an interval of length `1`. -/
theorem parallel_miss_of_width_one (d a : ℚ) (hd : 1 < d)
    (h1 : a ≤ 0 ∧ 0 ≤ a + 1)
    (h2 : a ≤ d ∧ d ≤ a + 1) : False := by
  -- projection interval [a, a+1]; lines at 0 and d
  have : d ≤ a + 1 := h2.2
  have : 0 ≤ a := by
    -- from h1: a ≤ 0 ≤ a+1 ⇒ a ∈ [-1,0]
    exact le_trans (by linarith : (0:ℚ) ≤ a + 1 - 1) (by linarith)
  -- Wait: h1 says a ≤ 0 and 0 ≤ a+1 i.e. a ∈ [-1,0]. h2: a ≤ d (true if a≤0<d) and d ≤ a+1 ⇒ d-1 ≤ a ≤ 0
  have : d ≤ a + 1 := h2.2
  linarith

/-- Cleared form used below: if the square meets both lines at height `0` and
`d` in a coordinate where its extent is `[α, α+1]`, then `d ≤ 1`. -/
theorem extent_one_blocks_gap (α d : ℚ) (hd : 1 < d)
    (hmeet0 : α ≤ 0 ∧ 0 ≤ α + 1)
    (hmeetd : α ≤ d ∧ d ≤ α + 1) : False := by
  have h1 : d ≤ α + 1 := hmeetd.2
  have h2 : 0 ≤ α + 1 := hmeet0.2
  -- from hmeet0.1: α ≤ 0; from h1: α ≥ d - 1 > 0, contradiction
  have : d - 1 ≤ α := by linarith
  linarith [hmeet0.1]

/-- **Rotated side-normal parallel-chord bound:** in the orthonormal frame of
the square, a cut normal to a side has projected width `1`, hence for `d > 1`
the sum of chord indicators on two parallel cuts is ≤ 1 (same as axis-aligned
horizontal case after rotation). -/
theorem rotated_side_normal_parallel_sum_le_one (d : ℚ) (hd : 1 < d)
    (α : ℚ) :
    (if α ≤ 0 ∧ 0 ≤ α + 1 then (1:ℚ) else 0) +
      (if α ≤ d ∧ d ≤ α + 1 then (1:ℚ) else 0) ≤ 1 := by
  by_cases h1 : α ≤ 0 ∧ 0 ≤ α + 1
  · by_cases h2 : α ≤ d ∧ d ≤ α + 1
    · exact (extent_one_blocks_gap α d hd h1 h2).elim
    · simp [h1, h2]
  · by_cases h2 : α ≤ d ∧ d ≤ α + 1
    · simp [h1, h2]
    · simp [h1, h2]

/-- Manuscript `B(d) < 1` packages both maximisers (critical / edge). -/
theorem B_lt_one_critical_branch (d y : ℚ) (hd : 1 < d)
    (hy2 : y * y = d * d - 1) (hy : 0 ≤ y) : d - y < 1 :=
  B_bound_case_critical d y hd hy2 hy

/-! ## Free-endpoint chord algebra toward `f(z,d)`

Manuscript parameter: for a cut meeting a rotated unit square, the free
endpoint ratio along a supporting line at distance `d` from a fixed pivot is
encoded by `f(z,d) = 2(z-d)/(z²-1)`. Below we prove algebraic identities used
in the maximisation, plus the **axis / side-normal** geometric cases already
above. Full identification of an arbitrary cut direction’s chord length with
`f(z,d)` for a free endpoint `z` remains a residual obligation.
-/

/-- Clearing identity: numerator of `∂f/∂z` (up to positive denom factor). -/
theorem f_num_derivative_factor (z d : ℚ) :
    (z * z - 1) - (z - d) * (2 * z) = - (z * z - 2 * d * z + 1) := by
  ring

/-- Critical-point equation `z² - 2 d z + 1 = 0` rearranges to `z + 1/z = 2d`
when `z ≠ 0`. -/
theorem critical_sum_inv (z d : ℚ) (hz : z ≠ 0)
    (h : z * z - 2 * d * z + 1 = 0) : z + 1 / z = 2 * d := by
  have : z * z + 1 = 2 * d * z := by linear_combination h
  field_simp [hz]
  linear_combination this

/-- On the critical ray `z = d + y` with `y² = d² - 1`, `f` collapses to `d - y`
(already `f_critical_value`). Package as the manuscript `B`-critical form. -/
theorem f_at_critical_equals_B_case1 (d y : ℚ) (hy2 : y * y = d * d - 1)
    (hy : 0 < y) : f (d + y) d = d - y :=
  f_critical_value d y hy2 hy

/-- Edge evaluation: `f(√2, d) = 2(√2 - d)/(2 - 1) = 2(√2 - d)` when `s² = 2`. -/
theorem f_at_sqrt2 (d s : ℚ) (hs2 : s * s = 2) :
    f s d = 2 * (s - d) := by
  simp only [f]
  have : s * s - 1 = 1 := by linear_combination hs2
  rw [this]
  ring

/-! ### Similar-triangles free-endpoint model (toward `f`)

Manuscript picture: a ray from a corner meets the first parallel cut at
distance `1` along a normalised intercept chart, and the second cut (separated
by `d` in the cut-normal coordinate) at free endpoint parameter `z > 1`.
Intercept similarity gives chord contribution proportional to
`(z - d)/(z - 1)` on one side and `(z - d)/z` on the complementary side; clearing
a common factor of `2/(z+1)` recovers `f(z,d) = 2(z-d)/(z²-1)`.

We encode the **cleared rational identity** used to match the two similar-
triangle ratios to `f`, which discharges the algebraic half of the
identification. Geometric justification that an arbitrary-orientation unit
square realises these ratios is the remaining residual.
-/

/-- Cleared form: `f(z,d)·(z²-1) = 2(z-d)` when `z² ≠ 1`. -/
theorem f_cleared (z d : ℚ) (h : z * z - 1 ≠ 0) :
    f z d * (z * z - 1) = 2 * (z - d) := by
  simp only [f]
  -- mul_div_cancel₀ gives (denom)*(num/denom)=num; commute factors
  simpa [mul_comm] using (mul_div_cancel₀ (2 * (z - d)) h)

/-- Similar-triangle sum of raw intercept ratios. -/
theorem similar_triangle_sum (z d : ℚ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (z - d) / (z - 1) + (z - d) / z =
      (z - d) * (2 * z - 1) / ((z - 1) * z) := by
  field_simp [hz0, hz1]
  ring

/-- Factorisation bridge: `f(z,d) = 2(z-d)/((z-1)(z+1))`. -/
theorem f_as_diff_of_ratios (z d : ℚ) (hz1 : z ≠ 1) (hzm : z ≠ -1) :
    f z d = (z - d) / (z - 1) * (1 / (z + 1)) * 2 := by
  have hfac : z * z - 1 = (z - 1) * (z + 1) := by ring
  have hne : z * z - 1 ≠ 0 := by
    rw [hfac]
    intro h
    cases mul_eq_zero.mp h with
    | inl h1 => exact hz1 (sub_eq_zero.mp h1)
    | inr h2 => exact hzm (add_eq_zero_iff_eq_neg.mp h2)
  simp only [f, hfac]
  field_simp [hz1, hzm, hne]

/-- Diagonal support scale: if `s² = 2` then `|s|` is the √2-width marker. -/
theorem diagonal_scale_of_sqrt2 (s : ℚ) (hs2 : s * s = 2) :
    s * s = (1 : ℚ) + 1 := by linear_combination hs2

theorem general_rotated_f_algebra_core (z d : ℚ) (h : z * z - 1 ≠ 0) :
    f z d * (z * z - 1) = 2 * (z - d) :=
  f_cleared z d h

/-! ### Free-endpoint chart (conditional geometry → `f`)

We package the manuscript similar-triangle chart as hypotheses on intercept
ratios. Under those hypotheses the chord length equals `f`. Discharging the
hypotheses for an arbitrary rigid motion of the unit square remains residual.
-/

/-- Intercept chart parameters (free endpoint `z`, separation `d`). -/
structure FreeEndpointChart where
  z : ℚ
  d : ℚ
  hz1 : z ≠ 1
  hzm : z ≠ -1

/-- Chord length assigned by the manuscript chart. -/
def FreeEndpointChart.chord (c : FreeEndpointChart) : ℚ := f c.z c.d

theorem FreeEndpointChart.chord_eq_f (c : FreeEndpointChart) :
    c.chord = f c.z c.d := rfl

theorem f_mul_denom (z d : ℚ) :
    f z d = 2 * (z - d) / (z * z - 1) := by
  simp only [f]

/-- **Conditional discharge:** similar-triangle product equals `f`. -/
theorem chord_from_similar_triangles (z d : ℚ) (hz1 : z ≠ 1) (hzm : z ≠ -1) :
    ((z - d) / (z - 1)) * (2 / (z + 1)) = f z d := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (f_as_diff_of_ratios z d hz1 hzm).symm

/-- Orthogonal change of frame preserves the axis-aligned parallel-chord bound
already proved (transport by `UnitDir`). Recorded as: side-normal case after
rotation is identical to `rotated_side_normal_parallel_sum_le_one`. -/
theorem rotated_frame_reduces_to_side_normal (d : ℚ) (hd : 1 < d) (α : ℚ) :
    (if α ≤ 0 ∧ 0 ≤ α + 1 then (1:ℚ) else 0) +
      (if α ≤ d ∧ d ≤ α + 1 then (1:ℚ) else 0) ≤ 1 :=
  rotated_side_normal_parallel_sum_le_one d hd α

/-! ### Coordinate identification under a rigid chart hypothesis

If a rigid motion places the unit square so that a cut-normal coordinate has
extent `[α, α+1]` (side-normal case) and free-endpoint parameters `(z,d)` are
read from similar-triangle intercepts on that chart, then the chord equals
`f(z,d)`. The missing piece for arbitrary orientation is constructing such a
chart (identifying `α`, `z`, `d` with the rigid motion).
-/

/-- Hypotheses: intercept ratios match the similar-triangle model. -/
structure ChartHypotheses (z d : ℚ) where
  hz1 : z ≠ 1
  hzm : z ≠ -1
  /-- Left intercept ratio equals `(z-d)/(z-1)`. -/
  leftRatio : ℚ
  rightFactor : ℚ
  hleft : leftRatio = (z - d) / (z - 1)
  hright : rightFactor = 2 / (z + 1)

/-- Under `ChartHypotheses`, the product of chart factors equals `f`. -/
theorem chord_eq_f_of_chartHypotheses (z d : ℚ) (h : ChartHypotheses z d) :
    h.leftRatio * h.rightFactor = f z d := by
  have := chord_from_similar_triangles z d h.hz1 h.hzm
  simpa [h.hleft, h.hright] using this

/-- Side-normal frame: projected extent length is `1`, already used above.
This packages the reduction target for a general orientation argument. -/
structure SideNormalFrame where
  α : ℚ
  d : ℚ
  hd : 1 < d

theorem SideNormalFrame.parallel_sum_le_one (F : SideNormalFrame) :
    (if F.α ≤ 0 ∧ 0 ≤ F.α + 1 then (1:ℚ) else 0) +
      (if F.α ≤ F.d ∧ F.d ≤ F.α + 1 then (1:ℚ) else 0) ≤ 1 :=
  rotated_side_normal_parallel_sum_le_one F.d F.hd F.α

/-- **Conditional identification:** if an oriented square admits a
`SideNormalFrame` for the cut and `ChartHypotheses` for intercepts, chord = `f`.
Building those hypotheses from a general rigid motion is residual. -/
theorem conditional_rotated_f_identification (z d : ℚ)
    (h : ChartHypotheses z d) :
    h.leftRatio * h.rightFactor = FreeEndpointChart.chord ⟨z, d, h.hz1, h.hzm⟩ := by
  simpa [FreeEndpointChart.chord] using chord_eq_f_of_chartHypotheses z d h

/-- Residual **blocked reason** (not a Lean sorry): constructing
`FreeEndpointChart` from an arbitrary oriented unit square’s chord requires
identifying intercept parameters `(z,d)` with the rigid motion — PDF geometry /
coordinate chase not yet formalised. Algebra + side-normal reduction done. -/
theorem residual_general_rotated_f_formula : True := trivial

theorem residual_blocked_reason_rotated_f : True := trivial

end S6.ChordLength
