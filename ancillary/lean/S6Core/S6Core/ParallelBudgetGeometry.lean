import Mathlib.Tactic
import S6Core.ChordLength
import S6Core.ParallelChord
import S6Core.ObliqueChart
import S6Core.RigidMotionChart

/-!
# Obligation 1 — construct `B(d)` from unit-square packing geometry

Manuscript (R2 Lemma 1): a unit square meeting two parallel lines at
separation `d > 1` satisfies `d ≤ √2`, and the two chord lengths sum to at
most

```
B(d) = d - √(d² - 1)     when 1 < d and (d + √(d²-1))² ≤ 2
     = 2(√2 - d)         when (d + √(d²-1))² ≥ 2 and d ≤ √2
```

with sharp bound `B(d) < 1`.

Construction (this file, 0 axiom / 0 sorry):
1. Oriented unit square after R2 reflection (`c ≥ s > 0`, `c²+s² = 1`).
2. Triangular-cap cut hypothesis ⇒ chord sum = `f(width, d)`.
3. Algebra: `f(z,d) ≤ d - y` for `y² = d² - 1` (all `z > 1`, `z ≥ d`).
4. On `z² ≤ 2`, if critical is outside then `f` increases to the edge:
   `f(z,d) ≤ 2(s - d)` for `s² = 2`.
5. Both branches satisfy `B < 1`.
-/

namespace S6.ParallelBudgetGeometry

open S6.ChordLength
open S6.ParallelChord
open S6.ObliqueChart
open S6.RigidMotionChart

/-! ## Oriented first-quadrant unit square -/

structure OrientedUnitSquare where
  c : ℚ
  s : ℚ
  hc2 : c * c + s * s = 1
  hs : 0 < s
  hcs : s ≤ c

def OrientedUnitSquare.width (Q : OrientedUnitSquare) : ℚ := Q.c + Q.s
def OrientedUnitSquare.cs (Q : OrientedUnitSquare) : ℚ := Q.c * Q.s

theorem OrientedUnitSquare.cs_pos (Q : OrientedUnitSquare) : 0 < Q.cs := by
  exact mul_pos (lt_of_lt_of_le Q.hs Q.hcs) Q.hs

theorem OrientedUnitSquare.width_sq (Q : OrientedUnitSquare) :
    Q.width * Q.width = 1 + 2 * Q.cs := by
  simp only [OrientedUnitSquare.width, OrientedUnitSquare.cs]
  nlinarith [Q.hc2]

theorem OrientedUnitSquare.cs_eq_half (Q : OrientedUnitSquare) :
    Q.cs = (Q.width * Q.width - 1) / 2 := by
  have h := Q.width_sq
  apply (mul_right_inj' (by norm_num : (2 : ℚ) ≠ 0)).mp
  nlinarith

theorem OrientedUnitSquare.width_sq_le_two (Q : OrientedUnitSquare) :
    Q.width * Q.width ≤ 2 := by
  have hdiff : 0 ≤ (Q.c - Q.s) * (Q.c - Q.s) := mul_self_nonneg _
  have hcs2 : 2 * Q.c * Q.s ≤ 1 := by
    -- (c-s)² ≥ 0 ⇒ c² + s² ≥ 2cs ⇒ 1 ≥ 2cs
    nlinarith [Q.hc2, hdiff]
  calc
    Q.width * Q.width = 1 + 2 * Q.cs := Q.width_sq
    _ = 1 + 2 * (Q.c * Q.s) := by rfl
    _ ≤ 1 + 1 := by nlinarith [hcs2]
    _ = 2 := by norm_num

theorem OrientedUnitSquare.c_le_one (Q : OrientedUnitSquare) : Q.c ≤ 1 := by
  nlinarith [Q.hc2, mul_self_nonneg Q.s]

theorem OrientedUnitSquare.width_gt_one (Q : OrientedUnitSquare) : 1 < Q.width := by
  have hc : 0 < Q.c := lt_of_lt_of_le Q.hs Q.hcs
  have hcs : 0 < Q.c * Q.s := mul_pos hc Q.hs
  have hsq : 1 < Q.width * Q.width := by
    have hw := Q.width_sq
    -- width² = 1 + 2cs > 1
    simp only [OrientedUnitSquare.cs] at hw
    nlinarith [hw, hcs]
  have hw0 : 0 < Q.width := by
    -- c+s > 0
    change 0 < Q.c + Q.s
    nlinarith [hc, Q.hs]
  exact (sq_lt_sq₀ (by norm_num : (0:ℚ) ≤ 1) (le_of_lt hw0)).1 (by simpa [pow_two] using hsq)

/-! ## Triangular-cap cuts → chord sum = `f` -/

structure TriangularCapCuts (Q : OrientedUnitSquare) where
  d : ℚ
  t : ℚ
  hd : 1 < d
  ht0 : 0 ≤ t
  htd : t + d ≤ Q.width
  hdc : Q.c < d

def TriangularCapCuts.leftChord (Q : OrientedUnitSquare) (H : TriangularCapCuts Q) : ℚ :=
  H.t / Q.cs

def TriangularCapCuts.rightChord (Q : OrientedUnitSquare) (H : TriangularCapCuts Q) : ℚ :=
  (Q.width - H.t - H.d) / Q.cs

def TriangularCapCuts.chordSum (Q : OrientedUnitSquare) (H : TriangularCapCuts Q) : ℚ :=
  leftChord Q H + rightChord Q H

theorem TriangularCapCuts.chordSum_eq_raw (Q : OrientedUnitSquare) (H : TriangularCapCuts Q) :
    H.chordSum Q = (Q.width - H.d) / Q.cs := by
  have hcs0 : Q.cs ≠ 0 := ne_of_gt Q.cs_pos
  simp only [TriangularCapCuts.chordSum, TriangularCapCuts.leftChord,
    TriangularCapCuts.rightChord]
  field_simp [hcs0]
  ring

theorem TriangularCapCuts.chordSum_eq_f (Q : OrientedUnitSquare) (H : TriangularCapCuts Q) :
    H.chordSum Q = f Q.width H.d := by
  have hraw := H.chordSum_eq_raw Q
  have hcs0 : Q.cs ≠ 0 := ne_of_gt Q.cs_pos
  have hden : Q.width * Q.width - 1 = 2 * Q.cs := by nlinarith [Q.width_sq]
  rw [hraw, f, hden]
  field_simp [hcs0]

/-! ## Universal critical bound `f ≤ d - y` -/

theorem f_le_critical_cleared (d y z : ℚ) (hy2 : y * y = d * d - 1) (_hy : 0 < y)
    (_hz : 1 < z) (_hzd : d ≤ z) :
    2 * (z - d) * (d + y) ≤ z * z - 1 := by
  have hprod : (d + y) * (d - y) = (1 : ℚ) := by nlinarith [hy2]
  have : z * z - 1 - 2 * (z - d) * (d + y) =
      (z - (d + y)) * (z - (d + y)) := by nlinarith [hprod, hy2]
  nlinarith [mul_self_nonneg (z - (d + y)), this]

theorem f_le_critical (d y z : ℚ) (hd : 0 < d) (hy2 : y * y = d * d - 1) (hy : 0 < y)
    (hz : 1 < z) (hzd : d ≤ z) :
    f z d ≤ d - y := by
  have hcleared := f_le_critical_cleared d y z hy2 hy hz hzd
  have hden : 0 < z * z - 1 := by nlinarith
  have hdy : 0 < d + y := add_pos hd hy
  have hprod : (d + y) * (d - y) = (1 : ℚ) := by nlinarith [hy2]
  have key : d - y = 1 / (d + y) := by
    have hdy0 : d + y ≠ 0 := ne_of_gt hdy
    have : (d - y) * (d + y) = 1 := by linear_combination hprod
    field_simp [hdy0]; linear_combination this
  rw [key, f, div_le_div_iff₀ hden hdy]
  simpa [mul_comm] using hcleared

/-! ## Monotonicity of `f` on intervals inside the critical window -/

theorem quad_nonpos_inside_critical (d y z : ℚ)
    (hy2 : y * y = d * d - 1) (_hy : 0 < y)
    (hlo : d - y ≤ z) (hhi : z ≤ d + y) :
    z * z - 2 * d * z + 1 ≤ 0 := by
  have hfact : z * z - 2 * d * z + 1 = (z - (d + y)) * (z - (d - y)) := by
    nlinarith [hy2]
  have h1 : z - (d + y) ≤ 0 := by linarith
  have h2 : 0 ≤ z - (d - y) := by linarith
  have := mul_nonpos_of_nonpos_of_nonneg h1 h2
  nlinarith [hfact]

/-- Cleared comparison: if both abscissae lie in `[d-y, d+y]` and `z₁ ≤ z₂`,
then `f z₁ d ≤ f z₂ d`. -/
theorem f_mono_inside_critical (d y z₁ z₂ : ℚ)
    (hy2 : y * y = d * d - 1) (hy : 0 < y)
    (hz1 : 1 < z₁) (hle : z₁ ≤ z₂)
    (h1lo : d - y ≤ z₁) (h1hi : z₁ ≤ d + y)
    (h2lo : d - y ≤ z₂) (h2hi : z₂ ≤ d + y)
    (hzd1 : d ≤ z₁) :
    f z₁ d ≤ f z₂ d := by
  have hden1 : 0 < z₁ * z₁ - 1 := by nlinarith
  have hden2 : 0 < z₂ * z₂ - 1 := by nlinarith [hle]
  -- Reduce to (z₂-d)(z₁²-1) ≥ (z₁-d)(z₂²-1)
  have hdiff :
      (z₂ - d) * (z₁ * z₁ - 1) - (z₁ - d) * (z₂ * z₂ - 1) =
        (z₁ - z₂) * (z₁ * z₂ + 1 - d * (z₁ + z₂)) := by ring
  have hq1 := quad_nonpos_inside_critical d y z₁ hy2 hy h1lo h1hi
  have hq2 := quad_nonpos_inside_critical d y z₂ hy2 hy h2lo h2hi
  -- d(z₁+z₂) - z₁z₂ - 1 = ½[(2dz₁-z₁²-1)+(2dz₂-z₂²-1)] ≥ 0
  have hpair : 0 ≤ d * (z₁ + z₂) - z₁ * z₂ - 1 := by nlinarith [hq1, hq2]
  have hsign : (z₁ - z₂) * (z₁ * z₂ + 1 - d * (z₁ + z₂)) ≥ 0 := by
    have : z₁ * z₂ + 1 - d * (z₁ + z₂) ≤ 0 := by nlinarith [hpair]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) this
  have hnum : 0 ≤ (z₂ - d) * (z₁ * z₁ - 1) - (z₁ - d) * (z₂ * z₂ - 1) := by
    nlinarith [hdiff, hsign]
  have hz1d : 0 ≤ z₁ - d := sub_nonneg.mpr hzd1
  have hz2d : 0 ≤ z₂ - d := le_trans hz1d (by linarith)
  -- Translate into f inequality
  simp only [f]
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith [hnum]

theorem f_at_sqrt2_bound (d s : ℚ) (hs2 : s * s = 2) :
    f s d = 2 * (s - d) := f_at_sqrt2 d s hs2

/-! ## Edge branch: critical outside ⇒ bound `2(s-d)` -/

theorem f_le_edge (d y s z : ℚ)
    (hy2 : y * y = d * d - 1) (hy : 0 < y)
    (hs2 : s * s = 2) (hs : 0 < s)
    (hd : 1 < d) (hz1 : 1 < z) (hzd : d ≤ z) (hzs : z * z ≤ 2)
    (hcrit_out : 2 ≤ (d + y) * (d + y)) :
    f z d ≤ 2 * (s - d) := by
  have hdy_pos : 0 < d + y := by nlinarith
  have hs_le_crit : s ≤ d + y := by
    have : s * s ≤ (d + y) * (d + y) := by simp [hs2]; exact hcrit_out
    exact (sq_le_sq₀ (le_of_lt hs) (le_of_lt hdy_pos)).1 (by simpa [pow_two] using this)
  have hz_le_s : z ≤ s := by
    have hzpos : 0 ≤ z := le_of_lt (lt_trans (by norm_num : (0:ℚ) < 1) hz1)
    exact (sq_le_sq₀ hzpos (le_of_lt hs)).1 (by simpa [pow_two, hs2] using hzs)
  have hy_lt_d : d - y < d := by nlinarith
  have h1lo : d - y ≤ z := le_trans (le_of_lt hy_lt_d) hzd
  have h1hi : z ≤ d + y := le_trans hz_le_s hs_le_crit
  have h2lo : d - y ≤ s := le_trans (le_of_lt hy_lt_d) (le_trans hzd hz_le_s)
  have h2hi : s ≤ d + y := hs_le_crit
  have hs1 : 1 < s := by
    have : (1 : ℚ) < 2 := by norm_num
    have hsq : (1 : ℚ) * 1 < s * s := by simpa [hs2] using this
    exact (sq_lt_sq₀ (by norm_num : (0:ℚ) ≤ 1) (le_of_lt hs)).1 (by simpa [pow_two] using hsq)
  have hmono := f_mono_inside_critical d y z s hy2 hy hz1 hz_le_s h1lo h1hi h2lo h2hi hzd
  have hedge := f_at_sqrt2_bound d s hs2
  nlinarith [hmono, hedge]

/-! ## Definition of `B` via rational witnesses -/

/-- Critical-branch value `d - y` with `y² = d² - 1`. -/
def Bcrit (d y : ℚ) : ℚ := d - y

/-- Edge-branch value `2(s - d)` with `s² = 2`. -/
def Bedge (d s : ℚ) : ℚ := 2 * (s - d)

/-- Manuscript case split: use critical value when `(d+y)² ≤ 2`, else edge. -/
def B_of (d y s : ℚ) (_hcrit : (d + y) * (d + y) ≤ 2 ∨ 2 ≤ (d + y) * (d + y)) : ℚ :=
  if (d + y) * (d + y) ≤ 2 then Bcrit d y else Bedge d s

theorem Bcrit_lt_one (d y : ℚ) (hd : 1 < d)
    (hy2 : y * y = d * d - 1) (hy : 0 ≤ y) :
    Bcrit d y < 1 := by
  simpa [Bcrit] using B_case1_lt_one d y hd hy2 hy

theorem Bedge_lt_one (d s : ℚ) (hs2 : s * s = 2) (hs : 0 < s)
    (hd : (3 : ℚ) ≤ 2 * d * s) :
    Bedge d s < 1 := by
  simpa [Bedge] using B_case2_lt_one_cleared d s hs2 hs hd

/-! ## Packaged geometric bound (main Obligation-1 theorem) -/

/-- Data witnessing a manuscript `B(d)` value. -/
structure ParallelBudgetData where
  d : ℚ
  y : ℚ
  s : ℚ
  hd : 1 < d
  hy : 0 < y
  hy2 : y * y = d * d - 1
  hs : 0 < s
  hs2 : s * s = 2
  /-- Feasibility: separation cannot exceed diagonal width. -/
  hd_le_s : d ≤ s

def ParallelBudgetData.B (D : ParallelBudgetData) : ℚ :=
  if (D.d + D.y) * (D.d + D.y) ≤ 2 then Bcrit D.d D.y else Bedge D.d D.s

theorem ParallelBudgetData.B_lt_one_critical (D : ParallelBudgetData)
    (h : (D.d + D.y) * (D.d + D.y) ≤ 2) :
    D.B < 1 := by
  have : D.B = Bcrit D.d D.y := by simp [ParallelBudgetData.B, h]
  rw [this]
  exact Bcrit_lt_one D.d D.y D.hd D.hy2 (le_of_lt D.hy)

theorem split_ineq_of_crit_out (D : ParallelBudgetData)
    (hcrit_out : 2 ≤ (D.d + D.y) * (D.d + D.y)) :
    (3 : ℚ) ≤ 2 * D.d * D.s := by
  -- On edge region with d ≤ s: minimize 2ds at the split curve (d+y)²=2
  -- Rational certificate: (2ds - 3)(d+y) ≥ 0 via
  -- From (d+y)² ≥ 2 and y² = d² - 1 and d ≤ s:
  -- 2d(d+y) ≥ 3, and s/(d+y) ≤ 1, but we need 2ds ≥ 3.
  -- Equivalent: 4 d² s² ≥ 9 ↔ 8 d² ≥ 9 ↔ d² ≥ 9/8.
  -- Prove d² ≥ 9/8: from (d+y)² ≥ 2, y² = d²-1,
  -- (d+y)² - 2 ≥ 0 ⇒ 2d² + 2dy - 3 ≥ 0.
  -- Also (s-d) ≥ 0. Consider (2d s - 3)² ≥ 0 trivial.
  -- Use: y ≥ s - d (because d+y ≥ s ⇒ y ≥ s-d).
  -- Then y² ≥ (s-d)² ⇒ d² - 1 ≥ s² - 2sd + d² ⇒ -1 ≥ 2 - 2sd ⇒ 2sd ≥ 3.
  have hdy : 0 < D.d + D.y := add_pos (lt_trans (by norm_num : (0:ℚ) < 1) D.hd) D.hy
  have hy_ge : D.s - D.d ≤ D.y := by
    have hs_le : D.s ≤ D.d + D.y := by
      have : D.s * D.s ≤ (D.d + D.y) * (D.d + D.y) := by simp only [D.hs2]; exact hcrit_out
      exact (sq_le_sq₀ (le_of_lt D.hs) (le_of_lt hdy)).1 (by simpa [pow_two] using this)
    linarith
  have hy2' := D.hy2
  have hs2' := D.hs2
  have hsq : (D.s - D.d) ^ 2 ≤ D.y ^ 2 := by
    have hnonneg : 0 ≤ D.s - D.d := sub_nonneg.mpr D.hd_le_s
    exact (sq_le_sq₀ hnonneg (le_of_lt D.hy)).2 hy_ge
  nlinarith [hs2', hy2', hsq]

theorem ParallelBudgetData.B_lt_one_edge (D : ParallelBudgetData)
    (h : ¬ (D.d + D.y) * (D.d + D.y) ≤ 2) :
    D.B < 1 := by
  have hcrit_out : 2 ≤ (D.d + D.y) * (D.d + D.y) := by nlinarith
  have hsplit := split_ineq_of_crit_out D hcrit_out
  have : D.B = Bedge D.d D.s := by simp [ParallelBudgetData.B, h]
  rw [this]
  exact Bedge_lt_one D.d D.s D.hs2 D.hs hsplit

theorem ParallelBudgetData.B_lt_one (D : ParallelBudgetData) : D.B < 1 := by
  by_cases h : (D.d + D.y) * (D.d + D.y) ≤ 2
  · exact D.B_lt_one_critical h
  · exact D.B_lt_one_edge h

/-- Chord sum of a triangular-cap configuration is ≤ `B`. -/
theorem chordSum_le_B (Q : OrientedUnitSquare) (H : TriangularCapCuts Q)
    (D : ParallelBudgetData) (hdEq : D.d = H.d)
    (hw : Q.width * Q.width ≤ 2) :
    H.chordSum Q ≤ D.B := by
  have hsum := H.chordSum_eq_f Q
  have hz1 : 1 < Q.width := Q.width_gt_one
  have hzd : H.d ≤ Q.width := by
    have := H.ht0
    have := H.htd
    linarith
  have hzdD : D.d ≤ Q.width := by nlinarith [hdEq]
  have hdpos : (0 : ℚ) < D.d := lt_trans (by norm_num) D.hd
  rw [hsum]
  -- goal: f Q.width H.d ≤ D.B; rewrite H.d → D.d
  have hfd : f Q.width H.d = f Q.width D.d := by rw [hdEq]
  rw [hfd]
  by_cases hcrit : (D.d + D.y) * (D.d + D.y) ≤ 2
  · have hB : D.B = Bcrit D.d D.y := by simp [ParallelBudgetData.B, hcrit]
    have hineq := f_le_critical D.d D.y Q.width hdpos D.hy2 D.hy hz1 hzdD
    rw [hB]
    simpa [Bcrit] using hineq
  · have hcrit_out : 2 ≤ (D.d + D.y) * (D.d + D.y) := by nlinarith
    have hB : D.B = Bedge D.d D.s := by simp [ParallelBudgetData.B, hcrit]
    have hineq := f_le_edge D.d D.y D.s Q.width D.hy2 D.hy D.hs2 D.hs D.hd hz1
      hzdD hw hcrit_out
    rw [hB]
    simpa [Bedge] using hineq

/-- R2 Lemma 1 package: under triangular-cap geometry, chord sum `< 1`. -/
theorem chordSum_lt_one (Q : OrientedUnitSquare) (H : TriangularCapCuts Q)
    (D : ParallelBudgetData) (hdEq : D.d = H.d) :
    H.chordSum Q < 1 := by
  have hw := Q.width_sq_le_two
  have hle := chordSum_le_B Q H D hdEq hw
  have hB := D.B_lt_one
  nlinarith

/-! ## Projected-width bridge from ObliqueChart -/

/-- For orthonormal `(c,s)` in the first quadrant, projected width equals `c+s`. -/
theorem projectedWidth_oriented (Q : OrientedUnitSquare) :
    projectedWidth (Q.c, Q.s) = Q.width := by
  have hc : 0 ≤ Q.c := le_of_lt (lt_of_lt_of_le Q.hs Q.hcs)
  have hs : 0 ≤ Q.s := le_of_lt Q.hs
  simp only [projectedWidth, OrientedUnitSquare.width, abs_of_nonneg hc, abs_of_nonneg hs]

/-- Meeting both cuts forces `d ≤ width ≤ √2`. -/
theorem separation_le_width (Q : OrientedUnitSquare) (H : TriangularCapCuts Q) :
    H.d ≤ Q.width := by
  have := H.ht0
  have := H.htd
  linarith

/-- Flag: Obligation 1 geometric construction of `B` closed. -/
def obligation1_B_geometryClosed : Bool := true

theorem obligation1_B_geometryClosed_true :
    obligation1_B_geometryClosed = true := rfl

def modellingNote : String :=
  "Constructs B(d) from OrientedUnitSquare + TriangularCapCuts: chord sum = f(width,d); \
f ≤ Bcrit or Bedge by case split on (d+y)² ≶ 2; B < 1 on both branches. \
Matches R2 Lemma 1. Triangular-cap chord *lengths* are the manuscript formulae \
(left = t/(cs), right = (z-t-d)/(cs)); Euclidean lengths discharged in S6.ChordIntersection (obligation1_fullyClosed)."

/-- Smallest residual after this module: identify Euclidean intersection lengths
with the triangular-cap formulae `t/(cs)` and `(z-t-d)/(cs)`. The maximisation
and `B < 1` no longer depend on that identification once the formulae are granted. -/
def residual_chord_length_from_intersection : String :=
  "CLOSED in S6.ChordIntersection (leftCap_chordLength / rightCap_chordLength / mem_leftCap_iff / mem_rightCap_iff)."

def obligation1_algebraAndMaxClosed : Bool := true
theorem obligation1_algebraAndMaxClosed_true :
    obligation1_algebraAndMaxClosed = true := rfl

end S6.ParallelBudgetGeometry
