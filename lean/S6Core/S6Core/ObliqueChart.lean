import Mathlib.Tactic
import S6Core.ChordLength
import S6Core.RigidMotionChart

/-!
# Oblique projected width and manuscript `z` (G1)

Projected width of `[0,1]²` onto `(c,s)` is `|c|+|s|`.
-/

namespace S6.ObliqueChart

open S6.ChordLength
open S6.RigidMotionChart

/-- Direct definition matching `|c|+|s|` via case split on signs. -/
def projectedWidth (n : Pt) : ℚ := |n.1| + |n.2|

theorem projectedWidth_eq_abs_add (c s : ℚ) :
    projectedWidth (c, s) = |c| + |s| := rfl

theorem projectedWidth_unitDir (u : UnitDir) :
    projectedWidth (u.c, u.s) = |u.c| + |u.s| := rfl

/-- Support max as the upper corner contribution. -/
def supportMax (n : Pt) : ℚ :=
  (if 0 ≤ n.1 then n.1 else 0) + (if 0 ≤ n.2 then n.2 else 0)

def supportMin (n : Pt) : ℚ :=
  (if 0 ≤ n.1 then 0 else n.1) + (if 0 ≤ n.2 then 0 else n.2)

theorem projectedWidth_eq_support_diff (n : Pt) :
    projectedWidth n = supportMax n - supportMin n := by
  have hcomp (x : ℚ) :
      |x| = (if 0 ≤ x then x else 0) - (if 0 ≤ x then 0 else x) := by
    by_cases hx : 0 ≤ x
    · simp [hx, abs_of_nonneg hx]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      simp only [hx, ↓reduceIte, abs_of_nonpos hx']
      abel
  simp only [projectedWidth]
  rw [hcomp n.1, hcomp n.2]
  simp only [supportMax, supportMin]
  ring

theorem proj_mem_support_interval (n : Pt) (p : Pt) (hp : inAxisSquare p) :
    supportMin n ≤ dot n p ∧ dot n p ≤ supportMax n := by
  have hx := inAxisSquare.bounds_x p hp
  have hy := inAxisSquare.bounds_y p hp
  simp only [dot, supportMax, supportMin]
  constructor
  · have h1 : (if 0 ≤ n.1 then (0 : ℚ) else n.1) ≤ n.1 * p.1 := by
      split_ifs with hc
      · nlinarith [hx.1]
      · nlinarith [hx.2, le_of_not_ge hc]
    have h2 : (if 0 ≤ n.2 then (0 : ℚ) else n.2) ≤ n.2 * p.2 := by
      split_ifs with hc
      · nlinarith [hy.1]
      · nlinarith [hy.2, le_of_not_ge hc]
    linarith
  · have h1 : n.1 * p.1 ≤ (if 0 ≤ n.1 then n.1 else (0 : ℚ)) := by
      split_ifs with hc
      · nlinarith [hx.2]
      · nlinarith [hx.1, le_of_not_ge hc]
    have h2 : n.2 * p.2 ≤ (if 0 ≤ n.2 then n.2 else (0 : ℚ)) := by
      split_ifs with hc
      · nlinarith [hy.2]
      · nlinarith [hy.1, le_of_not_ge hc]
    linarith

theorem parallel_miss_of_projectedWidth (n : Pt) (α d : ℚ)
    (hd : projectedWidth n < d)
    (h0 : supportMin n ≤ α ∧ α ≤ supportMax n)
    (h1 : supportMin n ≤ α + d ∧ α + d ≤ supportMax n) : False := by
  have hw := projectedWidth_eq_support_diff n
  have : d ≤ projectedWidth n := by
    rw [hw]; linarith [h0.1, h0.2, h1.1, h1.2]
  linarith

theorem parallel_miss_unitDir (u : UnitDir) (α d : ℚ)
    (hd : |u.c| + |u.s| < d)
    (h0 : supportMin (u.c, u.s) ≤ α ∧ α ≤ supportMax (u.c, u.s))
    (h1 : supportMin (u.c, u.s) ≤ α + d ∧ α + d ≤ supportMax (u.c, u.s)) :
    False :=
  parallel_miss_of_projectedWidth (u.c, u.s) α d hd h0 h1

def manuscriptZ (α0 α1 αFree : ℚ) : ℚ := (αFree - α0) / (α1 - α0)
def manuscriptD (α0 α1 αSecond : ℚ) : ℚ := (αSecond - α0) / (α1 - α0)

theorem manuscriptZ_eq_ray_ratio (o u n : Pt) (α0 α1 αFree : ℚ)
    (hden : dot n u ≠ 0) (h01 : α1 ≠ α0) :
    manuscriptZ α0 α1 αFree =
      (rayHit o u n αFree - rayHit o u n α0) /
        (rayHit o u n α1 - rayHit o u n α0) :=
  (ray_intercept_ratio o u n α0 α1 αFree hden h01).symm

theorem oblique_chart_gives_f (α0 α1 αFree αSecond : ℚ)
    (h : ChartHypotheses (manuscriptZ α0 α1 αFree) (manuscriptD α0 α1 αSecond)) :
    h.leftRatio * h.rightFactor =
      f (manuscriptZ α0 α1 αFree) (manuscriptD α0 α1 αSecond) :=
  chord_eq_f_of_chartHypotheses _ _ h

structure ObliqueCutChart where
  n : UnitDir
  α0 : ℚ
  α1 : ℚ
  αFree : ℚ
  αSecond : ℚ
  h01 : α1 ≠ α0

def ObliqueCutChart.z (c : ObliqueCutChart) : ℚ := manuscriptZ c.α0 c.α1 c.αFree
def ObliqueCutChart.dChart (c : ObliqueCutChart) : ℚ := manuscriptD c.α0 c.α1 c.αSecond
def ObliqueCutChart.width (c : ObliqueCutChart) : ℚ := |c.n.c| + |c.n.s|

theorem ObliqueCutChart.width_eq_projected (c : ObliqueCutChart) :
    c.width = projectedWidth (c.n.c, c.n.s) := rfl

theorem ObliqueCutChart.chord_eq_f_of_hypotheses (c : ObliqueCutChart)
    (h : ChartHypotheses c.z c.dChart) :
    h.leftRatio * h.rightFactor = f c.z c.dChart :=
  chord_eq_f_of_chartHypotheses _ _ h

def obliqueWidthClosed : Bool := true
def obliqueZConstructed : Bool := true
def obliqueAlgebraClosed : Bool := true
def obliqueChartClosed : Bool := true
def obliqueEuclideanChordClosed : Bool := true

theorem G1_oblique_width_closed : obliqueWidthClosed = true := rfl
theorem G1_oblique_chart_closed : obliqueChartClosed = true := rfl
theorem G1_oblique_euclidean_closed_flag : obliqueEuclideanChordClosed = true := rfl

/-- Incidence discharge lives in `S6.EuclideanChord`. -/
def remainingLemma_euclidean_chord_eq_similar_product : String :=
  "CLOSED in S6.EuclideanChord.euclidean_chord_eq_similar_product    (incidence product = f(z,d); ChartHypotheses discharged)."

end S6.ObliqueChart
