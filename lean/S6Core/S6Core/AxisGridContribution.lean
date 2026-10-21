import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.Obligation2

/-!
# Axis-aligned grid contribution (R2 fragment)

Target grid \(\mathcal G\): four outer sides of `[0,2μ]²` plus midlines
`x=μ` and `y=μ`. Total length `12μ`.

For an **axis-aligned** unit square, each line of \(\mathcal G\) meets the square
in a segment of length at most `1`.
-/

namespace S6.AxisGridContribution

open S6.OwnershipBridge
open S6.Obligation2

def clampIntervalLen (a L : ℚ) : ℚ :=
  let lo := max a 0
  let hi := min (a + 1) L
  max (hi - lo) 0

theorem clampIntervalLen_nonneg (a L : ℚ) : 0 ≤ clampIntervalLen a L := by
  simp only [clampIntervalLen]; exact le_max_right _ _

theorem clampIntervalLen_le_one (a L : ℚ) (_hL : 1 ≤ L) :
    clampIntervalLen a L ≤ 1 := by
  simp only [clampIntervalLen]
  have h1 : min (a + 1) L - max a 0 ≤ 1 := by
    have : min (a + 1) L ≤ a + 1 := min_le_left _ _
    have : a ≤ max a 0 := le_max_left _ _
    nlinarith
  exact max_le_iff.2 ⟨h1, by norm_num⟩

def bottomLen (s : AxisSquare) (μ : ℚ) : ℚ :=
  if s.y ≤ 0 ∧ 0 ≤ s.y + 1 then clampIntervalLen s.x (2 * μ) else 0

def topLen (s : AxisSquare) (μ : ℚ) : ℚ :=
  if s.y ≤ 2 * μ ∧ 2 * μ ≤ s.y + 1 then clampIntervalLen s.x (2 * μ) else 0

def leftLen (s : AxisSquare) (μ : ℚ) : ℚ :=
  if s.x ≤ 0 ∧ 0 ≤ s.x + 1 then clampIntervalLen s.y (2 * μ) else 0

def rightLen (s : AxisSquare) (μ : ℚ) : ℚ :=
  if s.x ≤ 2 * μ ∧ 2 * μ ≤ s.x + 1 then clampIntervalLen s.y (2 * μ) else 0

def hMidLen (s : AxisSquare) (μ : ℚ) : ℚ :=
  if s.y ≤ μ ∧ μ ≤ s.y + 1 then clampIntervalLen s.x (2 * μ) else 0

def vMidLen (s : AxisSquare) (μ : ℚ) : ℚ :=
  if s.x ≤ μ ∧ μ ≤ s.x + 1 then clampIntervalLen s.y (2 * μ) else 0

def axisGridContrib (s : AxisSquare) (μ : ℚ) : ℚ :=
  bottomLen s μ + topLen s μ + leftLen s μ + rightLen s μ +
    hMidLen s μ + vMidLen s μ

theorem bottomLen_le_one (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    bottomLen s μ ≤ 1 := by
  simp only [bottomLen]; split_ifs
  · exact clampIntervalLen_le_one _ _ (by nlinarith [hμ])
  · norm_num

theorem topLen_le_one (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    topLen s μ ≤ 1 := by
  simp only [topLen]; split_ifs
  · exact clampIntervalLen_le_one _ _ (by nlinarith [hμ])
  · norm_num

theorem leftLen_le_one (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    leftLen s μ ≤ 1 := by
  simp only [leftLen]; split_ifs
  · exact clampIntervalLen_le_one _ _ (by nlinarith [hμ])
  · norm_num

theorem rightLen_le_one (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    rightLen s μ ≤ 1 := by
  simp only [rightLen]; split_ifs
  · exact clampIntervalLen_le_one _ _ (by nlinarith [hμ])
  · norm_num

theorem hMidLen_le_one (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    hMidLen s μ ≤ 1 := by
  simp only [hMidLen]; split_ifs
  · exact clampIntervalLen_le_one _ _ (by nlinarith [hμ])
  · norm_num

theorem vMidLen_le_one (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    vMidLen s μ ≤ 1 := by
  simp only [vMidLen]; split_ifs
  · exact clampIntervalLen_le_one _ _ (by nlinarith [hμ])
  · norm_num

def swCorner : AxisSquare := ⟨0, 0⟩

theorem sw_meets_bottom (μ : ℚ) (_hμ : 1 < μ) :
    bottomLen swCorner μ = clampIntervalLen 0 (2 * μ) := by
  unfold bottomLen swCorner
  have h : (0 : ℚ) ≤ 0 ∧ (0 : ℚ) ≤ 0 + 1 := by norm_num
  rw [ite_eq_left h]

theorem clamp_zero_one (μ : ℚ) (hμ : 1 < μ) :
    clampIntervalLen (0 : ℚ) (2 * μ) = 1 := by
  unfold clampIntervalLen
  have hlo : max (0 : ℚ) 0 = 0 := max_self 0
  have hhi : min ((0 : ℚ) + 1) (2 * μ) = 1 := by
    simp only [zero_add]
    exact min_eq_left (by nlinarith [hμ] : (1 : ℚ) ≤ 2 * μ)
  rw [hlo, hhi]
  norm_num

theorem swCorner_bottom (μ : ℚ) (hμ : 1 < μ) : bottomLen swCorner μ = 1 := by
  rw [sw_meets_bottom μ hμ, clamp_zero_one μ hμ]

theorem sw_meets_left (μ : ℚ) (_hμ : 1 < μ) :
    leftLen swCorner μ = clampIntervalLen 0 (2 * μ) := by
  unfold leftLen swCorner
  have h : (0 : ℚ) ≤ 0 ∧ (0 : ℚ) ≤ 0 + 1 := by norm_num
  rw [ite_eq_left h]

theorem swCorner_left (μ : ℚ) (hμ : 1 < μ) : leftLen swCorner μ = 1 := by
  rw [sw_meets_left μ hμ, clamp_zero_one μ hμ]

theorem swCorner_top_zero (μ : ℚ) (hμ : 1 < μ) : topLen swCorner μ = 0 := by
  unfold topLen swCorner
  simp only [zero_add]
  have h : ¬ ((0 : ℚ) ≤ 2 * μ ∧ 2 * μ ≤ 1) := by
    intro ⟨_, h2⟩; nlinarith [hμ]
  rw [ite_eq_right h]

theorem swCorner_right_zero (μ : ℚ) (hμ : 1 < μ) : rightLen swCorner μ = 0 := by
  unfold rightLen swCorner
  simp only [zero_add]
  have h : ¬ ((0 : ℚ) ≤ 2 * μ ∧ 2 * μ ≤ 1) := by
    intro ⟨_, h2⟩; nlinarith [hμ]
  rw [ite_eq_right h]

theorem swCorner_outer_contrib (μ : ℚ) (hμ : 1 < μ) :
    bottomLen swCorner μ + topLen swCorner μ +
      leftLen swCorner μ + rightLen swCorner μ = 2 := by
  rw [swCorner_bottom μ hμ, swCorner_left μ hμ, swCorner_top_zero μ hμ,
    swCorner_right_zero μ hμ]
  norm_num

theorem four_corners_outer_le_eight (c1 c2 c3 c4 : ℚ)
    (h1 : c1 ≤ 2) (h2 : c2 ≤ 2) (h3 : c3 ≤ 2) (h4 : c4 ≤ 2) :
    c1 + c2 + c3 + c4 ≤ 8 := by nlinarith

def gridLen (μ : ℚ) : ℚ := 12 * μ

theorem gridLen_gt_twelve (μ : ℚ) (hμ : 1 < μ) : (12 : ℚ) < gridLen μ := by
  simp only [gridLen]; nlinarith

theorem axis_grid_cover_impossible (μ corners CF : ℚ) (hμ : 1 < μ)
    (hcorners : corners ≤ 8) (hCF : CF < 4)
    (hcover : gridLen μ ≤ corners + CF) : False := by
  have h12 := gridLen_gt_twelve μ hμ
  simp only [gridLen] at hcover h12
  nlinarith

end S6.AxisGridContribution
