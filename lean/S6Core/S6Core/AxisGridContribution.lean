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

/-! ## Corner-owner outer bound (axis) -/

/-- An axis square that contains the target SW corner `(0,0)` cannot meet
the top or right outer sides when `μ > 1`, and meets bottom+left in length ≤1
each ⇒ outer contribution ≤ 2. -/
theorem axis_contains_origin_outer_le_two (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hO : s.contains (0, 0)) :
    bottomLen s μ + topLen s μ + leftLen s μ + rightLen s μ ≤ 2 := by
  -- From contains (0,0): s.x ≤ 0 ≤ s.x+1 and s.y ≤ 0 ≤ s.y+1
  have hx0 : s.x ≤ 0 := by
    simp only [AxisSquare.contains] at hO; exact hO.1.1.1
  have hx1 : (0 : ℚ) ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hO; exact hO.1.1.2
  have hy0 : s.y ≤ 0 := by
    simp only [AxisSquare.contains] at hO; exact hO.1.2
  have hy1 : (0 : ℚ) ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hO; exact hO.2
  -- top: needs 2μ ∈ [s.y, s.y+1]; but s.y+1 ≤ 1 < 2 ≤ 2μ
  have htop : topLen s μ = 0 := by
    simp only [topLen]
    have h : ¬ (s.y ≤ 2 * μ ∧ 2 * μ ≤ s.y + 1) := by
      intro ⟨_, h2⟩
      have : s.y + 1 ≤ 1 := by nlinarith [hy0]
      nlinarith [hμ, h2, this]
    rw [ite_eq_right h]
  -- right: needs 2μ ∈ [s.x, s.x+1]; similarly impossible
  have hright : rightLen s μ = 0 := by
    simp only [rightLen]
    have h : ¬ (s.x ≤ 2 * μ ∧ 2 * μ ≤ s.x + 1) := by
      intro ⟨_, h2⟩
      have : s.x + 1 ≤ 1 := by nlinarith [hx0]
      nlinarith [hμ, h2, this]
    rw [ite_eq_right h]
  have hb := bottomLen_le_one s μ hμ
  have hl := leftLen_le_one s μ hμ
  nlinarith [htop, hright, hb, hl]

def seCornerAt (μ : ℚ) : AxisSquare := ⟨2 * μ - 1, 0⟩
def neCornerAt (μ : ℚ) : AxisSquare := ⟨2 * μ - 1, 2 * μ - 1⟩
def nwCornerAt (μ : ℚ) : AxisSquare := ⟨0, 2 * μ - 1⟩

theorem se_contains_se (μ : ℚ) (_hμ : 1 < μ) :
    (seCornerAt μ).contains (2 * μ, 0) := by
  simp only [AxisSquare.contains, seCornerAt]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> nlinarith

theorem axis_contains_se_outer_le_two (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSE : s.contains (2 * μ, 0)) :
    bottomLen s μ + topLen s μ + leftLen s μ + rightLen s μ ≤ 2 := by
  have hx0 : s.x ≤ 2 * μ := by
    simp only [AxisSquare.contains] at hSE; exact hSE.1.1.1
  have hx1 : 2 * μ ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hSE; exact hSE.1.1.2
  have hy0 : s.y ≤ 0 := by
    simp only [AxisSquare.contains] at hSE; exact hSE.1.2
  have hy1 : (0 : ℚ) ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hSE; exact hSE.2
  have htop : topLen s μ = 0 := by
    simp only [topLen]
    have h : ¬ (s.y ≤ 2 * μ ∧ 2 * μ ≤ s.y + 1) := by
      intro ⟨_, h2⟩
      have : s.y + 1 ≤ 1 := by nlinarith [hy0]
      nlinarith [hμ, h2, this]
    rw [ite_eq_right h]
  have hleft : leftLen s μ = 0 := by
    simp only [leftLen]
    have h : ¬ (s.x ≤ 0 ∧ 0 ≤ s.x + 1) := by
      intro ⟨h1, _⟩
      -- s.x ≤ 0 and 2μ ≤ s.x+1 ≤ 1 ⇒ 2μ ≤ 1, contradict μ>1
      nlinarith [hμ, h1, hx1]
    rw [ite_eq_right h]
  have hb := bottomLen_le_one s μ hμ
  have hr := rightLen_le_one s μ hμ
  nlinarith [htop, hleft, hb, hr]

theorem axis_contains_ne_outer_le_two (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNE : s.contains (2 * μ, 2 * μ)) :
    bottomLen s μ + topLen s μ + leftLen s μ + rightLen s μ ≤ 2 := by
  have hx0 : s.x ≤ 2 * μ := by
    simp only [AxisSquare.contains] at hNE; exact hNE.1.1.1
  have hx1 : 2 * μ ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hNE; exact hNE.1.1.2
  have hy0 : s.y ≤ 2 * μ := by
    simp only [AxisSquare.contains] at hNE; exact hNE.1.2
  have hy1 : 2 * μ ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hNE; exact hNE.2
  have hbot : bottomLen s μ = 0 := by
    simp only [bottomLen]
    have h : ¬ (s.y ≤ 0 ∧ 0 ≤ s.y + 1) := by
      intro ⟨h1, _⟩
      nlinarith [hμ, h1, hy1]
    rw [ite_eq_right h]
  have hleft : leftLen s μ = 0 := by
    simp only [leftLen]
    have h : ¬ (s.x ≤ 0 ∧ 0 ≤ s.x + 1) := by
      intro ⟨h1, _⟩
      nlinarith [hμ, h1, hx1]
    rw [ite_eq_right h]
  have ht := topLen_le_one s μ hμ
  have hr := rightLen_le_one s μ hμ
  nlinarith [hbot, hleft, ht, hr]

theorem axis_contains_nw_outer_le_two (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNW : s.contains (0, 2 * μ)) :
    bottomLen s μ + topLen s μ + leftLen s μ + rightLen s μ ≤ 2 := by
  have hx0 : s.x ≤ 0 := by
    simp only [AxisSquare.contains] at hNW; exact hNW.1.1.1
  have hx1 : (0 : ℚ) ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hNW; exact hNW.1.1.2
  have hy0 : s.y ≤ 2 * μ := by
    simp only [AxisSquare.contains] at hNW; exact hNW.1.2
  have hy1 : 2 * μ ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hNW; exact hNW.2
  have hbot : bottomLen s μ = 0 := by
    simp only [bottomLen]
    have h : ¬ (s.y ≤ 0 ∧ 0 ≤ s.y + 1) := by
      intro ⟨h1, _⟩
      nlinarith [hμ, h1, hy1]
    rw [ite_eq_right h]
  have hright : rightLen s μ = 0 := by
    simp only [rightLen]
    have h : ¬ (s.x ≤ 2 * μ ∧ 2 * μ ≤ s.x + 1) := by
      intro ⟨_, h2⟩
      have : s.x + 1 ≤ 1 := by nlinarith [hx0]
      nlinarith [hμ, h2, this]
    rw [ite_eq_right h]
  have ht := topLen_le_one s μ hμ
  have hl := leftLen_le_one s μ hμ
  nlinarith [hbot, hright, ht, hl]

/-- Four axis tiles owning the four target corners ⇒ outer corner budget ≤ 8. -/
theorem axis_four_corner_owners_outer_le_eight
    (sSW sSE sNE sNW : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : sSW.contains (0, 0)) (hSE : sSE.contains (2 * μ, 0))
    (hNE : sNE.contains (2 * μ, 2 * μ)) (hNW : sNW.contains (0, 2 * μ)) :
    (bottomLen sSW μ + topLen sSW μ + leftLen sSW μ + rightLen sSW μ) +
      (bottomLen sSE μ + topLen sSE μ + leftLen sSE μ + rightLen sSE μ) +
      (bottomLen sNE μ + topLen sNE μ + leftLen sNE μ + rightLen sNE μ) +
      (bottomLen sNW μ + topLen sNW μ + leftLen sNW μ + rightLen sNW μ) ≤ 8 := by
  have h1 := axis_contains_origin_outer_le_two sSW μ hμ hSW
  have h2 := axis_contains_se_outer_le_two sSE μ hμ hSE
  have h3 := axis_contains_ne_outer_le_two sNE μ hμ hNE
  have h4 := axis_contains_nw_outer_le_two sNW μ hμ hNW
  nlinarith


/-! ## Midline / CF axis bounds -/

theorem axis_mid_sum_le_two (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    hMidLen s μ + vMidLen s μ ≤ 2 := by
  nlinarith [hMidLen_le_one s μ hμ, vMidLen_le_one s μ hμ]

/-- Two filler tiles: each mid-sum ≤2 ⇒ combined mid CF ≤4 (non-strict).
Strict `CF < 4` needs an extra geometric gap (still open for full export). -/
theorem axis_two_filler_mid_le_four (s1 s2 : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    (hMidLen s1 μ + vMidLen s1 μ) + (hMidLen s2 μ + vMidLen s2 μ) ≤ 4 := by
  nlinarith [axis_mid_sum_le_two s1 μ hμ, axis_mid_sum_le_two s2 μ hμ]

/-- Full axis grid contrib of one square ≤6 (4 outer + 2 mid, each ≤1). -/
theorem axisGridContrib_le_six (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    axisGridContrib s μ ≤ 6 := by
  simp only [axisGridContrib]
  nlinarith [bottomLen_le_one s μ hμ, topLen_le_one s μ hμ,
    leftLen_le_one s μ hμ, rightLen_le_one s μ hμ,
    hMidLen_le_one s μ hμ, vMidLen_le_one s μ hμ]

end S6.AxisGridContribution
