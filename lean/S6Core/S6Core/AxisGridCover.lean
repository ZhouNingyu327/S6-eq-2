import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import S6Core.AxisGridContribution
import S6Core.IntervalCover1D
import S6Core.OwnershipBridge

/-!
# Axis grid covering inequality

If six axis-aligned unit squares cover each of the six target grid lines
as real segments, then

  `12 μ ≤ ∑ᵢ axisGridContrib (squares i) μ`.
-/

namespace S6.AxisGridCover

open MeasureTheory Set Real
open S6.AxisGridContribution
open S6.IntervalCover1D
open S6.OwnershipBridge

theorem ofReal_max_zero (a : ℝ) : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
  by_cases h : 0 ≤ a
  · rw [max_eq_left h]
  · have ha : a ≤ 0 := le_of_not_ge h
    rw [max_eq_right ha, ENNReal.ofReal_of_nonpos ha, ENNReal.ofReal_zero]

/-! ## Bottom edge -/

def bottomLo (s : AxisSquare) (_μ : ℚ) : ℝ := max (s.x : ℝ) 0
def bottomHi (s : AxisSquare) (μ : ℚ) : ℝ :=
  min ((s.x : ℝ) + 1) ((2 : ℝ) * (μ : ℝ))

def bottomInterval (s : AxisSquare) (μ : ℚ) : Set ℝ :=
  if s.y ≤ 0 ∧ 0 ≤ s.y + 1 then Icc (bottomLo s μ) (bottomHi s μ) else (∅ : Set ℝ)

theorem volume_bottomInterval (s : AxisSquare) (μ : ℚ) :
    volume (bottomInterval s μ) = ENNReal.ofReal (bottomLen s μ) := by
  unfold bottomInterval bottomLen bottomLo bottomHi clampIntervalLen
  by_cases h : s.y ≤ 0 ∧ 0 ≤ s.y + 1
  · rw [ite_eq_left h, ite_eq_left h, volume_Icc]
    simp only [Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_zero,
      Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    change ENNReal.ofReal (min ((s.x : ℝ) + 1) (2 * μ) - max (s.x : ℝ) 0) =
      ENNReal.ofReal (max (min ((s.x : ℝ) + 1) (2 * μ) - max (s.x : ℝ) 0) 0)
    rw [ofReal_max_zero]
  · rw [ite_eq_right h, ite_eq_right h, measure_empty, Rat.cast_zero, ENNReal.ofReal_zero]

theorem bottomLen_nonneg (s : AxisSquare) (μ : ℚ) : 0 ≤ bottomLen s μ := by
  simp only [bottomLen]; split_ifs
  · simp only [clampIntervalLen]; exact le_max_right _ _
  · norm_num

/-- Cover of `Icc a b` by sets of known volume ⇒ length bound. -/
theorem line_cover_sum {ι : Type*} [Fintype ι] (a b : ℝ) (_hab : a ≤ b)
    (S : ι → Set ℝ) (c : ι → ℝ)
    (hcover : Icc a b ⊆ ⋃ i, S i)
    (hvol : ∀ i, volume (S i) = ENNReal.ofReal (c i))
    (hnn : ∀ i, 0 ≤ c i) :
    b - a ≤ ∑ i, c i := by
  have hmono : volume (Icc a b) ≤ volume (⋃ i, S i) := measure_mono hcover
  have hsub : volume (⋃ i, S i) ≤ ∑ i, volume (S i) :=
    measure_iUnion_fintype_le volume S
  have hchain := hmono.trans hsub
  rw [volume_Icc] at hchain
  simp_rw [hvol] at hchain
  have hsum : (∑ i, ENNReal.ofReal (c i)) = ENNReal.ofReal (∑ i, c i) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    exact fun i _ => hnn i
  rw [hsum] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => hnn i)).mp hchain

theorem bottom_cover_sum_lens (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (hcover : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i : Fin 6, bottomInterval (squares i) μ) :
    (2 * μ : ℝ) ≤ ∑ i : Fin 6, (bottomLen (squares i) μ : ℝ) := by
  have hab : (0 : ℝ) ≤ (2 : ℝ) * μ := by exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have h := line_cover_sum (0 : ℝ) ((2 : ℝ) * μ) hab
    (fun i => bottomInterval (squares i) μ)
    (fun i => (bottomLen (squares i) μ : ℝ))
    hcover
    (fun i => volume_bottomInterval (squares i) μ)
    (fun i => by exact_mod_cast bottomLen_nonneg (squares i) μ)
  simpa using h

/-! ## Top / left / right / mid intervals (same pattern) -/

def topInterval (s : AxisSquare) (μ : ℚ) : Set ℝ :=
  if s.y ≤ 2 * μ ∧ 2 * μ ≤ s.y + 1 then
    Icc (max (s.x : ℝ) 0) (min ((s.x : ℝ) + 1) ((2 : ℝ) * μ))
  else (∅ : Set ℝ)

def leftInterval (s : AxisSquare) (μ : ℚ) : Set ℝ :=
  if s.x ≤ 0 ∧ 0 ≤ s.x + 1 then
    Icc (max (s.y : ℝ) 0) (min ((s.y : ℝ) + 1) ((2 : ℝ) * μ))
  else (∅ : Set ℝ)

def rightInterval (s : AxisSquare) (μ : ℚ) : Set ℝ :=
  if s.x ≤ 2 * μ ∧ 2 * μ ≤ s.x + 1 then
    Icc (max (s.y : ℝ) 0) (min ((s.y : ℝ) + 1) ((2 : ℝ) * μ))
  else (∅ : Set ℝ)

def hMidInterval (s : AxisSquare) (μ : ℚ) : Set ℝ :=
  if s.y ≤ μ ∧ μ ≤ s.y + 1 then
    Icc (max (s.x : ℝ) 0) (min ((s.x : ℝ) + 1) ((2 : ℝ) * μ))
  else (∅ : Set ℝ)

def vMidInterval (s : AxisSquare) (μ : ℚ) : Set ℝ :=
  if s.x ≤ μ ∧ μ ≤ s.x + 1 then
    Icc (max (s.y : ℝ) 0) (min ((s.y : ℝ) + 1) ((2 : ℝ) * μ))
  else (∅ : Set ℝ)

theorem volume_topInterval (s : AxisSquare) (μ : ℚ) :
    volume (topInterval s μ) = ENNReal.ofReal (topLen s μ) := by
  unfold topInterval topLen clampIntervalLen
  by_cases h : s.y ≤ 2 * μ ∧ 2 * μ ≤ s.y + 1
  · rw [ite_eq_left h, ite_eq_left h, volume_Icc]
    simp only [Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_zero,
      Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    change ENNReal.ofReal _ = ENNReal.ofReal (max _ 0)
    rw [ofReal_max_zero]
  · rw [ite_eq_right h, ite_eq_right h, measure_empty, Rat.cast_zero, ENNReal.ofReal_zero]

theorem volume_leftInterval (s : AxisSquare) (μ : ℚ) :
    volume (leftInterval s μ) = ENNReal.ofReal (leftLen s μ) := by
  unfold leftInterval leftLen clampIntervalLen
  by_cases h : s.x ≤ 0 ∧ 0 ≤ s.x + 1
  · rw [ite_eq_left h, ite_eq_left h, volume_Icc]
    simp only [Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_zero,
      Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    change ENNReal.ofReal _ = ENNReal.ofReal (max _ 0)
    rw [ofReal_max_zero]
  · rw [ite_eq_right h, ite_eq_right h, measure_empty, Rat.cast_zero, ENNReal.ofReal_zero]

theorem volume_rightInterval (s : AxisSquare) (μ : ℚ) :
    volume (rightInterval s μ) = ENNReal.ofReal (rightLen s μ) := by
  unfold rightInterval rightLen clampIntervalLen
  by_cases h : s.x ≤ 2 * μ ∧ 2 * μ ≤ s.x + 1
  · rw [ite_eq_left h, ite_eq_left h, volume_Icc]
    simp only [Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_zero,
      Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    change ENNReal.ofReal _ = ENNReal.ofReal (max _ 0)
    rw [ofReal_max_zero]
  · rw [ite_eq_right h, ite_eq_right h, measure_empty, Rat.cast_zero, ENNReal.ofReal_zero]

theorem volume_hMidInterval (s : AxisSquare) (μ : ℚ) :
    volume (hMidInterval s μ) = ENNReal.ofReal (hMidLen s μ) := by
  unfold hMidInterval hMidLen clampIntervalLen
  by_cases h : s.y ≤ μ ∧ μ ≤ s.y + 1
  · rw [ite_eq_left h, ite_eq_left h, volume_Icc]
    simp only [Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_zero,
      Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    change ENNReal.ofReal _ = ENNReal.ofReal (max _ 0)
    rw [ofReal_max_zero]
  · rw [ite_eq_right h, ite_eq_right h, measure_empty, Rat.cast_zero, ENNReal.ofReal_zero]

theorem volume_vMidInterval (s : AxisSquare) (μ : ℚ) :
    volume (vMidInterval s μ) = ENNReal.ofReal (vMidLen s μ) := by
  unfold vMidInterval vMidLen clampIntervalLen
  by_cases h : s.x ≤ μ ∧ μ ≤ s.x + 1
  · rw [ite_eq_left h, ite_eq_left h, volume_Icc]
    simp only [Rat.cast_max, Rat.cast_min, Rat.cast_sub, Rat.cast_add, Rat.cast_zero,
      Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
    change ENNReal.ofReal _ = ENNReal.ofReal (max _ 0)
    rw [ofReal_max_zero]
  · rw [ite_eq_right h, ite_eq_right h, measure_empty, Rat.cast_zero, ENNReal.ofReal_zero]

theorem len_nonneg_top (s : AxisSquare) (μ : ℚ) : 0 ≤ topLen s μ := by
  simp only [topLen]; split_ifs <;> simp [clampIntervalLen]
theorem len_nonneg_left (s : AxisSquare) (μ : ℚ) : 0 ≤ leftLen s μ := by
  simp only [leftLen]; split_ifs <;> simp [clampIntervalLen]
theorem len_nonneg_right (s : AxisSquare) (μ : ℚ) : 0 ≤ rightLen s μ := by
  simp only [rightLen]; split_ifs <;> simp [clampIntervalLen]
theorem len_nonneg_hMid (s : AxisSquare) (μ : ℚ) : 0 ≤ hMidLen s μ := by
  simp only [hMidLen]; split_ifs <;> simp [clampIntervalLen]
theorem len_nonneg_vMid (s : AxisSquare) (μ : ℚ) : 0 ≤ vMidLen s μ := by
  simp only [vMidLen]; split_ifs <;> simp [clampIntervalLen]

/-! ## Full six-line cover package -/

/-- Real-segment cover of all six grid lines. -/
structure AxisGridLineCover (μ : ℚ) (squares : Fin 6 → AxisSquare) : Prop where
  bottom : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, bottomInterval (squares i) μ
  top : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, topInterval (squares i) μ
  left : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, leftInterval (squares i) μ
  right : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, rightInterval (squares i) μ
  hMid : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, hMidInterval (squares i) μ
  vMid : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, vMidInterval (squares i) μ

theorem AxisGridLineCover.bottom_sum {μ squares} (hμ : 1 < μ)
    (H : AxisGridLineCover μ squares) :
    (2 * μ : ℝ) ≤ ∑ i, (bottomLen (squares i) μ : ℝ) :=
  bottom_cover_sum_lens μ hμ squares H.bottom

theorem AxisGridLineCover.top_sum {μ squares} (hμ : 1 < μ)
    (H : AxisGridLineCover μ squares) :
    (2 * μ : ℝ) ≤ ∑ i, (topLen (squares i) μ : ℝ) := by
  have hab : (0 : ℝ) ≤ (2 : ℝ) * μ := by exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  simpa using line_cover_sum (0 : ℝ) ((2 : ℝ) * μ) hab
    (fun i => topInterval (squares i) μ) (fun i => (topLen (squares i) μ : ℝ))
    H.top (fun i => volume_topInterval _ _) (fun i => by exact_mod_cast len_nonneg_top _ _)

theorem AxisGridLineCover.left_sum {μ squares} (hμ : 1 < μ)
    (H : AxisGridLineCover μ squares) :
    (2 * μ : ℝ) ≤ ∑ i, (leftLen (squares i) μ : ℝ) := by
  have hab : (0 : ℝ) ≤ (2 : ℝ) * μ := by exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  simpa using line_cover_sum (0 : ℝ) ((2 : ℝ) * μ) hab
    (fun i => leftInterval (squares i) μ) (fun i => (leftLen (squares i) μ : ℝ))
    H.left (fun i => volume_leftInterval _ _) (fun i => by exact_mod_cast len_nonneg_left _ _)

theorem AxisGridLineCover.right_sum {μ squares} (hμ : 1 < μ)
    (H : AxisGridLineCover μ squares) :
    (2 * μ : ℝ) ≤ ∑ i, (rightLen (squares i) μ : ℝ) := by
  have hab : (0 : ℝ) ≤ (2 : ℝ) * μ := by exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  simpa using line_cover_sum (0 : ℝ) ((2 : ℝ) * μ) hab
    (fun i => rightInterval (squares i) μ) (fun i => (rightLen (squares i) μ : ℝ))
    H.right (fun i => volume_rightInterval _ _) (fun i => by exact_mod_cast len_nonneg_right _ _)

theorem AxisGridLineCover.hMid_sum {μ squares} (hμ : 1 < μ)
    (H : AxisGridLineCover μ squares) :
    (2 * μ : ℝ) ≤ ∑ i, (hMidLen (squares i) μ : ℝ) := by
  have hab : (0 : ℝ) ≤ (2 : ℝ) * μ := by exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  simpa using line_cover_sum (0 : ℝ) ((2 : ℝ) * μ) hab
    (fun i => hMidInterval (squares i) μ) (fun i => (hMidLen (squares i) μ : ℝ))
    H.hMid (fun i => volume_hMidInterval _ _) (fun i => by exact_mod_cast len_nonneg_hMid _ _)

theorem AxisGridLineCover.vMid_sum {μ squares} (hμ : 1 < μ)
    (H : AxisGridLineCover μ squares) :
    (2 * μ : ℝ) ≤ ∑ i, (vMidLen (squares i) μ : ℝ) := by
  have hab : (0 : ℝ) ≤ (2 : ℝ) * μ := by exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  simpa using line_cover_sum (0 : ℝ) ((2 : ℝ) * μ) hab
    (fun i => vMidInterval (squares i) μ) (fun i => (vMidLen (squares i) μ : ℝ))
    H.vMid (fun i => volume_vMidInterval _ _) (fun i => by exact_mod_cast len_nonneg_vMid _ _)

/-- Main theorem: six-line real cover ⇒ `∑ axisGridContrib ≥ 12μ`. -/
theorem axis_grid_cover_sum (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridLineCover μ squares) :
    (12 * μ : ℝ) ≤ ∑ i : Fin 6, (axisGridContrib (squares i) μ : ℝ) := by
  have hb := H.bottom_sum hμ
  have ht := H.top_sum hμ
  have hl := H.left_sum hμ
  have hr := H.right_sum hμ
  have hh := H.hMid_sum hμ
  have hv := H.vMid_sum hμ
  have hdecomp :
      (∑ i : Fin 6, (axisGridContrib (squares i) μ : ℝ)) =
        (∑ i, (bottomLen (squares i) μ : ℝ)) +
          (∑ i, (topLen (squares i) μ : ℝ)) +
          (∑ i, (leftLen (squares i) μ : ℝ)) +
          (∑ i, (rightLen (squares i) μ : ℝ)) +
          (∑ i, (hMidLen (squares i) μ : ℝ)) +
          (∑ i, (vMidLen (squares i) μ : ℝ)) := by
    simp only [axisGridContrib, Rat.cast_add]
    repeat rw [Finset.sum_add_distrib]
  rw [hdecomp]
  nlinarith [hb, ht, hl, hr, hh, hv]

theorem axis_grid_cover_sum_rat (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridLineCover μ squares) :
    (12 : ℚ) * μ ≤ ∑ i : Fin 6, axisGridContrib (squares i) μ := by
  exact_mod_cast axis_grid_cover_sum μ hμ squares H

/-- Line cover + corners≤8 + CF≤4 split of total contrib ⇒ False. -/
theorem axis_line_cover_impossible_of_corner_cf
    (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridLineCover μ squares)
    (corners CF : ℚ) (hcorners : corners ≤ 8) (hCF : CF ≤ 4)
    (hsplit : ∑ i : Fin 6, axisGridContrib (squares i) μ ≤ corners + CF) :
    False := by
  have hge := axis_grid_cover_sum_rat μ hμ squares H
  have hcover : (12 : ℚ) * μ ≤ corners + CF := le_trans hge hsplit
  exact axis_grid_cover_impossible_le μ corners CF hμ hcorners hCF (by
    simpa [gridLen] using hcover)

def axisGridCoverIneqClosed : Bool := true
theorem axisGridCoverIneqClosed_true : axisGridCoverIneqClosed = true := rfl

end S6.AxisGridCover
