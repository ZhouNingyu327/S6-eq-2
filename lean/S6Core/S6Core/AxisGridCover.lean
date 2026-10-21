import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Instances.Rat
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


/-! ## ℚ point on bottom → real interval membership -/

theorem contains_bottom_mem_interval (s : AxisSquare) (μ : ℚ) (q : ℚ)
    (hq0 : 0 ≤ q) (hqL : q ≤ 2 * μ) (hc : s.contains (q, 0)) :
    (q : ℝ) ∈ bottomInterval s μ := by
  have hmeets : s.y ≤ 0 ∧ 0 ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.2, hc.2⟩
  have hx : s.x ≤ q ∧ q ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.1.1, hc.1.1.2⟩
  simp only [bottomInterval, hmeets, ↓reduceIte, bottomLo, bottomHi, mem_Icc]
  constructor
  · exact max_le (by exact_mod_cast hx.1) (by exact_mod_cast hq0)
  · exact le_min (by exact_mod_cast hx.2) (by exact_mod_cast hqL)

theorem contains_top_mem_interval (s : AxisSquare) (μ : ℚ) (q : ℚ)
    (hq0 : 0 ≤ q) (hqL : q ≤ 2 * μ) (hc : s.contains (q, 2 * μ)) :
    (q : ℝ) ∈ topInterval s μ := by
  have hmeets : s.y ≤ 2 * μ ∧ 2 * μ ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.2, hc.2⟩
  have hx : s.x ≤ q ∧ q ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.1.1, hc.1.1.2⟩
  simp only [topInterval, hmeets, ↓reduceIte, mem_Icc]
  constructor
  · exact max_le (by exact_mod_cast hx.1) (by exact_mod_cast hq0)
  · exact le_min (by exact_mod_cast hx.2) (by exact_mod_cast hqL)

/-- Finite union of bottom intervals is closed. -/
theorem bottomUnion_isClosed (μ : ℚ) (squares : Fin 6 → AxisSquare) :
    IsClosed (⋃ i, bottomInterval (squares i) μ) :=
  isClosed_iUnion_of_finite fun i => by
    simp only [bottomInterval]; split_ifs
    · exact isClosed_Icc
    · exact isClosed_empty

/-- All rationals on the bottom edge lie in the real union, given a ℚ cover. -/
theorem bottom_rats_subset_union (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, 0)) :
    ((↑) : ℚ → ℝ) '' {q : ℚ | 0 ≤ q ∧ q ≤ 2 * μ} ⊆
      ⋃ i, bottomInterval (squares i) μ := by
  intro x hx
  rcases hx with ⟨q, ⟨hq0, hqL⟩, rfl⟩
  rcases hQ q hq0 hqL with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, contains_bottom_mem_interval (squares i) μ q hq0 hqL hi⟩

/-! ## Closed + rationals ⇒ full Icc -/

def clampToIcc (q L : ℝ) : ℝ := max (0 : ℝ) (min q L)

theorem abs_sub_clampToIcc_le (x q L : ℝ) (hx0 : 0 ≤ x) (hxL : x ≤ L) (hL : 0 ≤ L) :
    |x - clampToIcc q L| ≤ |x - q| := by
  dsimp [clampToIcc]
  by_cases h1 : q < 0
  · have : min q L < 0 := lt_of_le_of_lt (min_le_left _ _) h1
    have hcl : max (0 : ℝ) (min q L) = 0 := max_eq_left (le_of_lt this)
    rw [hcl]
    have hx0' : |x - 0| = x := by simp [abs_of_nonneg hx0]
    have hxq : |x - q| = x - q :=
      abs_of_nonneg (sub_nonneg.mpr (by nlinarith [hx0, h1] : q ≤ x))
    rw [hx0', hxq]
    nlinarith
  · by_cases h2 : L < q
    · have hcl : max (0 : ℝ) (min q L) = L := by
        have hmin : min q L = L := min_eq_right (le_of_lt h2)
        rw [hmin, max_eq_right hL]
      rw [hcl]
      have hxL' : |x - L| = L - x := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxL)]
      have hxq : |x - q| = q - x := by
        have : x ≤ q := by nlinarith [hxL, h2]
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr this)]
      rw [hxL', hxq]
      nlinarith
    · have h1' : 0 ≤ q := le_of_not_gt h1
      have h2' : q ≤ L := le_of_not_gt h2
      have hmin : min q L = q := min_eq_left h2'
      have hcl : max (0 : ℝ) (min q L) = q := by rw [hmin, max_eq_right h1']
      rw [hcl]

theorem mem_closure_rats_Icc (x : ℝ) (L : ℚ) (hx0 : 0 ≤ x) (hxL : x ≤ (L : ℝ))
    (hL : 0 ≤ L) :
    x ∈ closure (((↑) : ℚ → ℝ) '' Icc (0 : ℚ) L) := by
  refine Metric.mem_closure_iff.mpr ?_
  intro ε hε
  obtain ⟨q, hq⟩ := exists_rat_near x hε
  set q' : ℚ := max (0 : ℚ) (min q L)
  have hq'I : q' ∈ Icc (0 : ℚ) L := by
    refine ⟨le_max_left _ _, max_le hL (min_le_right _ _)⟩
  have hcast : (q' : ℝ) = clampToIcc (q : ℝ) (L : ℝ) := by
    simp only [q', clampToIcc, Rat.cast_max, Rat.cast_min, Rat.cast_zero]
  have hdist : dist x (q' : ℝ) < ε := by
    rw [Real.dist_eq, hcast]
    exact lt_of_le_of_lt (abs_sub_clampToIcc_le x (q : ℝ) (L : ℝ) hx0 hxL
      (by exact_mod_cast hL)) hq
  refine ⟨(q' : ℝ), ?_, hdist⟩
  exact ⟨q', hq'I, rfl⟩

/-- Closed set containing every rational in `[0,L]` contains the real interval. -/
theorem Icc_subset_of_closed_of_rats (F : Set ℝ) (hF : IsClosed F) (L : ℚ)
    (hL : 0 ≤ L)
    (h : ∀ q : ℚ, 0 ≤ q → q ≤ L → (q : ℝ) ∈ F) :
    Icc (0 : ℝ) (L : ℝ) ⊆ F := by
  have hsub : ((↑) : ℚ → ℝ) '' Icc (0 : ℚ) L ⊆ F := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    exact h q hq.1 hq.2
  have hcl : closure (((↑) : ℚ → ℝ) '' Icc (0 : ℚ) L) ⊆ F :=
    (IsClosed.closure_subset_iff hF).mpr hsub
  intro x hx
  exact hcl (mem_closure_rats_Icc x L hx.1 hx.2 hL)

/-- ℚ pointwise cover of the bottom edge ⇒ real `Icc` cover. -/
theorem bottom_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, 0)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, bottomInterval (squares i) μ := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by
    simp
  rw [hEq]
  refine Icc_subset_of_closed_of_rats _ (bottomUnion_isClosed μ squares) (2 * μ) hL ?_
  intro q hq0 hqL
  rcases hQ q hq0 hqL with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, contains_bottom_mem_interval (squares i) μ q hq0 hqL hi⟩


/-! ## Remaining five lines: membership, closed union, ℚ→ℝ lift -/

theorem contains_left_mem_interval (s : AxisSquare) (μ : ℚ) (q : ℚ)
    (hq0 : 0 ≤ q) (hqL : q ≤ 2 * μ) (hc : s.contains (0, q)) :
    (q : ℝ) ∈ leftInterval s μ := by
  have hmeets : s.x ≤ 0 ∧ 0 ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.1.1, hc.1.1.2⟩
  have hy : s.y ≤ q ∧ q ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.2, hc.2⟩
  simp only [leftInterval, hmeets, ↓reduceIte, mem_Icc]
  constructor
  · exact max_le (by exact_mod_cast hy.1) (by exact_mod_cast hq0)
  · exact le_min (by exact_mod_cast hy.2) (by exact_mod_cast hqL)

theorem contains_right_mem_interval (s : AxisSquare) (μ : ℚ) (q : ℚ)
    (hq0 : 0 ≤ q) (hqL : q ≤ 2 * μ) (hc : s.contains (2 * μ, q)) :
    (q : ℝ) ∈ rightInterval s μ := by
  have hmeets : s.x ≤ 2 * μ ∧ 2 * μ ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.1.1, hc.1.1.2⟩
  have hy : s.y ≤ q ∧ q ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.2, hc.2⟩
  simp only [rightInterval, hmeets, ↓reduceIte, mem_Icc]
  constructor
  · exact max_le (by exact_mod_cast hy.1) (by exact_mod_cast hq0)
  · exact le_min (by exact_mod_cast hy.2) (by exact_mod_cast hqL)

theorem contains_hMid_mem_interval (s : AxisSquare) (μ : ℚ) (q : ℚ)
    (hq0 : 0 ≤ q) (hqL : q ≤ 2 * μ) (hc : s.contains (q, μ)) :
    (q : ℝ) ∈ hMidInterval s μ := by
  have hmeets : s.y ≤ μ ∧ μ ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.2, hc.2⟩
  have hx : s.x ≤ q ∧ q ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.1.1, hc.1.1.2⟩
  simp only [hMidInterval, hmeets, ↓reduceIte, mem_Icc]
  constructor
  · exact max_le (by exact_mod_cast hx.1) (by exact_mod_cast hq0)
  · exact le_min (by exact_mod_cast hx.2) (by exact_mod_cast hqL)

theorem contains_vMid_mem_interval (s : AxisSquare) (μ : ℚ) (q : ℚ)
    (hq0 : 0 ≤ q) (hqL : q ≤ 2 * μ) (hc : s.contains (μ, q)) :
    (q : ℝ) ∈ vMidInterval s μ := by
  have hmeets : s.x ≤ μ ∧ μ ≤ s.x + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.1.1, hc.1.1.2⟩
  have hy : s.y ≤ q ∧ q ≤ s.y + 1 := by
    simp only [AxisSquare.contains] at hc
    exact ⟨hc.1.2, hc.2⟩
  simp only [vMidInterval, hmeets, ↓reduceIte, mem_Icc]
  constructor
  · exact max_le (by exact_mod_cast hy.1) (by exact_mod_cast hq0)
  · exact le_min (by exact_mod_cast hy.2) (by exact_mod_cast hqL)

theorem lineUnion_isClosed (μ : ℚ) (S : Fin 6 → Set ℝ)
    (h : ∀ i, IsClosed (S i)) :
    IsClosed (⋃ i, S i) :=
  isClosed_iUnion_of_finite h

theorem topUnion_isClosed (μ : ℚ) (squares : Fin 6 → AxisSquare) :
    IsClosed (⋃ i, topInterval (squares i) μ) :=
  isClosed_iUnion_of_finite fun i => by
    simp only [topInterval]; split_ifs <;> simp [isClosed_Icc, isClosed_empty]

theorem leftUnion_isClosed (μ : ℚ) (squares : Fin 6 → AxisSquare) :
    IsClosed (⋃ i, leftInterval (squares i) μ) :=
  isClosed_iUnion_of_finite fun i => by
    simp only [leftInterval]; split_ifs <;> simp [isClosed_Icc, isClosed_empty]

theorem rightUnion_isClosed (μ : ℚ) (squares : Fin 6 → AxisSquare) :
    IsClosed (⋃ i, rightInterval (squares i) μ) :=
  isClosed_iUnion_of_finite fun i => by
    simp only [rightInterval]; split_ifs <;> simp [isClosed_Icc, isClosed_empty]

theorem hMidUnion_isClosed (μ : ℚ) (squares : Fin 6 → AxisSquare) :
    IsClosed (⋃ i, hMidInterval (squares i) μ) :=
  isClosed_iUnion_of_finite fun i => by
    simp only [hMidInterval]; split_ifs <;> simp [isClosed_Icc, isClosed_empty]

theorem vMidUnion_isClosed (μ : ℚ) (squares : Fin 6 → AxisSquare) :
    IsClosed (⋃ i, vMidInterval (squares i) μ) :=
  isClosed_iUnion_of_finite fun i => by
    simp only [vMidInterval]; split_ifs <;> simp [isClosed_Icc, isClosed_empty]

theorem top_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, 2 * μ)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, topInterval (squares i) μ := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  refine Icc_subset_of_closed_of_rats _ (topUnion_isClosed μ squares) (2 * μ) hL ?_
  intro q hq0 hqL
  rcases hQ q hq0 hqL with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, contains_top_mem_interval (squares i) μ q hq0 hqL hi⟩

theorem left_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (0, q)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, leftInterval (squares i) μ := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  refine Icc_subset_of_closed_of_rats _ (leftUnion_isClosed μ squares) (2 * μ) hL ?_
  intro q hq0 hqL
  rcases hQ q hq0 hqL with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, contains_left_mem_interval (squares i) μ q hq0 hqL hi⟩

theorem right_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (2 * μ, q)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, rightInterval (squares i) μ := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  refine Icc_subset_of_closed_of_rats _ (rightUnion_isClosed μ squares) (2 * μ) hL ?_
  intro q hq0 hqL
  rcases hQ q hq0 hqL with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, contains_right_mem_interval (squares i) μ q hq0 hqL hi⟩

theorem hMid_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, μ)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, hMidInterval (squares i) μ := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  refine Icc_subset_of_closed_of_rats _ (hMidUnion_isClosed μ squares) (2 * μ) hL ?_
  intro q hq0 hqL
  rcases hQ q hq0 hqL with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, contains_hMid_mem_interval (squares i) μ q hq0 hqL hi⟩

theorem vMid_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (μ, q)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, vMidInterval (squares i) μ := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  refine Icc_subset_of_closed_of_rats _ (vMidUnion_isClosed μ squares) (2 * μ) hL ?_
  intro q hq0 hqL
  rcases hQ q hq0 hqL with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, contains_vMid_mem_interval (squares i) μ q hq0 hqL hi⟩

/-- ℚ pointwise cover of all six grid lines ⇒ `AxisGridLineCover`. -/
structure AxisGridRatCover (μ : ℚ) (squares : Fin 6 → AxisSquare) : Prop where
  bottom : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, 0)
  top : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, 2 * μ)
  left : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (0, q)
  right : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (2 * μ, q)
  hMid : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, μ)
  vMid : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (μ, q)

theorem AxisGridLineCover_of_ratCover (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare) (H : AxisGridRatCover μ squares) :
    AxisGridLineCover μ squares where
  bottom := bottom_rat_cover_implies_real μ hμ squares H.bottom
  top := top_rat_cover_implies_real μ hμ squares H.top
  left := left_rat_cover_implies_real μ hμ squares H.left
  right := right_rat_cover_implies_real μ hμ squares H.right
  hMid := hMid_rat_cover_implies_real μ hμ squares H.hMid
  vMid := vMid_rat_cover_implies_real μ hμ squares H.vMid

/-- Six-line ℚ cover ⇒ ∑ axisGridContrib ≥ 12μ. -/
theorem axis_rat_cover_sum (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares) :
    (12 : ℚ) * μ ≤ ∑ i : Fin 6, axisGridContrib (squares i) μ :=
  axis_grid_cover_sum_rat μ hμ squares (AxisGridLineCover_of_ratCover μ hμ squares H)

def axisRatCoverLiftClosed : Bool := true
theorem axisRatCoverLiftClosed_true : axisRatCoverLiftClosed = true := rfl


/-! ## Corner-owner + two-filler discharge under ℚ grid cover -/

def outerContrib (s : AxisSquare) (μ : ℚ) : ℚ :=
  bottomLen s μ + topLen s μ + leftLen s μ + rightLen s μ

def midContrib (s : AxisSquare) (μ : ℚ) : ℚ :=
  hMidLen s μ + vMidLen s μ

theorem axisGridContrib_eq_outer_mid (s : AxisSquare) (μ : ℚ) :
    axisGridContrib s μ = outerContrib s μ + midContrib s μ := by
  simp only [axisGridContrib, outerContrib, midContrib]; ring

/-- ℚ six-line cover + four corner-owners + packing
`∑ contrib ≤ outer₄ + mid₂` ⇒ False (axis G5k0 model discharge). -/
theorem axis_rat_cover_impossible_of_owners_fillers
    (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares)
    (iSW iSE iNE iNW j1 j2 : Fin 6)
    (hSW : (squares iSW).contains (0, 0))
    (hSE : (squares iSE).contains (2 * μ, 0))
    (hNE : (squares iNE).contains (2 * μ, 2 * μ))
    (hNW : (squares iNW).contains (0, 2 * μ))
    (hsplit :
      ∑ k : Fin 6, axisGridContrib (squares k) μ ≤
        outerContrib (squares iSW) μ + outerContrib (squares iSE) μ +
          outerContrib (squares iNE) μ + outerContrib (squares iNW) μ +
          midContrib (squares j1) μ + midContrib (squares j2) μ) :
    False := by
  have hge := axis_rat_cover_sum μ hμ squares H
  set corners :=
    outerContrib (squares iSW) μ + outerContrib (squares iSE) μ +
      outerContrib (squares iNE) μ + outerContrib (squares iNW) μ
  set CF := midContrib (squares j1) μ + midContrib (squares j2) μ
  have hcorners : corners ≤ 8 := by
    dsimp [corners, outerContrib]
    exact axis_four_corner_owners_outer_le_eight
      (squares iSW) (squares iSE) (squares iNE) (squares iNW) μ hμ hSW hSE hNE hNW
  have hCF : CF ≤ 4 := by
    dsimp [CF, midContrib]
    exact axis_two_filler_mid_le_four (squares j1) (squares j2) μ hμ
  have hle : ∑ k : Fin 6, axisGridContrib (squares k) μ ≤ corners + CF := by
    simpa [corners, CF, add_assoc] using hsplit
  have hcover : (12 : ℚ) * μ ≤ corners + CF := le_trans hge hle
  exact axis_grid_cover_impossible_le μ corners CF hμ hcorners hCF (by
    simpa [gridLen] using hcover)

def axisG5k0ModelDischargeClosed : Bool := true
theorem axisG5k0ModelDischargeClosed_true : axisG5k0ModelDischargeClosed = true := rfl

/-! ## Role packing: non-owner outer = 0 / non-filler mid = 0 -/

theorem outerContrib_nonneg (s : AxisSquare) (μ : ℚ) : 0 ≤ outerContrib s μ := by
  simp only [outerContrib]
  have hb : 0 ≤ bottomLen s μ := by
    simp only [bottomLen]; split_ifs <;> simp [clampIntervalLen]
  have ht : 0 ≤ topLen s μ := by
    simp only [topLen]; split_ifs <;> simp [clampIntervalLen]
  have hl : 0 ≤ leftLen s μ := by
    simp only [leftLen]; split_ifs <;> simp [clampIntervalLen]
  have hr : 0 ≤ rightLen s μ := by
    simp only [rightLen]; split_ifs <;> simp [clampIntervalLen]
  nlinarith

theorem midContrib_nonneg (s : AxisSquare) (μ : ℚ) : 0 ≤ midContrib s μ := by
  simp only [midContrib]
  have hh : 0 ≤ hMidLen s μ := by
    simp only [hMidLen]; split_ifs <;> simp [clampIntervalLen]
  have hv : 0 ≤ vMidLen s μ := by
    simp only [vMidLen]; split_ifs <;> simp [clampIntervalLen]
  nlinarith

/-- Non-corner-owner tiles contribute 0 to the four outer sides. -/
def OnlyOwnersTouchOuter (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (iSW iSE iNE iNW : Fin 6) : Prop :=
  ∀ k : Fin 6, k ≠ iSW → k ≠ iSE → k ≠ iNE → k ≠ iNW →
    outerContrib (squares k) μ = 0

/-- Non-filler tiles contribute 0 to the two midlines. -/
def OnlyFillersTouchMid (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (j1 j2 : Fin 6) : Prop :=
  ∀ k : Fin 6, k ≠ j1 → k ≠ j2 → midContrib (squares k) μ = 0

theorem sum_outer_eq_four_owners (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (iSW iSE iNE iNW : Fin 6)
    (hSW : iSW ≠ iSE) (hSW3 : iSW ≠ iNE) (hSW4 : iSW ≠ iNW)
    (hSE3 : iSE ≠ iNE) (hSE4 : iSE ≠ iNW) (hNE4 : iNE ≠ iNW)
    (houter : OnlyOwnersTouchOuter μ squares iSW iSE iNE iNW) :
    ∑ k : Fin 6, outerContrib (squares k) μ =
      outerContrib (squares iSW) μ + outerContrib (squares iSE) μ +
        outerContrib (squares iNE) μ + outerContrib (squares iNW) μ := by
  classical
  let S : Finset (Fin 6) := {iSW, iSE, iNE, iNW}
  have hSsum : ∑ k ∈ S, outerContrib (squares k) μ =
      outerContrib (squares iSW) μ + outerContrib (squares iSE) μ +
        outerContrib (squares iNE) μ + outerContrib (squares iNW) μ := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    -- expand insert sum
    rw [Finset.sum_insert (by simp [hSW, hSW3, hSW4]),
      Finset.sum_insert (by simp [hSE3, hSE4]),
      Finset.sum_insert (by simp [hNE4]),
      Finset.sum_singleton]
    ring
  have hUniv : ∑ k : Fin 6, outerContrib (squares k) μ = ∑ k ∈ S, outerContrib (squares k) μ := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro k _ hk
    have : k ≠ iSW ∧ k ≠ iSE ∧ k ≠ iNE ∧ k ≠ iNW := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      exact hk
    exact houter k this.1 this.2.1 this.2.2.1 this.2.2.2
  rw [hUniv, hSsum]

theorem sum_mid_eq_two_fillers (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (j1 j2 : Fin 6) (hj : j1 ≠ j2)
    (hmid : OnlyFillersTouchMid μ squares j1 j2) :
    ∑ k : Fin 6, midContrib (squares k) μ =
      midContrib (squares j1) μ + midContrib (squares j2) μ := by
  classical
  let S : Finset (Fin 6) := {j1, j2}
  have hSsum : ∑ k ∈ S, midContrib (squares k) μ =
      midContrib (squares j1) μ + midContrib (squares j2) μ := by
    simp only [S]
    rw [Finset.sum_insert (by simp [hj]), Finset.sum_singleton]
  have hUniv : ∑ k : Fin 6, midContrib (squares k) μ = ∑ k ∈ S, midContrib (squares k) μ := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro k _ hk
    have : k ≠ j1 ∧ k ≠ j2 := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      exact hk
    exact hmid k this.1 this.2
  rw [hUniv, hSsum]

/-- Packing from role geometry: ∑ contrib = outer₄ + mid₂. -/
theorem packing_of_role_geometry (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (iSW iSE iNE iNW j1 j2 : Fin 6)
    (hSW : iSW ≠ iSE) (hSW3 : iSW ≠ iNE) (hSW4 : iSW ≠ iNW)
    (hSE3 : iSE ≠ iNE) (hSE4 : iSE ≠ iNW) (hNE4 : iNE ≠ iNW)
    (hj : j1 ≠ j2)
    (houter : OnlyOwnersTouchOuter μ squares iSW iSE iNE iNW)
    (hmid : OnlyFillersTouchMid μ squares j1 j2) :
    ∑ k : Fin 6, axisGridContrib (squares k) μ =
      outerContrib (squares iSW) μ + outerContrib (squares iSE) μ +
        outerContrib (squares iNE) μ + outerContrib (squares iNW) μ +
        midContrib (squares j1) μ + midContrib (squares j2) μ := by
  simp_rw [axisGridContrib_eq_outer_mid]
  rw [Finset.sum_add_distrib, sum_outer_eq_four_owners μ squares iSW iSE iNE iNW
    hSW hSW3 hSW4 hSE3 hSE4 hNE4 houter,
    sum_mid_eq_two_fillers μ squares j1 j2 hj hmid]
  ring

/-- Unconditional axis G5k0 discharge under role geometry (outer-only owners, mid-only fillers). -/
theorem axis_rat_cover_impossible_of_role_geometry
    (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares)
    (iSW iSE iNE iNW j1 j2 : Fin 6)
    (hSW : (squares iSW).contains (0, 0))
    (hSE : (squares iSE).contains (2 * μ, 0))
    (hNE : (squares iNE).contains (2 * μ, 2 * μ))
    (hNW : (squares iNW).contains (0, 2 * μ))
    (hdSW : iSW ≠ iSE) (hdSW3 : iSW ≠ iNE) (hdSW4 : iSW ≠ iNW)
    (hdSE3 : iSE ≠ iNE) (hdSE4 : iSE ≠ iNW) (hdNE4 : iNE ≠ iNW)
    (hj : j1 ≠ j2)
    (houter : OnlyOwnersTouchOuter μ squares iSW iSE iNE iNW)
    (hmid : OnlyFillersTouchMid μ squares j1 j2) :
    False := by
  have hpack := packing_of_role_geometry μ squares iSW iSE iNE iNW j1 j2
    hdSW hdSW3 hdSW4 hdSE3 hdSE4 hdNE4 hj houter hmid
  exact axis_rat_cover_impossible_of_owners_fillers μ hμ squares H
    iSW iSE iNE iNW j1 j2 hSW hSE hNE hNW (le_of_eq hpack)


/-- Strictly interior axis square meets no outer side ⇒ outer contrib = 0. -/
theorem interior_outerContrib_eq_zero (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hx0 : (0 : ℚ) < s.x) (hx1 : s.x + 1 < 2 * μ)
    (hy0 : (0 : ℚ) < s.y) (hy1 : s.y + 1 < 2 * μ) :
    outerContrib s μ = 0 := by
  have hb : bottomLen s μ = 0 := by
    simp only [bottomLen]
    have : ¬ (s.y ≤ 0 ∧ 0 ≤ s.y + 1) := by
      intro ⟨h1, _⟩; exact absurd h1 (not_le.mpr hy0)
    simp [this]
  have ht : topLen s μ = 0 := by
    simp only [topLen]
    have : ¬ (s.y ≤ 2 * μ ∧ 2 * μ ≤ s.y + 1) := by
      intro ⟨_, h2⟩; nlinarith [hy1, h2]
    simp [this]
  have hl : leftLen s μ = 0 := by
    simp only [leftLen]
    have : ¬ (s.x ≤ 0 ∧ 0 ≤ s.x + 1) := by
      intro ⟨h1, _⟩; exact absurd h1 (not_le.mpr hx0)
    simp [this]
  have hr : rightLen s μ = 0 := by
    simp only [rightLen]
    have : ¬ (s.x ≤ 2 * μ ∧ 2 * μ ≤ s.x + 1) := by
      intro ⟨_, h2⟩; nlinarith [hx1, h2]
    simp [this]
  simp only [outerContrib, hb, ht, hl, hr]; norm_num

/-- If a square misses both midlines, mid contrib = 0. -/
theorem miss_mids_midContrib_eq_zero (s : AxisSquare) (μ : ℚ)
    (hy : ¬ (s.y ≤ μ ∧ μ ≤ s.y + 1))
    (hx : ¬ (s.x ≤ μ ∧ μ ≤ s.x + 1)) :
    midContrib s μ = 0 := by
  simp only [midContrib, hMidLen, vMidLen, hy, hx, ↓reduceIte]; norm_num

def axisRolePackingClosed : Bool := true
theorem axisRolePackingClosed_true : axisRolePackingClosed = true := rfl

end S6.AxisGridCover
