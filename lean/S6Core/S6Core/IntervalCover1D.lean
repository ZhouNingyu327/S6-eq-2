import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# 1D interval covering ⇒ sum of lengths

If a finite family of closed intervals covers `[a,b] ⊆ ℝ`, then
`b - a ≤ ∑ (hi - lo)`. Via Lebesgue measure mono + `measure_iUnion_fintype_le`.
-/

namespace S6.IntervalCover1D

open MeasureTheory Set Real

def iLen (lo hi : ℝ) : ℝ := max (hi - lo) 0

theorem iLen_of_le (lo hi : ℝ) (hle : lo ≤ hi) : iLen lo hi = hi - lo :=
  max_eq_left (sub_nonneg.mpr hle)

theorem cover_Icc_sum_lengths {ι : Type*} [Fintype ι] (a b : ℝ) (_hab : a ≤ b)
    (lo hi : ι → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hcover : Icc a b ⊆ ⋃ i, Icc (lo i) (hi i)) :
    b - a ≤ ∑ i, iLen (lo i) (hi i) := by
  have hmono : volume (Icc a b) ≤ volume (⋃ i, Icc (lo i) (hi i)) :=
    measure_mono hcover
  have hsub : volume (⋃ i, Icc (lo i) (hi i)) ≤ ∑ i, volume (Icc (lo i) (hi i)) :=
    measure_iUnion_fintype_le volume (fun i => Icc (lo i) (hi i))
  have hchain : volume (Icc a b) ≤ ∑ i, volume (Icc (lo i) (hi i)) :=
    hmono.trans hsub
  have hba : volume (Icc a b) = ENNReal.ofReal (b - a) := volume_Icc
  have hii : ∀ i, volume (Icc (lo i) (hi i)) = ENNReal.ofReal (iLen (lo i) (hi i)) := by
    intro i
    rw [volume_Icc, iLen_of_le _ _ (hle i)]
  simp_rw [hba, hii] at hchain
  have hnonneg : ∀ i, 0 ≤ iLen (lo i) (hi i) := fun i => le_max_right _ _
  have hsum' : (∑ i, ENNReal.ofReal (iLen (lo i) (hi i))) =
      ENNReal.ofReal (∑ i, iLen (lo i) (hi i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    exact fun i _ => hnonneg i
  rw [hsum'] at hchain
  have hsum_nonneg : 0 ≤ ∑ i, iLen (lo i) (hi i) :=
    Finset.sum_nonneg fun i _ => hnonneg i
  exact (ENNReal.ofReal_le_ofReal_iff hsum_nonneg).mp hchain

theorem cover_Icc_sum_diff {ι : Type*} [Fintype ι] (a b : ℝ) (hab : a ≤ b)
    (lo hi : ι → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hcover : Icc a b ⊆ ⋃ i, Icc (lo i) (hi i)) :
    b - a ≤ ∑ i, (hi i - lo i) := by
  have h := cover_Icc_sum_lengths a b hab lo hi hle hcover
  simp_rw [iLen_of_le _ _ (hle _)] at h
  exact h

theorem cover_Icc_sum_diff_of_valid {ι : Type*} [Fintype ι] (a b : ℝ) (hab : a ≤ b)
    (lo hi : ι → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hcover : Icc a b ⊆ ⋃ i, Icc (lo i) (hi i)) :
    b - a ≤ ∑ i, (hi i - lo i) :=
  cover_Icc_sum_diff a b hab lo hi hle hcover

end S6.IntervalCover1D
