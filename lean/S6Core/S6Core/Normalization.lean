import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Normalization idempotence (M1 algebraic core)
-/

namespace S6.Normalization

def clip (β lo hi : ℚ) : ℚ := min (max β lo) hi

theorem clip_idempotent (β lo hi : ℚ) (hle : lo ≤ hi) :
    clip (clip β lo hi) lo hi = clip β lo hi := by
  simp only [clip]
  rcases le_total β lo with hβlo | hloβ
  · have hmax : max β lo = lo := max_eq_right hβlo
    have hmin : min lo hi = lo := min_eq_left hle
    have hclip : min (max β lo) hi = lo := by simpa [hmax] using hmin
    simp [hclip, max_self, hmin]
  · rcases le_total β hi with hβhi | hhiβ
    · have hmax : max β lo = β := max_eq_left hloβ
      have hmin : min β hi = β := min_eq_left hβhi
      have hclip : min (max β lo) hi = β := by simpa [hmax] using hmin
      simpa [hclip, hmax, hmin]
    · have hmax : max β lo = β := max_eq_left hloβ
      have hmin : min β hi = hi := min_eq_right hhiβ
      have hclip : min (max β lo) hi = hi := by simpa [hmax] using hmin
      simp [hclip, max_eq_left hle, min_self]

def pushLeft (α : ℚ) : ℚ := max α 0

theorem pushLeft_idempotent (α : ℚ) : pushLeft (pushLeft α) = pushLeft α := by
  simp only [pushLeft]
  rcases le_total α 0 with h | h
  · simp [max_eq_right h]
  · simp [max_eq_left h]

theorem clip_of_clipped (β lo hi : ℚ) (hle : lo ≤ hi)
    (hlo : lo ≤ β) (hhi : β ≤ hi) : clip β lo hi = β := by
  simp only [clip, max_eq_left hlo, min_eq_left hhi]

end S6.Normalization
