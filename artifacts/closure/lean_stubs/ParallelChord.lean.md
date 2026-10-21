# Pseudo-Lean stub: ParallelChord

```lean
-- NOT checked by Lean in this environment. For local mathlib ≥4.
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace S6

/-- Parallel-chord budget for a unit square meeting two parallel lines at distance d ∈ (1, √2]. -/
noncomputable def B (d : ℝ) : ℝ :=
  if d ≤ 3 / (2 * Real.sqrt 2) then
    d - Real.sqrt (d^2 - 1)
  else
    2 * (Real.sqrt 2 - d)

theorem B_lt_one {d : ℝ} (hd1 : 1 < d) (hd2 : d ≤ Real.sqrt 2) : B d < 1 := by
  sorry -- prove via the two-case maximisation in main text (M4)

/-- If a unit square meets two parallel lines at distance d>1 in nonempty chords of lengths ℓ₁,ℓ₂, then ℓ₁+ℓ₂ ≤ B d. -/
theorem parallel_chord_bound
    {d ℓ₁ ℓ₂ : ℝ} (hd : 1 < d) (hsum : ℓ₁ + ℓ₂ ≤ B d) : True := by
  trivial
  -- Replace with the actual geometric hypothesis formalisation.

end S6
```
