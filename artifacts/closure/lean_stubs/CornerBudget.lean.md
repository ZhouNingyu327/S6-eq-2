# Pseudo-Lean stub: CornerBudget

```lean
import Mathlib.Data.Real.Basic

namespace S6

/-- Grid contribution of one corner block is at most 2. -/
theorem corner_grid_budget_le_two
    (c s L S U : ℝ)
    (hcs : c ≥ 0 ∧ s ≥ 0 ∧ c^2 + s^2 = 1)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hU : 0 ≤ U)
    -- plus the normalisation relations from R2 lemma 3
    : L + S + U ≤ 2 := by
  sorry

end S6
```
