import Mathlib.Tactic

/-!
# Parallel chord budget B(μ) — algebraic fragment of R29N.2

Manuscript R29N.2 uses a uniform parallel-section budget `B = B(μ) < 1`
and grid-length comparisons. This module proves the **pure rational
inequalities** used in the contradiction; it does **not** construct `B(μ)`
from packing geometry nor re-prove R13 certificates.
-/

namespace S6.ParallelBudget

/-- Abstract parallel budget hypothesis used in R29N.2. -/
structure BudgetHyp where
  μ : ℚ
  B : ℚ
  vF : ℚ
  hμ : 1 < μ
  hB : B < 1
  hv : vF < μ

/-- Side-gap case bound: `8 + 3 B + vF < 11 + μ`. -/
theorem sideGap_bound (h : BudgetHyp) :
    (8 : ℚ) + 3 * h.B + h.vF < 11 + h.μ := by
  have : (8 : ℚ) + 3 * h.B + h.vF < 8 + 3 * 1 + h.μ := by
    have h3 : (3 : ℚ) * h.B < 3 * 1 := by
      nlinarith [h.hB]
    nlinarith [h.hv, h3]
  nlinarith

/-- For `μ > 1`: `11 + μ < 12 μ`. -/
theorem eleven_add_mu_lt_twelve_mu (μ : ℚ) (hμ : 1 < μ) :
    (11 : ℚ) + μ < 12 * μ := by
  nlinarith

/-- Side-gap R29N.2 contradiction algebra:
`8 + 3 B + vF < 12 μ` under `BudgetHyp`. -/
theorem sideGap_strict_lt_grid (h : BudgetHyp) :
    (8 : ℚ) + 3 * h.B + h.vF < 12 * h.μ := by
  have h1 := sideGap_bound h
  have h2 := eleven_add_mu_lt_twelve_mu h.μ h.hμ
  nlinarith

/-- No-side-gap case: `8 + 2 B + 2 μ < 12 μ` when `B < 1`, `μ > 1`. -/
theorem noSideGap_strict_lt_grid (μ B : ℚ) (hμ : 1 < μ) (hB : B < 1) :
    (8 : ℚ) + 2 * B + 2 * μ < 12 * μ := by
  nlinarith

/-- Equivalent form used in the manuscript write-up:
assuming a putative covering inequality `12 μ ≤ 8 + 3 B + vF` yields `False`. -/
theorem sideGap_covering_impossible (h : BudgetHyp)
    (hp : (12 : ℚ) * h.μ ≤ 8 + 3 * h.B + h.vF) : False := by
  have := sideGap_strict_lt_grid h
  nlinarith

theorem noSideGap_covering_impossible (μ B : ℚ) (hμ : 1 < μ) (hB : B < 1)
    (hp : (12 : ℚ) * μ ≤ 8 + 2 * B + 2 * μ) : False := by
  have := noSideGap_strict_lt_grid μ B hμ hB
  nlinarith

/-- Flag: algebraic fragment of R29N.2 parallel-budget contradictions closed. -/
def parallelBudgetAlgebraClosed : Bool := true

theorem parallelBudgetAlgebraClosed_true : parallelBudgetAlgebraClosed = true := rfl

def modellingNote : String :=
  "Proves the rational contradictions 8+3B+vF < 12μ and 8+2B+2μ < 12μ \
   under B<1, vF<μ, μ>1. Does not define B(μ) from geometry or import R13."

end S6.ParallelBudget
