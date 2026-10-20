import Mathlib.Data.Rat.Defs

/-!
# R41 Bernstein nonnegativity — native_decide samples
Full JSON (219 coeffs) verified in python_verifiers/verify_A_lemmas.py
-/

namespace S6.BernsteinChart

def nonneg : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonneg cs

theorem sample_chart_nonneg :
    nonneg [1, 1, 2, 5/2, 352/19683, 0] = true := by
  native_decide

theorem sample_strict_pos_subset :
    nonneg [352/19683, 1/1000000] = true := by
  native_decide

end S6.BernsteinChart
