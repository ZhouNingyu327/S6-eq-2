# Pseudo-Lean stub: BernsteinChart (R41)

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Data.List.Basic

namespace S6

/-- Nonnegativity of a bivariate Bernstein coefficient list. -/
def bernsteinNonneg (coeffs : List Rat) : Prop :=
  coeffs.all (fun c => c ≥ 0)

/-- Example: load coefficients from the JSON chart and decide. -/
theorem r41_chart_example_nonneg :
    bernsteinNonneg [1, 1, 2, 5/2] := by
  native_decide

-- Real work: parse round41_corner_certificate.json into Lean
-- and run bernsteinNonneg on each of the 9 charts (219 coeffs).

end S6
```
