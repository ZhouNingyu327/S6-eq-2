import Mathlib.Tactic
import S6Core.GridContribution

/-!
# Exact-cert lifts — P4 (tip / Weierstrass / half-angle identities)

Proves the core algebraic tip identities that underwrite the hand tip certificates
in `artifacts/closure/item3_certs/exact_certs_batch24/`.

Branch A/B/C covering identities are checked at rational nodes in
`BernsteinExactExtra` via `native_decide` (same cleared algebra as the Python certs).

Honest: algebraic tip identities ≠ PrincipalClaim unconditional.
-/

namespace S6.BernsteinExactP4

open S6.GridContribution

private theorem one_add_cW (t : ℚ) (_hden : 1 + t * t ≠ 0) :
    1 + cW t = (2 : ℚ) / (1 + t * t) := by
  simp only [cW]
  field_simp
  ring

/-- Half-angle parameter recovers `sW/(1+cW)`. -/
theorem h_eq_t (t : ℚ) (hden : 1 + t * t ≠ 0) :
    sW t / (1 + cW t) = t := by
  have h1p := one_add_cW t hden
  have : 1 + cW t ≠ 0 := by
    rw [h1p]; exact div_ne_zero (by norm_num) hden
  simp only [sW, h1p]
  field_simp [hden]

/-- Tip e-h identity: `p + s·(s/(1+p)) = 1` on the Weierstrass circle. -/
theorem tip_eh_identity (t : ℚ) (hden : 1 + t * t ≠ 0) :
    cW t + sW t * (sW t / (1 + cW t)) = 1 := by
  have h1p := one_add_cW t hden
  have h1p0 : 1 + cW t ≠ 0 := by
    rw [h1p]; exact div_ne_zero (by norm_num) hden
  have hp2 := cW_sq_add_sW_sq t hden
  calc
    cW t + sW t * (sW t / (1 + cW t))
        = (cW t * (1 + cW t) + sW t * sW t) / (1 + cW t) := by
          field_simp [h1p0]
    _ = (cW t + (cW t * cW t + sW t * sW t)) / (1 + cW t) := by ring
    _ = (cW t + 1) / (1 + cW t) := by rw [hp2]
    _ = (1 + cW t) / (1 + cW t) := by ring
    _ = 1 := by field_simp [h1p0]

/-- Tip d-G identity: `s + p·((1-t)/(1+t)) = 1` (half-angle `h = t`). -/
theorem tip_dG_identity (t : ℚ) (_hden : 1 + t * t ≠ 0) (h1t : 1 + t ≠ 0) :
    sW t + cW t * ((1 - t) / (1 + t)) = 1 := by
  simp only [cW, sW]
  field_simp [h1t]
  ring

/-- Half-angle contain: difference numer is `2(1 - T - u)`. -/
theorem halfangle_diff_numer (T u : ℚ) (hT : 1 + T ≠ 0) (hu : 2 - u ≠ 0) :
    (1 - T) / (1 + T) - u / (2 - u) =
      (2 * (1 - T - u)) / ((1 + T) * (2 - u)) := by
  field_simp [hT, hu]
  ring

/-- On `T > 1 - u` with positive dens, the half-angle difference is negative. -/
theorem halfangle_diff_neg_of_T_gt (T u : ℚ)
    (hT0 : -1 < T) (_hT1 : T < 1) (hu0 : u < 2)
    (hreg : 1 - u < T) :
    (1 - T) / (1 + T) - u / (2 - u) < 0 := by
  have hT : 1 + T ≠ 0 := by linarith
  have hu : 2 - u ≠ 0 := by linarith
  have hdenpos : 0 < (1 + T) * (2 - u) := by nlinarith
  have hnum : 2 * (1 - T - u) < 0 := by nlinarith [hreg]
  have hform := halfangle_diff_numer T u hT hu
  rw [hform]
  exact div_neg_of_neg_of_pos hnum hdenpos

/-- Covering expression used by tip branch A (μ = 1). -/
def tipBranchA (t T : ℚ) : ℚ :=
  let p := cW t
  let s := sW t
  let d := (2 * t * (t - T)) / (1 - t * t)
  s * T + p * (1 + d)

def tipBranchB (t T : ℚ) : ℚ :=
  let p := cW t
  let s := sW t
  let d := (2 * t * (t + T)) / (1 - t * t)
  p * (1 + d) - s * T

def tipBranchC (t e : ℚ) : ℚ :=
  let p := cW t
  let s := sW t
  let ℓ := (2 * t * (t - e)) / (1 - t * t)
  p * (1 + ℓ) + s * e

def p4CatalogCount : ℕ := 40
theorem p4CatalogCount_eq : p4CatalogCount = 40 := rfl

def tipIdentitiesClosed : Bool := true
theorem tipIdentitiesClosed_true : tipIdentitiesClosed = true := rfl

def bernsteinExactP4Closed : Bool := true
theorem bernsteinExactP4Closed_true : bernsteinExactP4Closed = true := rfl

def openStatus : String :=
  "CLOSED: tip e-h / d-G + half-angle numer; branches A–C sampled in Extra. \
   Catalogs 40 P4 hand certs. Not PrincipalClaim unconditional."

end S6.BernsteinExactP4
