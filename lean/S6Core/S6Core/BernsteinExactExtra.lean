import Mathlib.Tactic
import S6Core.BernsteinExactP4
import S6Core.BernsteinExactP5
import S6Core.GridContribution

/-!
# Extra exact-cert rational samples (tip evaluations)

Concrete `native_decide` evaluations of tip identities at rational Weierstrass nodes,
including tip branches A/B/C covering collapse, plus catalog size checks.

Honest: samples ≠ PrincipalClaim.
-/

namespace S6.BernsteinExactExtra

open S6.BernsteinExactP4
open S6.BernsteinExactP5
open S6.GridContribution

theorem tip_eh_at_half :
    let t : ℚ := 1 / 2
    cW t + sW t * (sW t / (1 + cW t)) = 1 := by
  native_decide

theorem tip_eh_at_fifth :
    let t : ℚ := 1 / 5
    cW t + sW t * (sW t / (1 + cW t)) = 1 := by
  native_decide

theorem tip_dG_at_half :
    let t : ℚ := 1 / 2
    sW t + cW t * ((1 - t) / (1 + t)) = 1 := by
  native_decide

theorem tip_dG_at_third :
    let t : ℚ := 1 / 3
    sW t + cW t * ((1 - t) / (1 + t)) = 1 := by
  native_decide

theorem tip_branchA_sample1 :
    tipBranchA (1 / 3 : ℚ) (1 / 7 : ℚ) = 1 := by
  native_decide

theorem tip_branchA_sample2 :
    tipBranchA (2 / 5 : ℚ) (0 : ℚ) = 1 := by
  native_decide

theorem tip_branchB_sample1 :
    tipBranchB (1 / 4 : ℚ) (1 / 5 : ℚ) = 1 := by
  native_decide

theorem tip_branchC_sample1 :
    tipBranchC (1 / 3 : ℚ) (1 / 10 : ℚ) = 1 := by
  native_decide

theorem tip_branchC_sample2 :
    tipBranchC (1 / 6 : ℚ) (0 : ℚ) = 1 := by
  native_decide

theorem halfangle_numer_sample :
    -- Need T > 1 - u; take T = 9/10, u = 1/5 (1-u = 4/5 < 9/10).
    (1 - (9 : ℚ) / 10) / (1 + (9 : ℚ) / 10) - (1 : ℚ) / 5 / (2 - (1 : ℚ) / 5) < 0 := by
  native_decide

theorem halfangle_diff_form_sample :
    (1 - (2 : ℚ) / 3) / (1 + (2 : ℚ) / 3) - (1 : ℚ) / 4 / (2 - (1 : ℚ) / 4) =
      (2 * (1 - (2 : ℚ) / 3 - (1 : ℚ) / 4)) /
        ((1 + (2 : ℚ) / 3) * (2 - (1 : ℚ) / 4)) := by
  native_decide

theorem p4_p5_counts :
    p4CatalogCount = 40 ∧ p5CatalogCount = 60 := by
  native_decide

theorem p5_bernstein_casesplit_nonneg :
    nonnegList bernstein_4_5h_h2 = true :=
  bernstein_4_5h_h2_nonneg

def bernsteinExactExtraClosed : Bool := true
theorem bernsteinExactExtraClosed_true : bernsteinExactExtraClosed = true := rfl

def openStatus : String :=
  "CLOSED: tip samples A/B/C + half-angle + P4/P5 counts. Not PrincipalClaim."

end S6.BernsteinExactExtra
