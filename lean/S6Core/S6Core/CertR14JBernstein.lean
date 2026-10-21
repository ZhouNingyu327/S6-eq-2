import Mathlib.Tactic
import S6Core.BernsteinGeometryMap
import S6Core.CertJBoxIdentification
import S6Core.CertR14JPoly
import S6Core.NearEndRationalChecks

/-!
# Branch-c R-poly Bernstein-form identification (degree (3,1))

Sources: `check_round14_J_certificate.py` Bernstein transform on the unit square;
coeffs recomputed to match min `19/125`.

## Proved
* Explicit Bernstein basis eval of degree (3,1) equals `r14_c_R_poly` (ring).
* All 8 Bernstein coeffs ≥ `19/125`.
* Basis weights nonnegative on the unit box; partition of unity.
* Hence `∀ u v, InUnitBox u v → 19/125 ≤ r14_c_R_poly u v` (strictly `0 < ·`).
* Inhabits `R14CoverStrictPosCM` and `R14BranchC_R_PointwiseGeMin`.

## Still open
* `R14SE2ForcesSomeCMPolyNonpos` — living geometry does not Lean-reduce to
  “some R-poly ≤ 0” once R-polys are strictly positive; need bridge/junction
  constraints. `SE2PackageContradictsJCover` / `BernsteinForcesRawEmpty` stay false.

Not PrincipalClaim / namedClosersDischarged. Bridge + BernsteinExact* untouched.
-/

namespace S6.CertR14JBernstein

open S6.BernsteinGeometryMap
open S6.CertJBoxIdentification
open S6.CertR14JPoly
open S6.NearEndRationalChecks

/-! ## Bernstein basis degree 3 × 1 (explicit) -/

def B3_0 (u : ℚ) : ℚ := (1 - u) ^ 3
def B3_1 (u : ℚ) : ℚ := 3 * u * (1 - u) ^ 2
def B3_2 (u : ℚ) : ℚ := 3 * u ^ 2 * (1 - u)
def B3_3 (u : ℚ) : ℚ := u ^ 3
def B1_0 (v : ℚ) : ℚ := 1 - v
def B1_1 (v : ℚ) : ℚ := v

/-- Bernstein coeffs of branch-c R-poly, `(i,j)`. -/
def c00 : ℚ := 1
def c01 : ℚ := 1
def c10 : ℚ := (13 : ℚ) / 15
def c11 : ℚ := (13 : ℚ) / 15
def c20 : ℚ := (47 : ℚ) / 75
def c21 : ℚ := (13 : ℚ) / 25
def c30 : ℚ := (51 : ℚ) / 125
def c31 : ℚ := (19 : ℚ) / 125

def r14_c_R_bernsteinEval (u v : ℚ) : ℚ :=
  c00 * B3_0 u * B1_0 v + c01 * B3_0 u * B1_1 v +
    c10 * B3_1 u * B1_0 v + c11 * B3_1 u * B1_1 v +
    c20 * B3_2 u * B1_0 v + c21 * B3_2 u * B1_1 v +
    c30 * B3_3 u * B1_0 v + c31 * B3_3 u * B1_1 v

theorem r14_c_R_poly_eq_bernstein (u v : ℚ) :
    r14_c_R_poly u v = r14_c_R_bernsteinEval u v := by
  simp only [r14_c_R_poly, r14_c_R_bernsteinEval, c00, c01, c10, c11, c20, c21, c30, c31,
    B3_0, B3_1, B3_2, B3_3, B1_0, B1_1]
  ring

theorem c00_ge_min : r14_c_R_bernsteinMin ≤ c00 := by
  simp only [c00, r14_c_R_bernsteinMin]; native_decide
theorem c01_ge_min : r14_c_R_bernsteinMin ≤ c01 := by
  simp only [c01, r14_c_R_bernsteinMin]; native_decide
theorem c10_ge_min : r14_c_R_bernsteinMin ≤ c10 := by
  simp only [c10, r14_c_R_bernsteinMin]; native_decide
theorem c11_ge_min : r14_c_R_bernsteinMin ≤ c11 := by
  simp only [c11, r14_c_R_bernsteinMin]; native_decide
theorem c20_ge_min : r14_c_R_bernsteinMin ≤ c20 := by
  simp only [c20, r14_c_R_bernsteinMin]; native_decide
theorem c21_ge_min : r14_c_R_bernsteinMin ≤ c21 := by
  simp only [c21, r14_c_R_bernsteinMin]; native_decide
theorem c30_ge_min : r14_c_R_bernsteinMin ≤ c30 := by
  simp only [c30, r14_c_R_bernsteinMin]; native_decide
theorem c31_ge_min : r14_c_R_bernsteinMin ≤ c31 := by
  simp only [c31, r14_c_R_bernsteinMin]; native_decide

theorem B3_sum (u : ℚ) : B3_0 u + B3_1 u + B3_2 u + B3_3 u = 1 := by
  simp only [B3_0, B3_1, B3_2, B3_3]; ring

theorem B1_sum (v : ℚ) : B1_0 v + B1_1 v = 1 := by
  simp only [B1_0, B1_1]; ring

theorem B3_0_nonneg (u : ℚ) (hu : InUnitInterval u) : 0 ≤ B3_0 u := by
  have ⟨hu0, hu1⟩ := hu
  have : 0 ≤ 1 - u := by linarith
  simp only [B3_0]; positivity

theorem B3_1_nonneg (u : ℚ) (hu : InUnitInterval u) : 0 ≤ B3_1 u := by
  have ⟨hu0, hu1⟩ := hu
  have : 0 ≤ 1 - u := by linarith
  simp only [B3_1]; positivity

theorem B3_2_nonneg (u : ℚ) (hu : InUnitInterval u) : 0 ≤ B3_2 u := by
  have ⟨hu0, hu1⟩ := hu
  have : 0 ≤ 1 - u := by linarith
  simp only [B3_2]; positivity

theorem B3_3_nonneg (u : ℚ) (hu : InUnitInterval u) : 0 ≤ B3_3 u := by
  have ⟨hu0, hu1⟩ := hu
  simp only [B3_3]; positivity

theorem B1_0_nonneg (v : ℚ) (hv : InUnitInterval v) : 0 ≤ B1_0 v := by
  have ⟨hv0, hv1⟩ := hv
  simp only [B1_0]; linarith

theorem B1_1_nonneg (v : ℚ) (hv : InUnitInterval v) : 0 ≤ B1_1 v := by
  have ⟨hv0, hv1⟩ := hv
  simp only [B1_1]; exact hv0

theorem bernstein_weights_sum (u v : ℚ) :
    B3_0 u * B1_0 v + B3_0 u * B1_1 v + B3_1 u * B1_0 v + B3_1 u * B1_1 v +
      B3_2 u * B1_0 v + B3_2 u * B1_1 v + B3_3 u * B1_0 v + B3_3 u * B1_1 v = 1 := by
  have hexpand :
      (B3_0 u + B3_1 u + B3_2 u + B3_3 u) * (B1_0 v + B1_1 v) =
        B3_0 u * B1_0 v + B3_0 u * B1_1 v + B3_1 u * B1_0 v + B3_1 u * B1_1 v +
          B3_2 u * B1_0 v + B3_2 u * B1_1 v + B3_3 u * B1_0 v + B3_3 u * B1_1 v := by
    ring
  calc
    _ = (B3_0 u + B3_1 u + B3_2 u + B3_3 u) * (B1_0 v + B1_1 v) := hexpand.symm
    _ = (1 : ℚ) * 1 := by rw [B3_sum, B1_sum]
    _ = 1 := by ring

theorem r14_c_R_bernsteinEval_ge_min (u v : ℚ) (h : InUnitBox u v) :
    r14_c_R_bernsteinMin ≤ r14_c_R_bernsteinEval u v := by
  have ⟨hu0, hu1, hv0, hv1⟩ := h
  have hu : InUnitInterval u := ⟨hu0, hu1⟩
  have hv : InUnitInterval v := ⟨hv0, hv1⟩
  set m : ℚ := r14_c_R_bernsteinMin
  set w00 := B3_0 u * B1_0 v
  set w01 := B3_0 u * B1_1 v
  set w10 := B3_1 u * B1_0 v
  set w11 := B3_1 u * B1_1 v
  set w20 := B3_2 u * B1_0 v
  set w21 := B3_2 u * B1_1 v
  set w30 := B3_3 u * B1_0 v
  set w31 := B3_3 u * B1_1 v
  have hw00 : 0 ≤ w00 := mul_nonneg (B3_0_nonneg u hu) (B1_0_nonneg v hv)
  have hw01 : 0 ≤ w01 := mul_nonneg (B3_0_nonneg u hu) (B1_1_nonneg v hv)
  have hw10 : 0 ≤ w10 := mul_nonneg (B3_1_nonneg u hu) (B1_0_nonneg v hv)
  have hw11 : 0 ≤ w11 := mul_nonneg (B3_1_nonneg u hu) (B1_1_nonneg v hv)
  have hw20 : 0 ≤ w20 := mul_nonneg (B3_2_nonneg u hu) (B1_0_nonneg v hv)
  have hw21 : 0 ≤ w21 := mul_nonneg (B3_2_nonneg u hu) (B1_1_nonneg v hv)
  have hw30 : 0 ≤ w30 := mul_nonneg (B3_3_nonneg u hu) (B1_0_nonneg v hv)
  have hw31 : 0 ≤ w31 := mul_nonneg (B3_3_nonneg u hu) (B1_1_nonneg v hv)
  have hsum : w00 + w01 + w10 + w11 + w20 + w21 + w30 + w31 = 1 := by
    simpa [w00, w01, w10, w11, w20, w21, w30, w31] using bernstein_weights_sum u v
  have hcombo :
      m * (w00 + w01 + w10 + w11 + w20 + w21 + w30 + w31) ≤
        w00 * c00 + w01 * c01 + w10 * c10 + w11 * c11 +
          w20 * c20 + w21 * c21 + w30 * c30 + w31 * c31 := by
    have := c00_ge_min
    have := c01_ge_min
    have := c10_ge_min
    have := c11_ge_min
    have := c20_ge_min
    have := c21_ge_min
    have := c30_ge_min
    have := c31_ge_min
    nlinarith
  have heval :
      r14_c_R_bernsteinEval u v =
        w00 * c00 + w01 * c01 + w10 * c10 + w11 * c11 +
          w20 * c20 + w21 * c21 + w30 * c30 + w31 * c31 := by
    simp only [r14_c_R_bernsteinEval, w00, w01, w10, w11, w20, w21, w30, w31]
    ring
  have : m ≤ r14_c_R_bernsteinEval u v := by
    have h' := hcombo
    simp only [hsum, mul_one] at h'
    rwa [heval]
  exact this

theorem r14_c_R_poly_ge_min (u v : ℚ) (h : InUnitBox u v) :
    r14_c_R_bernsteinMin ≤ r14_c_R_poly u v := by
  rw [r14_c_R_poly_eq_bernstein]
  exact r14_c_R_bernsteinEval_ge_min u v h

theorem r14_c_R_poly_pos_on_unit (u v : ℚ) (h : InUnitBox u v) :
    0 < r14_c_R_poly u v :=
  lt_of_lt_of_le r14_c_R_bernsteinMin_pos (r14_c_R_poly_ge_min u v h)

theorem r14BranchC_R_PointwiseGeMin : R14BranchC_R_PointwiseGeMin :=
  r14_c_R_poly_ge_min

theorem r14CoverStrictPosCM : R14CoverStrictPosCM :=
  ⟨r14_c_R_poly_pos_on_unit, r14_m_R_poly_pos_on_unit'⟩

def r14CoverStrictPosCMProved : Bool := true
theorem r14CoverStrictPosCMProved_true : r14CoverStrictPosCMProved = true := rfl

def r14BranchC_R_PointwiseGeMinProved : Bool := true
theorem r14BranchC_R_PointwiseGeMinProved_true :
    r14BranchC_R_PointwiseGeMinProved = true := rfl

/-! ## Partial CoV constructibility (not living⇒nonpos) -/

theorem r14_branchC_u_of_z (z : ℚ) (hz0 : 0 ≤ z) (hz1 : z ≤ (2 : ℚ) / 5) :
    InUnitInterval ((5 : ℚ) / 2 * z) ∧ branchC_x ((5 : ℚ) / 2 * z) = z := by
  have hu0 : 0 ≤ (5 : ℚ) / 2 * z := by nlinarith
  have hu1 : (5 : ℚ) / 2 * z ≤ 1 := by nlinarith
  refine ⟨⟨hu0, hu1⟩, ?_⟩
  simp only [branchC_x]; ring

theorem r14_uvFromPackage_of_z_in_branchC
    (p : S6.CertJBoxIdentification.SE2FieldPackage S6.BernsteinGeometryMap.leaf_R14)
    (hz0 : 0 ≤ p.z) (hz1 : p.z ≤ (2 : ℚ) / 5) (v : ℚ) (hv : InUnitInterval v) :
    ∃ u : ℚ, R14UVFromPackage p u v := by
  set u := (5 : ℚ) / 2 * p.z
  have ⟨hu, hx⟩ := r14_branchC_u_of_z p.z hz0 hz1
  refine ⟨u, ⟨⟨hu.1, hu.2, hv.1, hv.2⟩, Or.inl ?_⟩⟩
  simpa [u] using hx.symm

def r14SE2ForcesSomeCMPolyNonposProved : Bool := false
theorem r14SE2ForcesSomeCMPolyNonposProved_false :
    r14SE2ForcesSomeCMPolyNonposProved = false := rfl

def se2PackageContradictsJCoverProved : Bool := false
theorem se2PackageContradictsJCoverProved_false :
    se2PackageContradictsJCoverProved = false := rfl

def bernsteinForcesRawEmptyProved : Bool := false
theorem bernsteinForcesRawEmptyProved_false : bernsteinForcesRawEmptyProved = false := rfl

theorem bernsteinForcesRawEmpty_R14_of_forces
    (hforce : R14SE2ForcesSomeCMPolyNonpos) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of r14CoverStrictPosCM hforce

def blockedReason : String :=
  "CLOSED (1): branch-c R Bernstein-form ID; R14CoverStrictPosCM inhabited. \
   BLOCKED (2): R14SE2ForcesSomeCMPolyNonpos — living SE2 does not Lean-imply \
   R-poly≤0 (R-polys strictly positive on cover); need bridge/junction geometry. \
   BernsteinForcesRawEmpty false."

def openStatus : String :=
  "CLOSED: R14CoverStrictPosCM; R14BranchC_R_PointwiseGeMin. \
   OPEN: R14SE2ForcesSomeCMPolyNonpos; SE2PackageContradictsJCover; \
   BernsteinForcesRawEmpty; R17/R27–28. Not PrincipalClaim / namedClosers."

end S6.CertR14JBernstein
