import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.BernsteinGeometryMap
import S6Core.CertGeometryIdentification
import S6Core.CertJBoxIdentification
import S6Core.NearEndRationalChecks
import S6Core.LivingLeafCertDischarge
import S6Core.ChordLength

/-!
# R14 J multivariate polys / rectangle cover (partial Lean port)

Sources (read-only): `artifacts/ex/all/round14_J_certificate.json`,
`artifacts/ex/all/check_round14_J_certificate.py`,
`artifacts/closure/CERT_TO_LEAN_HANDOFF.md`.

## Proved
* Binary-subdivision `pathInterval` (same encoding as the checker).
* Original `(h,n,R)` and branch-c/m/s change-of-variables `(x,B)`.
* Transformed branch R-polys as Lean functions of `(u,v)`.
* Branch-m R-poly **strictly positive** on the unit box.
* Branch-m rectangle cover enumeration (10 paths; areas sum to 1).
* Sample pointwise evaluations + Bernstein min tokens for branch-c.
* Conditional: `R14CoverStrictPosCM` + `R14SE2ForcesSomeCMPolyNonpos`
  ⇒ `SE2PackageContradictsJCover "R14"`.

## Blocked
* Branch-c R-poly pointwise ≥ bernsteinMin on the whole square (needs Bernstein-form ID).
* P-polys (Pb/Pm transforms) — too large; min_P tokens stay in NearEndRationalChecks.
* `R14SE2ForcesSomeCMPolyNonpos` — no Lean map from SE2 `(z,d,…)` onto a cover point
  with some J R-poly ≤ 0.
* Hence `SE2PackageContradictsJCover` / `BernsteinForcesRawEmpty` stay false.

Not PrincipalClaim / namedClosersDischarged. Bridge + BernsteinExact* untouched.
-/

namespace S6.CertR14JPoly

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.BernsteinGeometryMap
open S6.CertGeometryIdentification
open S6.CertJBoxIdentification
open S6.NearEndRationalChecks
open S6.LivingLeafCertDischarge
open S6.ChordLength

/-! ## Path → rectangle (checker `interval`) -/

def pathStep (lo hi : ℚ) (bit : Char) : ℚ × ℚ :=
  let mid := (lo + hi) / 2
  if bit = '0' then (lo, mid) else (mid, hi)

def pathIntervalGo (cs : List Char) (axis : ℕ) (loU hiU loV hiV : ℚ) :
    (ℚ × ℚ) × (ℚ × ℚ) :=
  match cs with
  | [] => ((loU, hiU), (loV, hiV))
  | c :: rest =>
    if axis % 2 = 0 then
      let p := pathStep loU hiU c
      pathIntervalGo rest (axis + 1) p.1 p.2 loV hiV
    else
      let p := pathStep loV hiV c
      pathIntervalGo rest (axis + 1) loU hiU p.1 p.2

/-- Axis-alternating binary subdivision of `[0,1]²`. -/
def pathInterval (path : String) : (ℚ × ℚ) × (ℚ × ℚ) :=
  pathIntervalGo path.toList 0 0 1 0 1

def InRect (u v loU hiU loV hiV : ℚ) : Prop :=
  loU ≤ u ∧ u ≤ hiU ∧ loV ≤ v ∧ v ≤ hiV

theorem pathInterval_empty : pathInterval "" = ((0, 1), (0, 1)) := by native_decide
theorem pathInterval_00 : pathInterval "00" = ((0, 1 / 2), (0, 1 / 2)) := by native_decide
theorem pathInterval_10 : pathInterval "10" = ((1 / 2, 1), (0, 1 / 2)) := by native_decide
theorem pathInterval_1111 : pathInterval "1111" = ((3 / 4, 1), (3 / 4, 1)) := by native_decide

/-! ## Original J geometry (checker symbols `h,n,R`) -/

def J_h (x y : ℚ) : ℚ := 2 - x - 3 * y + x * y
def J_n (x y : ℚ) : ℚ := x + y - x * y
def J_R (x y : ℚ) : ℚ := 1 - x - 2 * y + x * y

/-! ## Branch change-of-variables -/

def branchC_x (u : ℚ) : ℚ := (2 : ℚ) / 5 * u
def branchM_x (u : ℚ) : ℚ := (2 : ℚ) / 5 + (1 : ℚ) / 40 * u
def branchS_x (u : ℚ) : ℚ := (17 : ℚ) / 40 + (23 : ℚ) / 40 * u
def branchM_B : ℚ := (4 : ℚ) / 15
def branchC_B (x : ℚ) : ℚ := x * x / (1 - 2 * x * x)

theorem branchC_x_mem_unit (u : ℚ) (hu : InUnitInterval u) :
    0 ≤ branchC_x u ∧ branchC_x u ≤ (2 : ℚ) / 5 := by
  have ⟨hu0, hu1⟩ := hu
  simp only [branchC_x]
  constructor <;> nlinarith

theorem branchM_x_mem (u : ℚ) (hu : InUnitInterval u) :
    (2 : ℚ) / 5 ≤ branchM_x u ∧ branchM_x u ≤ (17 : ℚ) / 40 := by
  have ⟨hu0, hu1⟩ := hu
  simp only [branchM_x]
  constructor <;> nlinarith

/-! ## Transformed branch R-polys (`transformed_polynomials[0]`) -/

def r14_c_R_poly (u v : ℚ) : ℚ :=
  (8 : ℚ) * u ^ 3 * v / 125 + (16 : ℚ) * u ^ 3 / 125
    - (8 : ℚ) * u ^ 2 * v / 25 - (8 : ℚ) * u ^ 2 / 25
    - (2 : ℚ) * u / 5 + 1

def r14_m_R_poly (u v : ℚ) : ℚ :=
  u * v / 10 - (3 : ℚ) * u / 8 - (32 : ℚ) * v / 5 + 9

def r14_s_R_poly (u v : ℚ) : ℚ :=
  (12167 : ℚ) * u ^ 3 * v / 64000 + (12167 : ℚ) * u ^ 3 / 64000
    - (57661 : ℚ) * u ^ 2 * v / 64000 - (121141 : ℚ) * u ^ 2 / 64000
    + (78821 : ℚ) * u * v / 64000 + (58581 : ℚ) * u / 64000
    - (33327 : ℚ) * v / 64000 + (50393 : ℚ) / 64000

/-! ## Pointwise facts -/

theorem r14_c_R_poly_at_00_pos : 0 < r14_c_R_poly 0 0 := by native_decide
theorem r14_c_R_poly_at_10_pos : 0 < r14_c_R_poly 1 0 := by native_decide
theorem r14_c_R_poly_at_01_pos : 0 < r14_c_R_poly 0 1 := by native_decide
theorem r14_c_R_poly_at_11_pos : 0 < r14_c_R_poly 1 1 := by native_decide

/-- Branch-m R-poly > 0 on the unit box.
Lower bound: drop nonnegative `uv/10`, then `9 - 3/8 - 32/5 = 89/40 > 0`. -/
theorem r14_m_R_poly_pos_on_unit (u v : ℚ) (h : InUnitBox u v) :
    0 < r14_m_R_poly u v := by
  have ⟨hu0, hu1, hv0, hv1⟩ := h
  have hdrop : (0 : ℚ) ≤ u * v / 10 := by
    have : (0 : ℚ) ≤ u * v := mul_nonneg hu0 hv0
    nlinarith
  have hbound : r14_m_R_poly u v ≥ 9 - (3 : ℚ) / 8 - (32 : ℚ) / 5 := by
    simp only [r14_m_R_poly]
    nlinarith
  have hpos : (0 : ℚ) < 9 - (3 : ℚ) / 8 - (32 : ℚ) / 5 := by native_decide
  linarith

theorem r14_m_R_poly_pos_on_unit' :
    ∀ u v : ℚ, InUnitBox u v → 0 < r14_m_R_poly u v :=
  r14_m_R_poly_pos_on_unit

/-! ## Branch-m rectangle cover -/

def r14_m_paths : List String :=
  ["00", "0100", "0101", "0110", "0111", "10", "1100", "1101", "1110", "1111"]

def rectArea (loU hiU loV hiV : ℚ) : ℚ := (hiU - loU) * (hiV - loV)

def r14_m_cover_area : ℚ :=
  r14_m_paths.foldl
    (fun acc p =>
      let r := pathInterval p
      acc + rectArea r.1.1 r.1.2 r.2.1 r.2.2)
    0

theorem r14_m_cover_area_eq_one : r14_m_cover_area = 1 := by native_decide
theorem r14_m_paths_length : r14_m_paths.length = 10 := by native_decide

/-! ## Bernstein min tokens -/

def r14_c_R_bernsteinMin : ℚ := (19 : ℚ) / 125
theorem r14_c_R_bernsteinMin_pos : 0 < r14_c_R_bernsteinMin := r14_c_root_min_R_pos

def r14_c_P_bernsteinMin : ℚ := (290632 : ℚ) / 9765625
theorem r14_c_P_bernsteinMin_pos : 0 < r14_c_P_bernsteinMin := r14_c_root_min_P_pos

/-- OPEN: Bernstein-form ID of `r14_c_R_poly` ⇒ pointwise ≥ min on unit box. -/
def R14BranchC_R_PointwiseGeMin : Prop :=
  ∀ u v : ℚ, InUnitBox u v → r14_c_R_bernsteinMin ≤ r14_c_R_poly u v

def r14BranchC_R_PointwiseGeMinProved : Bool := false
theorem r14BranchC_R_PointwiseGeMinProved_false :
    r14BranchC_R_PointwiseGeMinProved = false := rfl

/-! ## SE2 package ↔ cover identification interface -/

def r14PackageChartParams (p : SE2FieldPackage BernsteinGeometryMap.leaf_R14) : ℚ × ℚ := (p.z, p.d)

theorem r14PackageChartParams_chord (p : SE2FieldPackage BernsteinGeometryMap.leaf_R14) :
    p.cfg.chart.leftRatio * p.cfg.chart.rightFactor = f p.z p.d :=
  se2FieldPackage_chart _ p

theorem closerModule_eq_R14_leaf (ℓ : NearLeaf) (h : closerModule ℓ = "R14") :
    ℓ = BernsteinGeometryMap.leaf_R14 := by
  revert h
  simp only [BernsteinGeometryMap.leaf_R14]
  rcases ℓ with ⟨rt, left, fh⟩
  cases rt <;> cases left <;> cases fh <;> intro h <;>
    first | rfl | (simp [closerModule] at h)

/-- Partial ID: `(u,v)` arises from package chart `z` via a branch `x(u)` CoV. -/
def R14UVFromPackage (p : SE2FieldPackage BernsteinGeometryMap.leaf_R14)
    (u v : ℚ) : Prop :=
  InUnitBox u v ∧
    (p.z = branchC_x u ∨ p.z = branchM_x u ∨ p.z = branchS_x u)

/-- OPEN: living R14 SE2 yields a CoV point where branch-c or branch-m R-poly ≤ 0. -/
def R14SE2ForcesSomeCMPolyNonpos : Prop :=
  ∀ p : SE2FieldPackage BernsteinGeometryMap.leaf_R14,
    ∃ u v : ℚ, R14UVFromPackage p u v ∧
      (r14_c_R_poly u v ≤ 0 ∨ r14_m_R_poly u v ≤ 0)

def r14SE2ForcesSomeCMPolyNonposProved : Bool := false
theorem r14SE2ForcesSomeCMPolyNonposProved_false :
    r14SE2ForcesSomeCMPolyNonposProved = false := rfl

/-- Full c∧m cover strict positivity (c half still open). -/
def R14CoverStrictPosCM : Prop :=
  (∀ u v : ℚ, InUnitBox u v → 0 < r14_c_R_poly u v) ∧
    (∀ u v : ℚ, InUnitBox u v → 0 < r14_m_R_poly u v)

def r14CoverStrictPosCMProved : Bool := false
theorem r14CoverStrictPosCMProved_false : r14CoverStrictPosCMProved = false := rfl

theorem r14_m_half_coverStrictPos :
    ∀ u v : ℚ, InUnitBox u v → 0 < r14_m_R_poly u v :=
  r14_m_R_poly_pos_on_unit'

/-- Partial positivity package actually inhabited. -/
def R14PartialPointwisePos : Prop :=
  (∀ u v : ℚ, InUnitBox u v → 0 < r14_m_R_poly u v) ∧
    0 < r14_c_R_poly 0 0 ∧ 0 < r14_c_R_poly 1 0 ∧
      0 < r14_c_R_poly 0 1 ∧ 0 < r14_c_R_poly 1 1 ∧
        0 < r14_c_R_bernsteinMin ∧ 0 < r14_c_P_bernsteinMin

theorem r14PartialPointwisePos : R14PartialPointwisePos :=
  ⟨r14_m_R_poly_pos_on_unit',
    r14_c_R_poly_at_00_pos, r14_c_R_poly_at_10_pos,
    r14_c_R_poly_at_01_pos, r14_c_R_poly_at_11_pos,
    r14_c_R_bernsteinMin_pos, r14_c_P_bernsteinMin_pos⟩

/-- Conditional: cover strict positivity + SE2⇒nonpos extraction ⇒ R14 package contradicts. -/
theorem se2PackageContradictsJCover_R14_of
    (hpos : R14CoverStrictPosCM)
    (hforce : R14SE2ForcesSomeCMPolyNonpos) :
    SE2PackageContradictsJCover "R14" := by
  intro ℓ hlab cfg
  have hℓ := closerModule_eq_R14_leaf ℓ hlab
  subst hℓ
  obtain ⟨u, v, ⟨hbox, _hz⟩, hnonpos⟩ := hforce ⟨cfg⟩
  cases hnonpos with
  | inl hc0 => exact (not_le_of_gt (hpos.1 u v hbox)) hc0
  | inr hm0 => exact (not_le_of_gt (hpos.2 u v hbox)) hm0

theorem bernsteinForcesRawEmpty_R14_of
    (hpos : R14CoverStrictPosCM)
    (hforce : R14SE2ForcesSomeCMPolyNonpos) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_of_package_contradicts _
    (se2PackageContradictsJCover_R14_of hpos hforce)

/-! ## Flags -/

def r14JPolyPartialProved : Bool := true
theorem r14JPolyPartialProved_true : r14JPolyPartialProved = true := rfl

def se2PackageContradictsJCoverProved : Bool := false
theorem se2PackageContradictsJCoverProved_false :
    se2PackageContradictsJCoverProved = false := rfl

def bernsteinForcesRawEmptyProved : Bool := false
theorem bernsteinForcesRawEmptyProved_false : bernsteinForcesRawEmptyProved = false := rfl

def blockedReason : String :=
  "Partial R14 J poly port CLOSED: pathInterval; h/n/R; branch CoV; c/m/s R-polys; \
   m R-poly >0 on unit box; m cover area=1; c corner samples + bernsteinMin tokens; \
   conditional package-contradicts. \
   FULL ID BLOCKED: c pointwise≥min (Bernstein-form); SE2⇒(u,v) with R-poly≤0; \
   P-polys unported."

def openStatus : String :=
  "CLOSED: CertR14JPoly partial port + conditional R14 raw-empty. \
   OPEN: R14CoverStrictPosCM (c half); R14SE2ForcesSomeCMPolyNonpos; \
   SE2PackageContradictsJCover; BernsteinForcesRawEmpty. \
   Not PrincipalClaim / namedClosersDischarged."

end S6.CertR14JPoly
