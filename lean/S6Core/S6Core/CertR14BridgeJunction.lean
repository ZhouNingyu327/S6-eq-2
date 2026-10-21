import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.BernsteinGeometryMap
import S6Core.CertJBoxIdentification
import S6Core.CertR14JPoly
import S6Core.CertR14JBernstein

/-!
# R14 bridge / junction constraints vs SE2 fields (partial Lean port)

Sources (read-only): `artifacts/ex/all/check_round14_bridge.py`,
`check_round14_junction.py`, `round14_*_checks.json`.

## Proved (honest)
* Weierstrass `cW`/`sW` bridge `K` and left-ray identities.
* Junction coordinate identity (`s₂X - c₂Y = s₂ + c₂ - 1`).
* SE2 for R14 excludes `JunctionConflict` / dual residual.
* SE2 left-gap ⇒ `dL > 1`; with `z ∈ (0,1)`, `leftRayBound z < dL`.
* Algebraic Z3 packs unsat: `LeftLengthHyps`, `ABridgeHyps`, `LeftGapOwnerHyps`.
* Conditionals: any of `R14SE2Realises{LeftLength,ABridge,LeftGapOwner}Pack` ⇒
  `R14SE2ForcesBridgeJunctionContradiction` / `BernsteinForcesRawEmpty "R14"`
  (**not** via R-poly ≤ 0; SE2 has no μ / W-bridge `(A,D,U,l)` fields).

## Inventory only
* Bridge/junction Z3 unsat scopes named; JSON holds solver results.

## Blocked
* `R14SE2Realises*Pack` (SE2 ⇒ W-bridge / ownership fields). No false ID invented.
* ∀cfg `z ∈ (0,1)` (chart alone does not force it).
* `R14SE2ForcesBridgeJunctionContradiction` / `BernsteinForcesRawEmpty` stay false.

Not PrincipalClaim / namedClosersDischarged. Bridge theorem files untouched.
-/

namespace S6.CertR14BridgeJunction

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.BernsteinGeometryMap
open S6.CertJBoxIdentification
open S6.CertR14JPoly
open S6.CertR14JBernstein

/-! ## Weierstrass (matches bridge script / Obligation4M8) -/

def cW (z : ℚ) : ℚ := (1 - z * z) / (1 + z * z)
def sW (z : ℚ) : ℚ := (2 * z) / (1 + z * z)
def leftRayBound (z : ℚ) : ℚ := (2 * z) / (1 + z)
def bridgeK (z : ℚ) : ℚ := (cW z + sW z - 1) / (cW z * sW z)

theorem cW_mul (z : ℚ) (_h : 1 + z * z ≠ 0) :
    cW z * (1 + z * z) = 1 - z * z := by
  simp only [cW]; field_simp

theorem sW_mul (z : ℚ) (_h : 1 + z * z ≠ 0) :
    sW z * (1 + z * z) = 2 * z := by
  simp only [sW]; field_simp

theorem one_sub_sq_ne (z : ℚ) (hz1 : z ≠ 1) (h1 : 1 + z ≠ 0) :
    1 - z * z ≠ 0 := by
  intro h
  have : z * z = 1 := by linarith
  have : z = 1 ∨ z = -1 := sq_eq_one_iff.mp (by simpa [pow_two] using this)
  cases this with
  | inl h' => exact hz1 h'
  | inr h' => exact h1 (by linarith)

theorem cW_add_sW_sub_one (z : ℚ) (h2 : 1 + z * z ≠ 0) :
    cW z + sW z - 1 = (2 * z * (1 - z)) / (1 + z * z) := by
  simp only [cW, sW]
  field_simp [h2]
  ring

theorem cW_mul_sW (z : ℚ) (h2 : 1 + z * z ≠ 0) :
    cW z * sW z = (1 - z * z) * (2 * z) / (1 + z * z) ^ 2 := by
  simp only [cW, sW]
  field_simp [h2]

/-- `K = (1+z²)/(1+z)` under standard nonzero dens. -/
theorem bridge_K_eq (z : ℚ) (h1 : 1 + z ≠ 0) (h2 : 1 + z * z ≠ 0)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    bridgeK z = (1 + z * z) / (1 + z) := by
  have h1z := sub_ne_zero.mpr hz1
  have h1z2 := one_sub_sq_ne z hz1 h1
  have hnum := cW_add_sW_sub_one z h2
  have hden := cW_mul_sW z h2
  have hden0 : cW z * sW z ≠ 0 := by
    rw [hden]
    refine div_ne_zero ?_ (pow_ne_zero 2 h2)
    exact mul_ne_zero h1z2 (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hz0)
  simp only [bridgeK]
  rw [hnum, hden]
  -- (2z(1-z)/(1+z²)) / (2z(1-z²)/(1+z²)²) = (1+z²)/(1+z)
  have hfac : 1 - z * z = (1 - z) * (1 + z) := by ring
  rw [hfac]
  field_simp [h2, h1, h1z, hz0]

/-- `1 - (1-s)/c = 2z/(1+z)`. -/
theorem bridge_left_ray_identity (z : ℚ) (h1 : 1 + z ≠ 0) (h2 : 1 + z * z ≠ 0)
    (hz1 : z ≠ 1) :
    1 - (1 - sW z) / cW z = leftRayBound z := by
  have h1z := sub_ne_zero.mpr hz1
  have h1z2 := one_sub_sq_ne z hz1 h1
  have hcz : cW z ≠ 0 := by
    intro h0
    have := cW_mul z h2
    simp only [h0, zero_mul] at this
    exact h1z2 (by linarith)
  -- 1 - (1-s)/c = (c - 1 + s)/c = (c+s-1)/c
  have hrewrite : 1 - (1 - sW z) / cW z = (cW z + sW z - 1) / cW z := by
    field_simp [hcz]
    ring
  rw [hrewrite, cW_add_sW_sub_one z h2]
  simp only [cW, leftRayBound]
  field_simp [h2, h1, h1z, hcz]
  -- goal reduces to z(1-z)(1+z)/(1-z²) = z
  have hpow : 1 - z ^ 2 = (1 - z) * (1 + z) := by ring
  simp only [hpow]
  field_simp [h1, h1z]

/-! ## Junction coordinate identity 2 -/

def junc_c (t : ℚ) : ℚ := (1 - t * t) / (1 + t * t)
def junc_s (t : ℚ) : ℚ := (2 * t) / (1 + t * t)
def junc_D (x y : ℚ) : ℚ := (x - y) * (1 + x * y)
def junc_Y (x y N : ℚ) : ℚ := 2 * x * y * (N - x - y) / junc_D x y
def junc_X (x y N : ℚ) : ℚ :=
  1 - x + y * (1 - x * x) * (N - x - y) / junc_D x y

theorem junction_coord_id_2 (x y N : ℚ)
    (hD : junc_D x y ≠ 0) (h2 : 1 + x * x ≠ 0) :
    junc_s x * junc_X x y N - junc_c x * junc_Y x y N
      = junc_s x + junc_c x - 1 := by
  simp only [junc_X, junc_Y, junc_D, junc_s, junc_c]
  have := hD
  have := h2
  field_simp
  ring

/-! ## SE2 conflict interface (not R-poly ≤ 0) -/

theorem r14_se2_excludes_junction
    (cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14) :
    ¬ JunctionConflict cfg.rays :=
  se2_excludes_junction _ cfg

theorem r14_se2_excludes_dual
    (cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14) :
    ¬ CloserDualResidual BernsteinGeometryMap.leaf_R14 cfg.rays :=
  se2_excludes_dualResidual _ cfg

theorem r14Package_leftRayBound
    (p : SE2FieldPackage BernsteinGeometryMap.leaf_R14)
    (h1 : 1 + p.z ≠ 0) (h2 : 1 + p.z * p.z ≠ 0) (hz1 : p.z ≠ 1) :
    1 - (1 - sW p.z) / cW p.z = leftRayBound p.z :=
  bridge_left_ray_identity p.z h1 h2 hz1

def R14BridgeJunctionIdentities : Prop :=
  (∀ z : ℚ, 1 + z ≠ 0 → 1 + z * z ≠ 0 → z ≠ 0 → z ≠ 1 →
      bridgeK z = (1 + z * z) / (1 + z)) ∧
    (∀ z : ℚ, 1 + z ≠ 0 → 1 + z * z ≠ 0 → z ≠ 1 →
      1 - (1 - sW z) / cW z = leftRayBound z) ∧
      (∀ x y N : ℚ, junc_D x y ≠ 0 → 1 + x * x ≠ 0 →
        junc_s x * junc_X x y N - junc_c x * junc_Y x y N
          = junc_s x + junc_c x - 1)

theorem r14BridgeJunctionIdentities : R14BridgeJunctionIdentities :=
  ⟨fun z h1 h2 hz0 hz1 => bridge_K_eq z h1 h2 hz0 hz1,
    fun z h1 h2 hz1 => bridge_left_ray_identity z h1 h2 hz1,
    fun x y N hD h2 => junction_coord_id_2 x y N hD h2⟩

/-! ## Partial SE2 ⇒ bridge left-ray comparison (leftLength scope fragment) -/

theorem r14_se2_left_gap
    (cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14) :
    cfg.leftRays.gapsL := by
  have h := cfg.left_ok
  simpa [LeftStatusMatches, BernsteinGeometryMap.leaf_R14] using h

theorem r14_se2_dL_gt_one
    (cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14) :
    1 < cfg.leftRays.dL :=
  (r14_se2_left_gap cfg).2

/-- For `z ∈ (0,1)`, `2z/(1+z) < 1`. -/
theorem leftRayBound_lt_one (z : ℚ) (hz0 : 0 < z) (hz1 : z < 1) :
    leftRayBound z < 1 := by
  simp only [leftRayBound]
  have hden : 0 < 1 + z := by linarith
  exact (div_lt_one hden).mpr (by linarith)

/-- SE2 left-gap + chart `z ∈ (0,1)` ⇒ `leftRayBound z < dL`
(one side of the bridge `leftLength` Z3 scope). -/
theorem r14_se2_leftRayBound_lt_dL
    (cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14)
    (hz0 : 0 < cfg.z) (hz1 : cfg.z < 1) :
    leftRayBound cfg.z < cfg.leftRays.dL := by
  have hgt1 := r14_se2_dL_gt_one cfg
  have hbound := leftRayBound_lt_one cfg.z hz0 hz1
  linarith

theorem left_ray_squeeze_false (z dL : ℚ)
    (hlt : leftRayBound z < dL) (hle : dL ≤ leftRayBound z) : False := by
  linarith

/-- BLOCKED / false-shaped if read as Z3 `left_length`: SE2 `dL` (gap, `>1`)
is not Z3 `l`. Under `z∈(0,1)` SE2 already gives `leftRayBound < dL`, so
`dL ≤ leftRayBound` cannot hold for inhabited SE2. Residual is
`R14SE2RealisesLeftLengthPack` instead. -/
def R14SE2ForcesLeftRayLeBound : Prop :=
  ∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    0 < cfg.z → cfg.z < 1 → cfg.leftRays.dL ≤ leftRayBound cfg.z

def r14SE2ForcesLeftRayLeBoundProved : Bool := false
theorem r14SE2ForcesLeftRayLeBoundProved_false :
    r14SE2ForcesLeftRayLeBoundProved = false := rfl

/-- OPEN: living R14 SE2 realises a bridge/junction hypothesis package that the
external Z3 scopes show unsatisfiable. **Not** an R-poly ≤ 0 claim. -/
def R14SE2ForcesBridgeJunctionContradiction : Prop :=
  ∀ _cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14, False

theorem bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (H : R14SE2ForcesBridgeJunctionContradiction) :
    BernsteinForcesRawEmpty "R14" :=
  fun _hc ℓ hlab => by
    have hℓ := closerModule_eq_R14_leaf ℓ hlab
    subst hℓ
    intro ⟨cfg⟩
    exact H cfg

theorem bernsteinForcesRawEmpty_R14_of_cover_and_bridge
    (_hpos : R14CoverStrictPosCM)
    (H : R14SE2ForcesBridgeJunctionContradiction) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction H

theorem bernsteinForcesRawEmpty_R14_of_leftRayLeBound
    (hz : ∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14, 0 < cfg.z ∧ cfg.z < 1)
    (H : R14SE2ForcesLeftRayLeBound) :
    BernsteinForcesRawEmpty "R14" := by
  intro _hc ℓ hlab
  have hℓ := closerModule_eq_R14_leaf ℓ hlab
  subst hℓ
  intro ⟨cfg⟩
  have ⟨hz0, hz1⟩ := hz cfg
  exact left_ray_squeeze_false cfg.z cfg.leftRays.dL
    (r14_se2_leftRayBound_lt_dL cfg hz0 hz1) (H cfg hz0 hz1)

theorem r14SE2ForcesBridgeJunctionContradiction_of_leftRayLeBound
    (hz : ∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14, 0 < cfg.z ∧ cfg.z < 1)
    (H : R14SE2ForcesLeftRayLeBound) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  have ⟨hz0, hz1⟩ := hz cfg
  exact left_ray_squeeze_false cfg.z cfg.leftRays.dL
    (r14_se2_leftRayBound_lt_dL cfg hz0 hz1) (H cfg hz0 hz1)

/-! ## Algebraic Z3 leftLength unsat (not SE2.dL) -/

/-- Bridge script `left_length`: `μ>1`, `z∈(0,1)`, Weierstrass `(cW,sW)`,
W-endpoint `c·l ≥ μ·c-1+μ·s`, and `l ≤ 2z/(1+z)`.
Z3 `l` is C's left-ray length under W — **not** SE2 `leftRays.dL`. -/
structure LeftLengthHyps (μ z l : ℚ) : Prop where
  hμ : 1 < μ
  hz0 : 0 < z
  hz1 : z < 1
  hw : cW z * l ≥ μ * cW z - 1 + μ * sW z
  hle : l * (1 + z) ≤ 2 * z

theorem cW_pos_of_mem_unit (z : ℚ) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < cW z := by
  simp only [cW]
  have hnum : 0 < 1 - z * z := by nlinarith
  have hden : 0 < 1 + z * z := by nlinarith
  exact div_pos hnum hden

theorem zSq_sub_two_z_sub_one_neg (z : ℚ) (hz0 : 0 < z) (hz1 : z < 1) :
    z * z - 2 * z - 1 < 0 := by
  nlinarith

/-- Cleared form of `W-lower − leftRayBound`:
`(μ(c+s)-1)(1+z) - 2z·c = -(μ-1)(z+1)(z²-2z-1)/(1+z²)`. -/
theorem w_lower_minus_bound_cleared (μ z : ℚ)
    (_h2 : 1 + z * z ≠ 0) :
    (μ * (cW z + sW z) - 1) * (1 + z) - 2 * z * cW z
      = -((μ - 1) * (z + 1) * (z * z - 2 * z - 1)) / (1 + z * z) := by
  simp only [cW, sW]
  field_simp [_h2]
  ring

theorem w_endpoint_lower_gt_leftRayBound (μ z : ℚ)
    (hμ : 1 < μ) (hz0 : 0 < z) (hz1 : z < 1) :
    leftRayBound z < (μ * (cW z + sW z) - 1) / cW z := by
  have hc := cW_pos_of_mem_unit z hz0 hz1
  have hden : 0 < 1 + z := by linarith
  have h2pos : 0 < 1 + z * z := by nlinarith
  have h2 : 1 + z * z ≠ 0 := ne_of_gt h2pos
  have hcleared := w_lower_minus_bound_cleared μ z h2
  have hneg := zSq_sub_two_z_sub_one_neg z hz0 hz1
  have hμ0 : 0 < μ - 1 := by linarith
  have hzp : 0 < z + 1 := by linarith
  have hfac : 0 < (μ - 1) * (z + 1) := mul_pos hμ0 hzp
  have hprod : (μ - 1) * (z + 1) * (z * z - 2 * z - 1) < 0 :=
    mul_neg_of_pos_of_neg hfac hneg
  have hnum : 0 < -((μ - 1) * (z + 1) * (z * z - 2 * z - 1)) :=
    neg_pos.mpr hprod
  have hcleared_pos :
      0 < (μ * (cW z + sW z) - 1) * (1 + z) - 2 * z * cW z := by
    rw [hcleared]
    exact div_pos hnum h2pos
  have hstep :
      2 * z * cW z < (μ * (cW z + sW z) - 1) * (1 + z) := by linarith
  simp only [leftRayBound]
  exact (div_lt_div_iff₀ hden hc).mpr (by linarith [hstep])

theorem leftLengthHyps_false (μ z l : ℚ) (H : LeftLengthHyps μ z l) : False := by
  have hc := cW_pos_of_mem_unit z H.hz0 H.hz1
  have hden : 0 < 1 + z := by linarith [H.hz0]
  have hle : l ≤ leftRayBound z := by
    simp only [leftRayBound]
    exact (le_div_iff₀ hden).mpr H.hle
  have hw' : (μ * (cW z + sW z) - 1) / cW z ≤ l := by
    have : μ * (cW z + sW z) - 1 ≤ l * cW z := by
      have := H.hw
      linarith
    exact (div_le_iff₀ hc).mpr this
  have hgt := w_endpoint_lower_gt_leftRayBound μ z H.hμ H.hz0 H.hz1
  linarith

def R14LeftLengthPackUnsat : Prop :=
  ∀ μ z l : ℚ, LeftLengthHyps μ z l → False

theorem r14LeftLengthPackUnsat : R14LeftLengthPackUnsat :=
  leftLengthHyps_false

def r14LeftLengthPackUnsatProved : Bool := true
theorem r14LeftLengthPackUnsatProved_true : r14LeftLengthPackUnsatProved = true := rfl

/-- OPEN: living R14 SE2 realises W-bridge `(μ,l)` matching Z3 `left_length`
(with chart `z`). **Not** `dL ≤ leftRayBound` — `dL` ≠ Z3 `l`. -/
def R14SE2RealisesLeftLengthPack : Prop :=
  ∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    ∃ μ l : ℚ, LeftLengthHyps μ cfg.z l

def r14SE2RealisesLeftLengthPackProved : Bool := false
theorem r14SE2RealisesLeftLengthPackProved_false :
    r14SE2RealisesLeftLengthPackProved = false := rfl

theorem r14SE2ForcesBridgeJunctionContradiction_of_leftLengthPack
    (H : R14SE2RealisesLeftLengthPack) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  obtain ⟨μ, l, h⟩ := H cfg
  exact leftLengthHyps_false μ cfg.z l h

theorem bernsteinForcesRawEmpty_R14_of_leftLengthPack
    (H : R14SE2RealisesLeftLengthPack) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (r14SE2ForcesBridgeJunctionContradiction_of_leftLengthPack H)

/-! ## Algebraic Z3 ABridge unsat -/

/-- Bridge script `A_bridge`: `μ>1`, `c,s>0`, `s·z=1-c`, plane `s·A+c·D=1`,
W-halfplane `c(μ-D)≤s·U`, tip `A≥z+U`. -/
structure ABridgeHyps (μ c s z A D U : ℚ) : Prop where
  hμ : 1 < μ
  hc : 0 < c
  hs : 0 < s
  hsz : s * z = 1 - c
  hplane : s * A + c * D = 1
  hWU : c * (μ - D) ≤ s * U
  hA : z + U ≤ A

theorem aBridgeHyps_false (μ c s z A D U : ℚ) (H : ABridgeHyps μ c s z A D U) :
    False := by
  -- Cleared: s·A = 1 - c·D ≥ s·(z+U) = s·z + s·U ≥ s·z + c·(μ-D)
  have hplane' : s * A = 1 - c * D := by linarith [H.hplane]
  have hsA : s * (z + U) ≤ s * A := by
    exact mul_le_mul_of_nonneg_left H.hA (le_of_lt H.hs)
  have hsU : c * (μ - D) ≤ s * U := H.hWU
  have hcleared : s * z + c * (μ - D) ≤ 1 - c * D := by
    linarith [hplane', hsA, hsU]
  have hmain : s * z + μ * c ≤ 1 := by linarith
  have hc' : c = 1 - s * z := by linarith [H.hsz]
  have hsubst : s * z + μ * (1 - s * z) ≤ 1 := by simpa [hc'] using hmain
  have hμpos : 0 < μ - 1 := by linarith [H.hμ]
  have hle : μ - 1 ≤ (μ - 1) * (s * z) := by linarith [hsubst]
  have hsz_ge : 1 ≤ s * z := (le_mul_iff_one_le_right hμpos).mp hle
  have hsz_lt : s * z < 1 := by
    have : s * z = 1 - c := H.hsz
    linarith [H.hc]
  linarith

def R14ABridgePackUnsat : Prop :=
  ∀ μ c s z A D U : ℚ, ABridgeHyps μ c s z A D U → False

theorem r14ABridgePackUnsat : R14ABridgePackUnsat := aBridgeHyps_false

def r14ABridgePackUnsatProved : Bool := true
theorem r14ABridgePackUnsatProved_true : r14ABridgePackUnsatProved = true := rfl

/-- OPEN: SE2 realises ABridge fields. NearEndSE2 has no `(μ,c,s,A,D,U)`. -/
def R14SE2RealisesABridgePack : Prop :=
  ∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    ∃ μ c s A D U : ℚ, ABridgeHyps μ c s cfg.z A D U

def r14SE2RealisesABridgePackProved : Bool := false
theorem r14SE2RealisesABridgePackProved_false :
    r14SE2RealisesABridgePackProved = false := rfl

theorem r14SE2ForcesBridgeJunctionContradiction_of_aBridgePack
    (H : R14SE2RealisesABridgePack) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  obtain ⟨μ, c, s, A, D, U, h⟩ := H cfg
  exact aBridgeHyps_false μ c s cfg.z A D U h

theorem bernsteinForcesRawEmpty_R14_of_aBridgePack
    (H : R14SE2RealisesABridgePack) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (r14SE2ForcesBridgeJunctionContradiction_of_aBridgePack H)

/-! ## Algebraic Z3 leftGapOwner unsat -/

/-- Bridge script `left_gap_owner`: `μ>1`, `x+y<1`, `r≥μ-x`, `u≥μ-y`, `r+u<1`. -/
structure LeftGapOwnerHyps (μ x y r u : ℚ) : Prop where
  hμ : 1 < μ
  hxy : x + y < 1
  hr : μ - x ≤ r
  hu : μ - y ≤ u
  hru : r + u < 1

theorem leftGapOwnerHyps_false (μ x y r u : ℚ)
    (H : LeftGapOwnerHyps μ x y r u) : False := by
  have hsum : 2 * μ - (x + y) ≤ r + u := by linarith [H.hr, H.hu]
  have hgt : 1 < 2 * μ - (x + y) := by linarith [H.hμ, H.hxy]
  linarith [H.hru]

def R14LeftGapOwnerPackUnsat : Prop :=
  ∀ μ x y r u : ℚ, LeftGapOwnerHyps μ x y r u → False

theorem r14LeftGapOwnerPackUnsat : R14LeftGapOwnerPackUnsat :=
  leftGapOwnerHyps_false

def r14LeftGapOwnerPackUnsatProved : Bool := true
theorem r14LeftGapOwnerPackUnsatProved_true :
    r14LeftGapOwnerPackUnsatProved = true := rfl

/-- OPEN: SE2 realises left-gap-owner fields `(μ,x,y,r,u)`. -/
def R14SE2RealisesLeftGapOwnerPack : Prop :=
  ∀ _cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    ∃ μ x y r u : ℚ, LeftGapOwnerHyps μ x y r u

def r14SE2RealisesLeftGapOwnerPackProved : Bool := false
theorem r14SE2RealisesLeftGapOwnerPackProved_false :
    r14SE2RealisesLeftGapOwnerPackProved = false := rfl

theorem r14SE2ForcesBridgeJunctionContradiction_of_leftGapOwnerPack
    (H : R14SE2RealisesLeftGapOwnerPack) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  obtain ⟨μ, x, y, r, u, h⟩ := H cfg
  exact leftGapOwnerHyps_false μ x y r u h

theorem bernsteinForcesRawEmpty_R14_of_leftGapOwnerPack
    (H : R14SE2RealisesLeftGapOwnerPack) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (r14SE2ForcesBridgeJunctionContradiction_of_leftGapOwnerPack H)

/-! ## Z3 scope inventory (names only) -/

inductive R14BridgeUnsatScope
  | noLeftTip
  | ABridge
  | leftLength
  | JCondition
  | angleBudget
  | leftGapOwner
  deriving DecidableEq, Repr

inductive R14JunctionUnsatScope
  | angleOrder
  | sumBudget
  | muGeometry
  | reducedHull
  deriving DecidableEq, Repr

def r14BridgeUnsatScopeCount : ℕ := 6
theorem r14BridgeUnsatScopeCount_eq : r14BridgeUnsatScopeCount = 6 := rfl

def r14JunctionUnsatScopeCount : ℕ := 4
theorem r14JunctionUnsatScopeCount_eq : r14JunctionUnsatScopeCount = 4 := rfl

def r14BridgeJunctionIdentitiesProved : Bool := true
theorem r14BridgeJunctionIdentitiesProved_true :
    r14BridgeJunctionIdentitiesProved = true := rfl

def r14SE2ForcesBridgeJunctionContradictionProved : Bool := false
theorem r14SE2ForcesBridgeJunctionContradictionProved_false :
    r14SE2ForcesBridgeJunctionContradictionProved = false := rfl

def bernsteinForcesRawEmptyProved : Bool := false
theorem bernsteinForcesRawEmptyProved_false : bernsteinForcesRawEmptyProved = false := rfl

def rawSE2EmptyProved : Bool := false
theorem rawSE2EmptyProved_false : rawSE2EmptyProved = false := rfl

def blockedReason : String :=
  "CLOSED: identities; dL fragment; LeftLength/ABridge/LeftGapOwner algebraic unsat. \
   BLOCKED: SE2⇒any W-bridge/ownership pack (NearEndSE2 has no μ/(A,D,U,l)); \
   ForcesBridgeJunction. Not R-poly≤0."

def openStatus : String :=
  "CLOSED: LeftLength+ABridge+LeftGapOwner pack unsat. \
   OPEN: SE2⇒packs; ForcesBridgeJunction; BernsteinForcesRawEmpty. \
   Not PrincipalClaim / namedClosersDischarged."

end S6.CertR14BridgeJunction
