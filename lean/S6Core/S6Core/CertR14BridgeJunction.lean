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
* Algebraic Z3 packs unsat: `LeftLengthHyps`, `ABridgeHyps`, `LeftGapOwnerHyps`,
  `JConditionHyps`, `SumBudgetHyps`, `NoLeftTipHyps`, `AngleOrderHyps`.
* Extended living packages `NearEndR14With*` empty (SE2 + pack hyps ⇒ False)
  without claiming plain SE2 implies the pack fields.
* Conditionals: `R14SE2Realises*Pack` ⇒ ForcesBridgeJunction / raw-empty
  (**not** via R-poly ≤ 0).

## Inventory only
* Bridge/junction Z3 unsat scopes named; JSON holds solver results.

## Blocked
* `R14SE2Realises*Pack` (plain SE2 ⇒ pack fields). No false ID invented.
* ∀cfg `z ∈ (0,1)`; `R14SE2ForcesBridgeJunctionContradiction` stay false.

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

/-! ## Algebraic Z3 J_condition unsat -/

/-- Bridge script `J_condition`: Weierstrass `(cW,sW)`, W-halfplane,
`2U≤(1-z)²`, `K·c·s=c+s-μ`, `K>D`. -/
structure JConditionHyps (μ z D U K : ℚ) : Prop where
  hμ : 1 < μ
  hz0 : 0 < z
  hz1 : z < 1
  hWU : cW z * (μ - D) ≤ sW z * U
  hU0 : 0 ≤ U
  hU2 : 2 * U ≤ (1 - z) * (1 - z)
  hK : K * cW z * sW z = cW z + sW z - μ
  hKD : D < K

theorem j_poly_pos_of_mem_unit (z : ℚ) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < z ^ 4 - 2 * z ^ 3 + 2 * z ^ 2 + 2 * z + 1 := by
  have heq : z ^ 4 - 2 * z ^ 3 + 2 * z ^ 2 + 2 * z + 1
      = z * z * (z - 1) * (z - 1) + (z + 1) * (z + 1) := by ring
  rw [heq]
  have h1 : 0 ≤ z * z * (z - 1) * (z - 1) := by
    have : 0 ≤ (z * (z - 1)) ^ 2 := sq_nonneg _
    convert this using 1; ring
  have h2 : 0 < (z + 1) * (z + 1) := by nlinarith
  linarith

theorem sW_pos_of_mem_unit (z : ℚ) (hz0 : 0 < z) (_hz1 : z < 1) :
    0 < sW z := by
  simp only [sW]
  exact div_pos (by linarith) (by nlinarith : 0 < 1 + z * z)

theorem cW_sW_mul_pos_of_mem_unit (z : ℚ) (hz0 : 0 < z) (hz1 : z < 1) :
    0 < cW z * sW z :=
  mul_pos (cW_pos_of_mem_unit z hz0 hz1) (sW_pos_of_mem_unit z hz0 hz1)

/-- `D ≥ μ - z(1-z)/(1+z)` from W-halfplane + `2U≤(1-z)²`. -/
theorem j_condition_D_lower (μ z D U : ℚ)
    (hz0 : 0 < z) (hz1 : z < 1)
    (hWU : cW z * (μ - D) ≤ sW z * U)
    (hU2 : 2 * U ≤ (1 - z) * (1 - z)) :
    μ - z * (1 - z) / (1 + z) ≤ D := by
  have hc := cW_pos_of_mem_unit z hz0 hz1
  have hs := sW_pos_of_mem_unit z hz0 hz1
  have hden : 0 < 1 + z := by linarith
  have h2pos : 0 < 1 + z * z := by nlinarith
  have h2 : 1 + z * z ≠ 0 := ne_of_gt h2pos
  have hcW := cW_mul z h2
  have hsW := sW_mul z h2
  have hU : U ≤ (1 - z) * (1 - z) / 2 :=
    (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr (by linarith)
  have hstep : cW z * (μ - D) ≤ sW z * ((1 - z) * (1 - z) / 2) := by
    have : sW z * U ≤ sW z * ((1 - z) * (1 - z) / 2) :=
      mul_le_mul_of_nonneg_left hU (le_of_lt hs)
    linarith
  -- Cleared form of μ-D ≤ z(1-z)/(1+z)
  have hcleared : (μ - D) * (1 + z) ≤ z * (1 - z) := by
    have hfac : 0 ≤ (1 + z) * (1 + z * z) :=
      mul_nonneg (le_of_lt hden) (le_of_lt h2pos)
    have hmul :
        cW z * (μ - D) * ((1 + z) * (1 + z * z))
          ≤ sW z * ((1 - z) * (1 - z) / 2) * ((1 + z) * (1 + z * z)) :=
      mul_le_mul_of_nonneg_right hstep hfac
    have hL :
        cW z * (μ - D) * ((1 + z) * (1 + z * z))
          ≤ z * (1 - z) * (1 - z) * (1 + z) := by
      calc
        cW z * (μ - D) * ((1 + z) * (1 + z * z))
            ≤ sW z * ((1 - z) * (1 - z) / 2) * ((1 + z) * (1 + z * z)) := hmul
        _ = (sW z * (1 + z * z)) * ((1 - z) * (1 - z) / 2) * (1 + z) := by ring
        _ = (2 * z) * ((1 - z) * (1 - z) / 2) * (1 + z) := by rw [hsW]
        _ = z * (1 - z) * (1 - z) * (1 + z) := by ring
    have hR :
        z * (1 - z) * (cW z * (1 + z * z))
          = z * (1 - z) * (1 - z) * (1 + z) := by
      rw [hcW]; ring
    have hcancel :
        (μ - D) * (1 + z) * (cW z * (1 + z * z))
          ≤ z * (1 - z) * (cW z * (1 + z * z)) := by
      calc
        (μ - D) * (1 + z) * (cW z * (1 + z * z))
            = cW z * (μ - D) * ((1 + z) * (1 + z * z)) := by ring
        _ ≤ z * (1 - z) * (1 - z) * (1 + z) := hL
        _ = z * (1 - z) * (cW z * (1 + z * z)) := by rw [← hR]
    have hpos : 0 < cW z * (1 + z * z) := mul_pos hc h2pos
    exact (mul_le_mul_iff_of_pos_right hpos).mp hcancel
  have : μ - D ≤ z * (1 - z) / (1 + z) :=
    (le_div_iff₀ hden).mpr hcleared
  linarith

theorem j_K_lt_D_lower (μ z : ℚ) (hμ : 1 < μ) (hz0 : 0 < z) (hz1 : z < 1) :
    (cW z + sW z - μ) / (cW z * sW z) < μ - z * (1 - z) / (1 + z) := by
  have hcs := cW_sW_mul_pos_of_mem_unit z hz0 hz1
  have hden : 0 < 1 + z := by linarith
  have h2pos : 0 < 1 + z * z := by nlinarith
  have h2 : 1 + z * z ≠ 0 := ne_of_gt h2pos
  have hpoly := j_poly_pos_of_mem_unit z hz0 hz1
  have hμ0 : 0 < μ - 1 := by linarith
  have hdiff :
      (μ - z * (1 - z) / (1 + z)) * (cW z * sW z) - (cW z + sW z - μ)
        = (μ - 1) * (z ^ 4 - 2 * z ^ 3 + 2 * z ^ 2 + 2 * z + 1)
          / (1 + z * z) ^ 2 := by
    simp only [cW, sW]
    field_simp [h2, hden]
    ring
  have hpos : 0 <
      (μ - 1) * (z ^ 4 - 2 * z ^ 3 + 2 * z ^ 2 + 2 * z + 1) / (1 + z * z) ^ 2 :=
    div_pos (mul_pos hμ0 hpoly) (pow_pos h2pos 2)
  have hmul : cW z + sW z - μ <
      (μ - z * (1 - z) / (1 + z)) * (cW z * sW z) := by
    linarith [hdiff, hpos]
  exact (div_lt_iff₀ hcs).mpr hmul

theorem jConditionHyps_false (μ z D U K : ℚ) (H : JConditionHyps μ z D U K) :
    False := by
  have hcs := cW_sW_mul_pos_of_mem_unit z H.hz0 H.hz1
  have hD := j_condition_D_lower μ z D U H.hz0 H.hz1 H.hWU H.hU2
  have hKeq : K = (cW z + sW z - μ) / (cW z * sW z) := by
    refine (eq_div_iff (ne_of_gt hcs)).mpr ?_
    have := H.hK
    -- H.hK : (K * cW z) * sW z = cW + sW - μ
    simpa [mul_assoc] using this
  have hlt := j_K_lt_D_lower μ z H.hμ H.hz0 H.hz1
  linarith [H.hKD, hD, hKeq, hlt]

def R14JConditionPackUnsat : Prop :=
  ∀ μ z D U K : ℚ, JConditionHyps μ z D U K → False

theorem r14JConditionPackUnsat : R14JConditionPackUnsat := jConditionHyps_false

def r14JConditionPackUnsatProved : Bool := true
theorem r14JConditionPackUnsatProved_true : r14JConditionPackUnsatProved = true := rfl

def R14SE2RealisesJConditionPack : Prop :=
  ∀ cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    ∃ μ D U K : ℚ, JConditionHyps μ cfg.z D U K

def r14SE2RealisesJConditionPackProved : Bool := false
theorem r14SE2RealisesJConditionPackProved_false :
    r14SE2RealisesJConditionPackProved = false := rfl

theorem r14SE2ForcesBridgeJunctionContradiction_of_jConditionPack
    (H : R14SE2RealisesJConditionPack) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  obtain ⟨μ, D, U, K, h⟩ := H cfg
  exact jConditionHyps_false μ cfg.z D U K h

theorem bernsteinForcesRawEmpty_R14_of_jConditionPack
    (H : R14SE2RealisesJConditionPack) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (r14SE2ForcesBridgeJunctionContradiction_of_jConditionPack H)

/-! ## Algebraic Z3 junction sumBudget unsat -/

/-- Junction script `check_sum`: `N+S+x+2y-y²≤2` with `N≥1`, `S≥0`, `x+y≥1`. -/
structure SumBudgetHyps (x y N S : ℚ) : Prop where
  hx0 : 0 < x
  hx1 : x < 1
  hy0 : 0 < y
  hy1 : y < 1
  hN : 1 ≤ N
  hS : 0 ≤ S
  hbud : N + S + x + 2 * y - y * y ≤ 2
  hxy : 1 ≤ x + y

theorem sumBudgetHyps_false (x y N S : ℚ) (H : SumBudgetHyps x y N S) : False := by
  have hy01 : 0 < y * (1 - y) := mul_pos H.hy0 (by linarith [H.hy1])
  have hge : 2 + y * (1 - y) ≤ N + S + x + 2 * y - y * y := by
    -- 1+x+2y-y² = 1+x+y+y(1-y) ≥ 2+y(1-y)
    have : 1 + x + 2 * y - y * y = 1 + x + y + y * (1 - y) := by ring
    have : 2 + y * (1 - y) ≤ 1 + x + 2 * y - y * y := by
      rw [this]; linarith [H.hxy]
    linarith [H.hN, H.hS]
  linarith [H.hbud, hy01]

def R14SumBudgetPackUnsat : Prop :=
  ∀ x y N S : ℚ, SumBudgetHyps x y N S → False

theorem r14SumBudgetPackUnsat : R14SumBudgetPackUnsat := sumBudgetHyps_false

def r14SumBudgetPackUnsatProved : Bool := true
theorem r14SumBudgetPackUnsatProved_true : r14SumBudgetPackUnsatProved = true := rfl

def R14SE2RealisesSumBudgetPack : Prop :=
  ∀ _cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    ∃ x y N S : ℚ, SumBudgetHyps x y N S

def r14SE2RealisesSumBudgetPackProved : Bool := false
theorem r14SE2RealisesSumBudgetPackProved_false :
    r14SE2RealisesSumBudgetPackProved = false := rfl

theorem r14SE2ForcesBridgeJunctionContradiction_of_sumBudgetPack
    (H : R14SE2RealisesSumBudgetPack) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  obtain ⟨x, y, N, S, h⟩ := H cfg
  exact sumBudgetHyps_false x y N S h

theorem bernsteinForcesRawEmpty_R14_of_sumBudgetPack
    (H : R14SE2RealisesSumBudgetPack) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (r14SE2ForcesBridgeJunctionContradiction_of_sumBudgetPack H)

/-! ## Algebraic Z3 bridge noLeftTip unsat -/

/-- Bridge script `no_left_tip`: C cannot contain the left anchored inner tip. -/
structure NoLeftTipHyps (x k w S l r u : ℚ) : Prop where
  hx0 : 0 < x
  hx1 : x < 1
  hk0 : 0 < k
  hk1 : k < (4 : ℚ) / 15
  hw : 0 ≤ w
  hS : 0 ≤ S
  hgap : 0 < 1 - S - x - 2 * k + k * k - w
  hl : 1 - w ≤ l
  hr : 1 - x ≤ r
  hu : 1 - k ≤ u
  hsum : l + r + u * u ≤ 2

theorem noLeftTipHyps_false (x k w S l r u : ℚ) (H : NoLeftTipHyps x k w S l r u) :
    False := by
  have hklt1 : k < 1 := lt_trans H.hk1 (by norm_num)
  have h1k : 0 ≤ 1 - k := by linarith
  have hu0 : 0 ≤ u := le_trans h1k H.hu
  have hu2 : (1 - k) * (1 - k) ≤ u * u := by nlinarith [H.hu, hu0]
  have hw_ge : 1 - x - 2 * k + k * k ≤ w := by
    have hle :
        (1 - w) + (1 - x) + (1 - k) * (1 - k) ≤ l + r + u * u := by
      nlinarith [H.hl, H.hr, hu2]
    have : (1 - w) + (1 - x) + (1 - k) * (1 - k) ≤ 2 :=
      le_trans hle H.hsum
    nlinarith
  have hw_lt : w < 1 - x - 2 * k + k * k := by
    have : w < 1 - S - x - 2 * k + k * k := by linarith [H.hgap]
    linarith [H.hS]
  exact (not_le_of_gt hw_lt) hw_ge

def R14NoLeftTipPackUnsat : Prop :=
  ∀ x k w S l r u : ℚ, NoLeftTipHyps x k w S l r u → False

theorem r14NoLeftTipPackUnsat : R14NoLeftTipPackUnsat := noLeftTipHyps_false

def r14NoLeftTipPackUnsatProved : Bool := true
theorem r14NoLeftTipPackUnsatProved_true : r14NoLeftTipPackUnsatProved = true := rfl

def R14SE2RealisesNoLeftTipPack : Prop :=
  ∀ _cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    ∃ x k w S l r u : ℚ, NoLeftTipHyps x k w S l r u

def r14SE2RealisesNoLeftTipPackProved : Bool := false
theorem r14SE2RealisesNoLeftTipPackProved_false :
    r14SE2RealisesNoLeftTipPackProved = false := rfl

theorem r14SE2ForcesBridgeJunctionContradiction_of_noLeftTipPack
    (H : R14SE2RealisesNoLeftTipPack) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  obtain ⟨x, k, w, S, l, r, u, h⟩ := H cfg
  exact noLeftTipHyps_false x k w S l r u h

theorem bernsteinForcesRawEmpty_R14_of_noLeftTipPack
    (H : R14SE2RealisesNoLeftTipPack) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (r14SE2ForcesBridgeJunctionContradiction_of_noLeftTipPack H)

/-! ## Algebraic Z3 junction angleOrder unsat -/

/-- Junction script `check_angle_order`: right-adjacent meeting forces `t₃ < t₂`
(`y ≥ x` is unsat under the tan/budget hyps). -/
structure AngleOrderHyps (x y L N T : ℚ) : Prop where
  hx0 : 0 < x
  hx1 : x < 1
  hy0 : 0 < y
  hy1 : y < 1
  hL : 1 ≤ L
  hN : 1 ≤ N
  hLcos : L * (1 - x * x) ≤ 1 + x * x
  hLsin : 2 * x * L ≤ 1 + x * x
  hTeq : T * (1 - y * y) = 1 + y * y - 2 * y * N
  hT0 : 0 ≤ T
  hLT : 2 ≤ L + T
  hyx : x ≤ y

private theorem angleOrder_T_le (y N T : ℚ)
    (hy0 : 0 < y) (hy1 : y < 1) (hN : 1 ≤ N)
    (hTeq : T * (1 - y * y) = 1 + y * y - 2 * y * N) (_hT0 : 0 ≤ T) :
    T ≤ (1 - y) / (1 + y) := by
  have hypos : 0 < 1 - y := by linarith
  have h1y : (0 : ℚ) < 1 + y := by linarith
  have h1y2 : 0 < 1 - y * y := by nlinarith
  have hNy : 2 * y ≤ 2 * y * N := by nlinarith [hN, hy0]
  have hnum : 1 + y * y - 2 * y * N ≤ (1 - y) * (1 - y) := by
    have : 1 + y * y - 2 * y = (1 - y) * (1 - y) := by ring
    linarith
  have hmul : T * (1 - y * y) ≤ (1 - y) * (1 - y) := by
    rw [hTeq]; exact hnum
  have hdiv : T ≤ (1 - y) * (1 - y) / (1 - y * y) :=
    (le_div_iff₀ h1y2).mpr (by nlinarith [hmul])
  have hsimp : (1 - y) * (1 - y) / (1 - y * y) = (1 - y) / (1 + y) := by
    have hfac : 1 - y * y = (1 - y) * (1 + y) := by ring
    rw [hfac]
    field_simp [ne_of_gt hypos, ne_of_gt h1y]
  rwa [hsimp] at hdiv

private theorem angleOrder_L_ge (x y L N T : ℚ) (H : AngleOrderHyps x y L N T) :
    (1 + 3 * x) / (1 + x) ≤ L := by
  have hTle := angleOrder_T_le y N T H.hy0 H.hy1 H.hN H.hTeq H.hT0
  have hLge : 2 - (1 - y) / (1 + y) ≤ L := by linarith [H.hLT, hTle]
  have hrew : 2 - (1 - y) / (1 + y) = (1 + 3 * y) / (1 + y) := by
    have h1y : (0 : ℚ) < 1 + y := by linarith [H.hy0]
    field_simp [ne_of_gt h1y]
    ring
  have hLge' : (1 + 3 * y) / (1 + y) ≤ L := by rwa [← hrew]
  have hmono : (1 + 3 * x) / (1 + x) ≤ (1 + 3 * y) / (1 + y) := by
    have hx1 : (0 : ℚ) < 1 + x := by linarith [H.hx0]
    have hy1 : (0 : ℚ) < 1 + y := by linarith [H.hy0]
    rw [div_le_div_iff₀ hx1 hy1]
    nlinarith [H.hyx]
  exact le_trans hmono hLge'

theorem angleOrderHyps_false (x y L N T : ℚ) (H : AngleOrderHyps x y L N T) :
    False := by
  have hLge := angleOrder_L_ge x y L N T H
  have hx0 : 0 < x := H.hx0
  have hx1 : x < 1 := H.hx1
  have hx1p : (0 : ℚ) < 1 + x := by linarith
  have h1x2 : 0 < 1 - x * x := by nlinarith
  have hLg : L ≤ (1 + x * x) / (2 * x) := by
    have hx2 : (0 : ℚ) < 2 * x := by nlinarith
    exact (le_div_iff₀ hx2).mpr (by linarith [H.hLsin])
  have hLh : L ≤ (1 + x * x) / (1 - x * x) :=
    (le_div_iff₀ h1x2).mpr H.hLcos
  by_cases hcross : x * x + 2 * x ≤ 1
  · have hx12 : x < (1 : ℚ) / 2 := by
      by_contra h
      have hx12' : (1 : ℚ) / 2 ≤ x := le_of_not_gt h
      nlinarith [hcross, hx12']
    have hstrict : (1 + x * x) / (1 - x * x) < (1 + 3 * x) / (1 + x) := by
      rw [div_lt_div_iff₀ h1x2 hx1p]
      nlinarith [hx12]
    exact (not_le_of_gt (lt_of_le_of_lt hLh hstrict)) hLge
  · have hcross' : 1 < x * x + 2 * x := lt_of_not_ge hcross
    have hx25 : (2 : ℚ) / 5 < x := by
      by_contra h
      have hx25' : x ≤ (2 : ℚ) / 5 := le_of_not_gt h
      have : x * x + 2 * x ≤ (2 : ℚ) / 5 * ((2 : ℚ) / 5) + 2 * ((2 : ℚ) / 5) := by
        nlinarith [hx25']
      nlinarith [hcross']
    set a : ℚ := (2 : ℚ) / 5
    have hq25 : -a * a * a + 5 * (a * a) + a - 1 = (17 : ℚ) / 125 := by
      simp only [a]; norm_num
    have hfac :
        (-(x * x * x) + 5 * (x * x) + x - 1) -
            (-a * a * a + 5 * (a * a) + a - 1) =
          (x - a) * (-(x * x + x * a + a * a) + 5 * (x + a) + 1) := by
      ring
    have hposfac : 0 < -(x * x + x * a + a * a) + 5 * (x + a) + 1 := by
      have ha_val : a = (2 : ℚ) / 5 := rfl
      rw [ha_val]
      nlinarith [hx0, hx1]
    have hqpos : 0 < -(x * x * x) + 5 * (x * x) + x - 1 := by
      have ha : 0 < x - a := sub_pos.mpr hx25
      have hinc :
          (-a * a * a + 5 * (a * a) + a - 1) <
            -(x * x * x) + 5 * (x * x) + x - 1 := by
        have : 0 <
            (-(x * x * x) + 5 * (x * x) + x - 1) -
              (-a * a * a + 5 * (a * a) + a - 1) := by
          rw [hfac]; exact mul_pos ha hposfac
        linarith
      have h17 : (0 : ℚ) < (17 : ℚ) / 125 := by norm_num
      calc
        (0 : ℚ) < (17 : ℚ) / 125 := h17
        _ = -a * a * a + 5 * (a * a) + a - 1 := hq25.symm
        _ < -(x * x * x) + 5 * (x * x) + x - 1 := hinc
    have hstrict : (1 + x * x) / (2 * x) < (1 + 3 * x) / (1 + x) := by
      have hx2 : (0 : ℚ) < 2 * x := by nlinarith
      rw [div_lt_div_iff₀ hx2 hx1p]
      nlinarith [hqpos]
    exact (not_le_of_gt (lt_of_le_of_lt hLg hstrict)) hLge

def R14AngleOrderPackUnsat : Prop :=
  ∀ x y L N T : ℚ, AngleOrderHyps x y L N T → False

theorem r14AngleOrderPackUnsat : R14AngleOrderPackUnsat := angleOrderHyps_false

def r14AngleOrderPackUnsatProved : Bool := true
theorem r14AngleOrderPackUnsatProved_true : r14AngleOrderPackUnsatProved = true := rfl

def R14SE2RealisesAngleOrderPack : Prop :=
  ∀ _cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14,
    ∃ x y L N T : ℚ, AngleOrderHyps x y L N T

def r14SE2RealisesAngleOrderPackProved : Bool := false
theorem r14SE2RealisesAngleOrderPackProved_false :
    r14SE2RealisesAngleOrderPackProved = false := rfl

theorem r14SE2ForcesBridgeJunctionContradiction_of_angleOrderPack
    (H : R14SE2RealisesAngleOrderPack) :
    R14SE2ForcesBridgeJunctionContradiction := by
  intro cfg
  obtain ⟨x, y, L, N, T, h⟩ := H cfg
  exact angleOrderHyps_false x y L N T h

theorem bernsteinForcesRawEmpty_R14_of_angleOrderPack
    (H : R14SE2RealisesAngleOrderPack) :
    BernsteinForcesRawEmpty "R14" :=
  bernsteinForcesRawEmpty_R14_of_bridgeJunction
    (r14SE2ForcesBridgeJunctionContradiction_of_angleOrderPack H)

/-! ## Honest extended living packages (empty; not plain-SE2) -/

/-- SE2 plus ABridge witnesses. Empty by `aBridgeHyps_false`. Does **not**
assert that plain `NearEndSE2` supplies `(μ,c,s,A,D,U)`. -/
structure NearEndR14WithABridge where
  cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14
  μ : ℚ
  c : ℚ
  s : ℚ
  A : ℚ
  D : ℚ
  U : ℚ
  pack : ABridgeHyps μ c s cfg.z A D U

theorem not_nearEndR14WithABridge : ¬ Nonempty NearEndR14WithABridge := by
  rintro ⟨w⟩
  exact aBridgeHyps_false w.μ w.c w.s w.cfg.z w.A w.D w.U w.pack

structure NearEndR14WithLeftLength where
  cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14
  μ : ℚ
  l : ℚ
  pack : LeftLengthHyps μ cfg.z l

theorem not_nearEndR14WithLeftLength : ¬ Nonempty NearEndR14WithLeftLength := by
  rintro ⟨w⟩
  exact leftLengthHyps_false w.μ w.cfg.z w.l w.pack

structure NearEndR14WithJCondition where
  cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14
  μ : ℚ
  D : ℚ
  U : ℚ
  K : ℚ
  pack : JConditionHyps μ cfg.z D U K

theorem not_nearEndR14WithJCondition : ¬ Nonempty NearEndR14WithJCondition := by
  rintro ⟨w⟩
  exact jConditionHyps_false w.μ w.cfg.z w.D w.U w.K w.pack

structure NearEndR14WithNoLeftTip where
  cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14
  x : ℚ
  k : ℚ
  w : ℚ
  S : ℚ
  l : ℚ
  r : ℚ
  u : ℚ
  pack : NoLeftTipHyps x k w S l r u

theorem not_nearEndR14WithNoLeftTip : ¬ Nonempty NearEndR14WithNoLeftTip := by
  rintro ⟨w⟩
  exact noLeftTipHyps_false w.x w.k w.w w.S w.l w.r w.u w.pack

structure NearEndR14WithAngleOrder where
  cfg : NearEndSE2 BernsteinGeometryMap.leaf_R14
  x : ℚ
  y : ℚ
  L : ℚ
  N : ℚ
  T : ℚ
  pack : AngleOrderHyps x y L N T

theorem not_nearEndR14WithAngleOrder : ¬ Nonempty NearEndR14WithAngleOrder := by
  rintro ⟨w⟩
  exact angleOrderHyps_false w.x w.y w.L w.N w.T w.pack

def r14ExtendedPackagesEmptyProved : Bool := true
theorem r14ExtendedPackagesEmptyProved_true :
    r14ExtendedPackagesEmptyProved = true := rfl

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
  "CLOSED: LeftLength/ABridge/LeftGapOwner/JCondition/SumBudget/NoLeftTip/AngleOrder \
   algebraic unsat; NearEndR14With* empty. BLOCKED: plain SE2⇒pack fields; \
   ForcesBridgeJunction. Not R-poly≤0."

def openStatus : String :=
  "CLOSED: seven algebraic packs + extended-package emptiness. \
   OPEN: SE2⇒packs; ForcesBridgeJunction; BernsteinForcesRawEmpty; angleBudget. \
   Not PrincipalClaim / namedClosersDischarged."

end S6.CertR14BridgeJunction
