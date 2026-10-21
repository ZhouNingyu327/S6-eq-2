import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.LivingLeafCertDischarge
import S6Core.BernsteinGeometryMap
import S6Core.ChordLength
import S6Core.RigidMotionChart

/-!
# Partial cert positivity ↔ chart/ray identification (R14 / R17 / R27–R28)

Sources: `artifacts/closure/CERT_TO_LEAN_HANDOFF.md`,
`artifacts/certs/near_end_leaf_certificate_registry.json`,
`NearEndRationalChecks` / `NearEndExactR24_28` payloads.

## Proved (honest partial ID)
1. Any `NearEndSE2 ℓ` reproduces registry leaf hypotheses:
   `OuterRTMatches`, `LeftStatusMatches`, `FHorizMatches`.
2. Chart side: `chord = f(z,d)` from `ChartHypotheses`.
3. Ray thresholds: OuterRT meet/gap decode to `dR`/`dT` inequalities when matched.
4. Cert positivity cores inhabited (R14/R17/R27–28) — same as BernsteinGeometryMap.
5. Combined `CertGeometryIdPartial` packages (1)–(4) for priority closers.

## Blocked (full ID)
`CertPositivityForcesSE2Empty`: no Lean map from Bernstein/ℚ positivity
(`min_R`/`min_P`, √2-sq bounds, coeff nonneg lists) to a contradiction among
`(C, rays, leftRays, chart, fProj)`. Those payloads live in `(u,v)` / poly boxes
in the J-certificate JSON, not yet identified with SE(2) fields.

Does **not** inhabit `BernsteinForcesRawEmpty`. Not PrincipalClaim.
-/

namespace S6.CertGeometryIdentification

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.LivingLeafCertDischarge
open S6.BernsteinGeometryMap
open S6.NearEndRationalChecks
open S6.ChordLength
open S6.RigidMotionChart

/-- Registry geometric hypotheses as matched by a partial SE(2) package. -/
def LeafHypFromSE2 (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) : Prop :=
  OuterRTMatches ℓ.rt cfg.rays ∧
    LeftStatusMatches ℓ.left cfg.leftRays ∧
      FHorizMatches ℓ.fh cfg.fProj

theorem leafHyp_of_se2 (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) : LeafHypFromSE2 ℓ cfg :=
  ⟨cfg.rt_ok, cfg.left_ok, cfg.fh_ok⟩

/-- Chart identification fragment already on `NearEndSE2`. -/
theorem chart_chord_of_se2 (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) :
    cfg.chart.leftRatio * cfg.chart.rightFactor = f cfg.z cfg.d :=
  NearEndSE2.chord_eq_f cfg

/-- Outer ray distance thresholds implied by OuterRT match. -/
def OuterRayThresholds {g : RigidMotion} (rt : OuterRT) (w : OuterRayWitnesses g) : Prop :=
  match rt with
  | .bothMeet => w.dR ≤ 1 ∧ w.dT ≤ 1
  | .topGap => w.dR ≤ 1 ∧ 1 < w.dT
  | .rightGap => 1 < w.dR ∧ w.dT ≤ 1
  | .bothGap => 1 < w.dR ∧ 1 < w.dT

theorem outerRayThresholds_of_rtMatches {g : RigidMotion} (rt : OuterRT)
    (w : OuterRayWitnesses g) (h : OuterRTMatches rt w) : OuterRayThresholds rt w := by
  cases rt with
  | bothMeet =>
    change w.meetsR ∧ w.meetsT at h
    exact ⟨h.1.2, h.2.2⟩
  | topGap =>
    change w.meetsR ∧ w.gapsT at h
    exact ⟨h.1.2, h.2.2⟩
  | rightGap =>
    change w.gapsR ∧ w.meetsT at h
    exact ⟨h.1.2, h.2.2⟩
  | bothGap =>
    change w.gapsR ∧ w.gapsT at h
    exact ⟨h.1.2, h.2.2⟩

theorem outerRayThresholds_of_se2 (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) :
    OuterRayThresholds ℓ.rt cfg.rays :=
  outerRayThresholds_of_rtMatches ℓ.rt cfg.rays cfg.rt_ok

/-! ## Priority leaf anchors -/

-- leaf anchors from BernsteinGeometryMap (same NearLeaf triples)
abbrev leaf_R14 := BernsteinGeometryMap.leaf_R14
abbrev leaf_R17 := BernsteinGeometryMap.leaf_R17
abbrev leaf_R27_meet_empty := BernsteinGeometryMap.leaf_R27_meet_empty

/-- R14 registry hyps from SE2: bothMeet + left gap + F empty. -/
theorem r14_hyp_from_se2 (cfg : NearEndSE2 leaf_R14) :
    (cfg.rays.meetsR ∧ cfg.rays.meetsT) ∧ cfg.leftRays.gapsL ∧ cfg.fProj = 0 :=
  ⟨realised_bothMeet_meets leaf_R14 cfg rfl,
    realised_left_gap leaf_R14 cfg rfl,
    realised_empty_fProj leaf_R14 cfg rfl⟩

/-- R17 registry hyps: bothMeet + left gap + F neg. -/
theorem r17_hyp_from_se2 (cfg : NearEndSE2 leaf_R17) :
    (cfg.rays.meetsR ∧ cfg.rays.meetsT) ∧ cfg.leftRays.gapsL ∧ cfg.fProj < 0 :=
  ⟨realised_bothMeet_meets leaf_R17 cfg rfl,
    realised_left_gap leaf_R17 cfg rfl,
    realised_neg_fProj leaf_R17 cfg rfl⟩

/-- R27 meet/empty registry hyps: rightGap + left meet + F empty. -/
theorem r27_hyp_from_se2 (cfg : NearEndSE2 leaf_R27_meet_empty) :
    (cfg.rays.gapsR ∧ cfg.rays.meetsT) ∧ cfg.leftRays.meetsL ∧ cfg.fProj = 0 :=
  ⟨realised_rightGap_rays leaf_R27_meet_empty cfg rfl,
    realised_left_meet leaf_R27_meet_empty cfg rfl,
    realised_empty_fProj leaf_R27_meet_empty cfg rfl⟩

/-! ## Partial identification package -/

/-- Strongest honest partial ID for one priority closer leaf. -/
structure CertGeometryIdPartial (ℓ : NearLeaf) (label : String) : Prop where
  closer : closerModule ℓ = label
  cert : CloserCertDischarged label
  hyp_of_se2 : ∀ cfg : NearEndSE2 ℓ, LeafHypFromSE2 ℓ cfg
  chart_of_se2 : ∀ cfg : NearEndSE2 ℓ,
    cfg.chart.leftRatio * cfg.chart.rightFactor = f cfg.z cfg.d
  thresholds_of_se2 : ∀ cfg : NearEndSE2 ℓ, OuterRayThresholds ℓ.rt cfg.rays
  excludes_dual : ∀ cfg : NearEndSE2 ℓ, ¬ CloserDualResidual ℓ cfg.rays

theorem certGeometryIdPartial_mk (ℓ : NearLeaf) (label : String)
    (hc : closerModule ℓ = label) (hcert : CloserCertDischarged label) :
    CertGeometryIdPartial ℓ label where
  closer := hc
  cert := hcert
  hyp_of_se2 := fun cfg => leafHyp_of_se2 ℓ cfg
  chart_of_se2 := fun cfg => chart_chord_of_se2 ℓ cfg
  thresholds_of_se2 := fun cfg => outerRayThresholds_of_se2 ℓ cfg
  excludes_dual := fun cfg => se2_excludes_dualResidual ℓ cfg

theorem certGeometryIdPartial_R14 : CertGeometryIdPartial leaf_R14 "R14" :=
  certGeometryIdPartial_mk _ _ (by native_decide) closerCert_R14

theorem certGeometryIdPartial_R17 : CertGeometryIdPartial leaf_R17 "R17" :=
  certGeometryIdPartial_mk _ _ (by native_decide) closerCert_R17

theorem certGeometryIdPartial_R27_meet_empty :
    CertGeometryIdPartial leaf_R27_meet_empty "R27/R28" :=
  certGeometryIdPartial_mk _ _ (by native_decide) closerCert_R27_28

def AllPriorityCertGeometryIdPartials : Prop :=
  CertGeometryIdPartial leaf_R14 "R14" ∧
    CertGeometryIdPartial leaf_R17 "R17" ∧
      CertGeometryIdPartial leaf_R27_meet_empty "R27/R28"

theorem allPriorityCertGeometryIdPartials : AllPriorityCertGeometryIdPartials :=
  ⟨certGeometryIdPartial_R14, certGeometryIdPartial_R17, certGeometryIdPartial_R27_meet_empty⟩

/-! ## R14 J-certificate positivity tokens (from round14_J_certificate.json) -/

/-- Branch-c root leaf min_R / min_P positivity (exact-rational Bernstein). -/
def R14JBranchCPositivity : Prop :=
  (0 : ℚ) < (19 : ℚ) / 125 ∧ (0 : ℚ) < (290632 : ℚ) / 9765625

theorem r14_j_branch_c_positivity : R14JBranchCPositivity :=
  ⟨r14_c_root_min_R_pos, r14_c_root_min_P_pos⟩

/-- Branch-m path-00 min_R positivity sample. -/
def R14JBranchM00Positivity : Prop := (0 : ℚ) < (451 : ℚ) / 80

theorem r14_j_branch_m00_positivity : R14JBranchM00Positivity := r14_m_00_min_R_pos

/-- R17 analytic √2-squared bounds from NearEndRationalChecks. -/
def R17AnalyticPositivity : Prop := R17CertBundle

theorem r17_analytic_positivity : R17AnalyticPositivity := r17_certBundle

/-- R27/R28 harness Bernstein uniform-sign sample. -/
def R27_28BernsteinPositivity : Prop := R27_28CertBundle

theorem r27_28_bernstein_positivity : R27_28BernsteinPositivity := r27_28_certBundle

/-! ## Honest ID interface (two sides; no map) -/

/-- Geometry side of the missing J ID: SE2 ⇒ registry leaf hyps + chart + thresholds. -/
def GeometrySideOfId (ℓ : NearLeaf) : Prop :=
  (∀ cfg : NearEndSE2 ℓ, LeafHypFromSE2 ℓ cfg) ∧
    (∀ cfg : NearEndSE2 ℓ,
      cfg.chart.leftRatio * cfg.chart.rightFactor = f cfg.z cfg.d) ∧
      (∀ cfg : NearEndSE2 ℓ, OuterRayThresholds ℓ.rt cfg.rays)

theorem geometrySide_of_any (ℓ : NearLeaf) : GeometrySideOfId ℓ :=
  ⟨fun cfg => leafHyp_of_se2 ℓ cfg,
    fun cfg => chart_chord_of_se2 ℓ cfg,
    fun cfg => outerRayThresholds_of_se2 ℓ cfg⟩

/-- Cert side of the missing J ID: positivity cores for priority closers. -/
def CertSideOfId : Prop :=
  R14CertPositivityCore ∧ R17CertPositivityCore ∧ R27_28CertPositivityCore

theorem certSide_of_id : CertSideOfId :=
  ⟨r14_cert_positivity_core, r17_cert_positivity_core, r27_28_cert_positivity_core⟩

/-! ## Open full-ID residual -/

/-- Missing J step: cert positivity forces raw SE2 emptiness for this closer. -/
def CertPositivityForcesSE2Empty (label : String) : Prop :=
  CloserCertDischarged label →
    ∀ ℓ : NearLeaf, closerModule ℓ = label → ¬ NearEndSE2Inhabited ℓ

/-- Equivalent residual already named on BernsteinGeometryMap. -/
theorem certPositivityForcesSE2Empty_iff_bernsteinForces (label : String) :
    CertPositivityForcesSE2Empty label ↔ BernsteinForcesRawEmpty label :=
  Iff.rfl

def certPositivityForcesSE2EmptyProved : Bool := false
theorem certPositivityForcesSE2EmptyProved_false :
    certPositivityForcesSE2EmptyProved = false := rfl

def certGeometryIdPartialProved : Bool := true
theorem certGeometryIdPartialProved_true : certGeometryIdPartialProved = true := rfl

/-- Both sides inhabited; the identification map between them is still open. -/
theorem bothSidesInhabited_id_map_open :
    CertSideOfId ∧
      GeometrySideOfId leaf_R14 ∧
        GeometrySideOfId leaf_R17 ∧
          GeometrySideOfId leaf_R27_meet_empty ∧
            certPositivityForcesSE2EmptyProved = false :=
  ⟨certSide_of_id, geometrySide_of_any _, geometrySide_of_any _, geometrySide_of_any _,
    certPositivityForcesSE2EmptyProved_false⟩


/-- Same residual as BernsteinGeometryMap (not flipped). -/
theorem bernsteinForcesRawEmpty_still_open :
    BernsteinGeometryMap.bernsteinForcesRawEmptyProved = false :=
  BernsteinGeometryMap.bernsteinForcesRawEmptyProved_false

theorem rawSE2Empty_still_open :
    BernsteinGeometryMap.rawSE2EmptyProved = false :=
  BernsteinGeometryMap.rawSE2EmptyProved_false

def blockedReason : String :=
  "Partial ID CLOSED: SE2⇒registry hyps + chart chord=f + ray thresholds + cert cores. \
   FULL ID BLOCKED: R14 min_R/min_P live on J (u,v) Bernstein boxes; R17 √2-sq and \
   R27 coeff lists have no Lean map onto (C,rays,leftRays,chart,fProj) contradiction."

def openStatus : String :=
  "CLOSED: CertGeometryIdPartial for R14/R17/R27–28; leafHyp/chart/threshold extraction; \
   J positivity tokens exported. \
   OPEN: CertPositivityForcesSE2Empty / BernsteinForcesRawEmpty; combinatorial spine. \
   Not PrincipalClaim / namedClosersDischarged."

end S6.CertGeometryIdentification
