import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.NearEndRealisation
import S6Core.LivingLeafCertDischarge
import S6Core.BernsteinGeometryMap
import S6Core.CertGeometryIdentification
import S6Core.NearEndRationalChecks
import S6Core.NearEndExactR24_28
import S6Core.BernsteinExactP1
import S6Core.BernsteinGridLift
import S6Core.ChordLength

/-!
# J (u,v)-box / Bernstein-grid identification glue (R14 / R17 / R27–R28)

Sources (read-only): `artifacts/ex/all/round14_J_certificate*.json`,
`artifacts/certs/near_end_leaf_certificate_registry.json`,
`NearEndRationalChecks`, `NearEndExactR24_28`, `BernsteinExactP1`,
`BernsteinGridLift.bernstein_weight_nonneg`.

## Proved (honest partial)
1. `SE2FieldPackage` extracts chart/ray/left/F fields from any `NearEndSE2`.
2. Package respects chart `chord = f` and `OuterRayThresholds` / leaf hyps.
3. Unit-box predicate + 1D Bernstein degree-1 pointwise lower bound from coeff mins.
4. R14 J-cover sample mins all positive; R17 √2-sq / R27–28 coeff-grid tokens.
5. Conditional: `SE2PackageContradictsJCover label → BernsteinForcesRawEmpty label`.

## Blocked (full ID)
`SE2PackageContradictsJCover` uninhabited: no Lean map from package fields onto a
point of the J `(u,v)` cover where living geometry forces a nonpositive certificate
value. Multivariate J polys from `round14_J_certificate.json` are not ported.
Hence `BernsteinForcesRawEmpty` / `CertPositivityForcesSE2Empty` stay false.

Does **not** flip PrincipalClaim / namedClosersDischarged. Bridge files untouched.
BernsteinExact* modules not rewritten.
-/

namespace S6.CertJBoxIdentification

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.NearEndRealisation
open S6.LivingLeafCertDischarge
open S6.BernsteinGeometryMap
open S6.CertGeometryIdentification
open S6.NearEndRationalChecks
open S6.BernsteinGridLift
open S6.ChordLength

/-! ## Unit box + 1D Bernstein grid lift -/

def InUnitBox (u v : ℚ) : Prop :=
  0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1

def InUnitInterval (u : ℚ) : Prop := 0 ≤ u ∧ u ≤ 1

/-- Degree-1 Bernstein form on `[0,1]`: `(1-u)·c₀ + u·c₁`. -/
def bernstein1 (c0 c1 u : ℚ) : ℚ := (1 - u) * c0 + u * c1

theorem bernstein1_ge_of_coeff_mins (c0 c1 m u : ℚ)
    (h0 : m ≤ c0) (h1 : m ≤ c1) (hu : InUnitInterval u) :
    m ≤ bernstein1 c0 c1 u := by
  have ⟨hu0, hu1⟩ := hu
  have hsum : (1 - u) + u = (1 : ℚ) := by ring
  have : m * ((1 - u) + u) ≤ (1 - u) * c0 + u * c1 := by
    have a : m * (1 - u) ≤ (1 - u) * c0 := by nlinarith
    have b : m * u ≤ u * c1 := by nlinarith
    linarith
  simpa [bernstein1, hsum, mul_one] using this

theorem bernstein1_pos_of_strict_coeff_mins (c0 c1 m u : ℚ)
    (hm : 0 < m) (h0 : m ≤ c0) (h1 : m ≤ c1) (hu : InUnitInterval u) :
    0 < bernstein1 c0 c1 u :=
  lt_of_lt_of_le hm (bernstein1_ge_of_coeff_mins c0 c1 m u h0 h1 hu)

theorem unit_bernstein_weight_nonneg (u : ℚ) (i k : ℕ) (hu : InUnitInterval u) :
    0 ≤ u ^ i * (1 - u) ^ k :=
  bernstein_weight_nonneg u i k hu.1 hu.2

/-! ## SE2 field package (domain side of the missing map) -/

/-- Chart + ray + left + F fields carried by a partial SE(2) package. -/
structure SE2FieldPackage (ℓ : NearLeaf) where
  cfg : NearEndSE2 ℓ

def SE2FieldPackage.z {ℓ : NearLeaf} (p : SE2FieldPackage ℓ) : ℚ := p.cfg.z
def SE2FieldPackage.d {ℓ : NearLeaf} (p : SE2FieldPackage ℓ) : ℚ := p.cfg.d
def SE2FieldPackage.dR {ℓ : NearLeaf} (p : SE2FieldPackage ℓ) : ℚ := p.cfg.rays.dR
def SE2FieldPackage.dT {ℓ : NearLeaf} (p : SE2FieldPackage ℓ) : ℚ := p.cfg.rays.dT
def SE2FieldPackage.dL {ℓ : NearLeaf} (p : SE2FieldPackage ℓ) : ℚ := p.cfg.leftRays.dL
def SE2FieldPackage.fProj {ℓ : NearLeaf} (p : SE2FieldPackage ℓ) : ℚ := p.cfg.fProj

def se2FieldPackage_of (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) : SE2FieldPackage ℓ where
  cfg := cfg

theorem se2FieldPackage_chart (ℓ : NearLeaf) (p : SE2FieldPackage ℓ) :
    p.cfg.chart.leftRatio * p.cfg.chart.rightFactor = f p.z p.d :=
  chart_chord_of_se2 ℓ p.cfg

theorem se2FieldPackage_thresholds (ℓ : NearLeaf) (p : SE2FieldPackage ℓ) :
    OuterRayThresholds ℓ.rt p.cfg.rays :=
  outerRayThresholds_of_se2 ℓ p.cfg

theorem se2FieldPackage_leafHyp (ℓ : NearLeaf) (p : SE2FieldPackage ℓ) :
    LeafHypFromSE2 ℓ p.cfg :=
  leafHyp_of_se2 ℓ p.cfg

theorem r14_package_hyps (p : SE2FieldPackage BernsteinGeometryMap.leaf_R14) :
    (p.cfg.rays.meetsR ∧ p.cfg.rays.meetsT) ∧ p.cfg.leftRays.gapsL ∧ p.fProj = 0 :=
  r14_hyp_from_se2 p.cfg

theorem r17_package_hyps (p : SE2FieldPackage BernsteinGeometryMap.leaf_R17) :
    (p.cfg.rays.meetsR ∧ p.cfg.rays.meetsT) ∧ p.cfg.leftRays.gapsL ∧ p.fProj < 0 :=
  r17_hyp_from_se2 p.cfg

theorem r27_package_hyps (p : SE2FieldPackage BernsteinGeometryMap.leaf_R27_meet_empty) :
    (p.cfg.rays.gapsR ∧ p.cfg.rays.meetsT) ∧ p.cfg.leftRays.meetsL ∧ p.fProj = 0 :=
  r27_hyp_from_se2 p.cfg

/-! ## Cert-side J / Bernstein-grid positivity tokens -/

def R14JCoverSampleMinsPos : Prop :=
  (0 : ℚ) < (19 : ℚ) / 125 ∧
    (0 : ℚ) < (290632 : ℚ) / 9765625 ∧
      (0 : ℚ) < (451 : ℚ) / 80 ∧
        (0 : ℚ) < (7938371 : ℚ) / 160 ∧
          (0 : ℚ) < (33 : ℚ) / 8 ∧
            (0 : ℚ) < (81 : ℚ) / 32 ∧
              (0 : ℚ) < (81 : ℚ) / 20 ∧
                (0 : ℚ) < (197 : ℚ) / 80 ∧
                  (0 : ℚ) < (219 : ℚ) / 40 ∧
                    (0 : ℚ) < (159 : ℚ) / 40 ∧
                      (0 : ℚ) < (383 : ℚ) / 160 ∧
                        (0 : ℚ) < (39 : ℚ) / 10 ∧
                          (0 : ℚ) < (93 : ℚ) / 40

theorem r14_j_cover_sample_mins_pos : R14JCoverSampleMinsPos :=
  ⟨r14_c_root_min_R_pos, r14_c_root_min_P_pos, r14_m_00_min_R_pos, r14_m_00_min_P_pos,
    r14_m_0100_min_R_pos, r14_m_0101_min_R_pos, r14_m_0110_min_R_pos, r14_m_0111_min_R_pos,
    r14_m_10_min_R_pos, r14_m_1100_min_R_pos, r14_m_1101_min_R_pos, r14_m_1110_min_R_pos,
    r14_m_1111_min_R_pos⟩

def R17Sqrt2GridPos : Prop := R17CertBundle
theorem r17_sqrt2_grid_pos : R17Sqrt2GridPos := r17_certBundle

def R27_28CoeffGridPos : Prop :=
  R27_28CertBundle ∧
    S6.BernsteinExactP1.nonnegList
      S6.BernsteinExactP1.check_round27_g2_two_branches_n4_ba4d19a580_numer = true ∧
      S6.NearEndExactR24_28.nonnegList
        S6.NearEndExactR24_28.check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs = true

theorem r27_28_coeff_grid_pos : R27_28CoeffGridPos :=
  ⟨r27_28_certBundle,
    S6.BernsteinExactP1.check_round27_g2_two_branches_n4_ba4d19a580_numer_nonneg,
    S6.NearEndExactR24_28.check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs_nonneg⟩

def PriorityCertGridTokens : Prop :=
  R14JCoverSampleMinsPos ∧ R17Sqrt2GridPos ∧ R27_28CoeffGridPos

theorem priorityCertGridTokens : PriorityCertGridTokens :=
  ⟨r14_j_cover_sample_mins_pos, r17_sqrt2_grid_pos, r27_28_coeff_grid_pos⟩

/-! ## Conditional full ID (package contradiction ⇒ raw empty) -/

/-- OPEN geometric reading: every SE2 field package for this closer contradicts
the J/Bernstein-grid positivity cover (living geometry would force a nonpositive
certificate value on the cover). -/
def SE2PackageContradictsJCover (label : String) : Prop :=
  ∀ ℓ : NearLeaf, closerModule ℓ = label → ∀ _cfg : NearEndSE2 ℓ, False

theorem not_se2Inhabited_of_package_contradicts (label : String)
    (H : SE2PackageContradictsJCover label)
    (ℓ : NearLeaf) (hlab : closerModule ℓ = label) :
    ¬ NearEndSE2Inhabited ℓ := by
  intro ⟨cfg⟩
  exact H ℓ hlab cfg

theorem bernsteinForcesRawEmpty_of_package_contradicts (label : String)
    (H : SE2PackageContradictsJCover label) :
    BernsteinForcesRawEmpty label :=
  fun _hc ℓ hlab => not_se2Inhabited_of_package_contradicts label H ℓ hlab

theorem certPositivityForcesSE2Empty_of_package_contradicts (label : String)
    (H : SE2PackageContradictsJCover label) :
    CertPositivityForcesSE2Empty label :=
  fun _hc ℓ hlab => not_se2Inhabited_of_package_contradicts label H ℓ hlab

def JBoxIdPartial : Prop :=
  PriorityCertGridTokens ∧
    GeometrySideOfId BernsteinGeometryMap.leaf_R14 ∧
      GeometrySideOfId BernsteinGeometryMap.leaf_R17 ∧
        GeometrySideOfId BernsteinGeometryMap.leaf_R27_meet_empty

theorem jBoxIdPartial : JBoxIdPartial :=
  ⟨priorityCertGridTokens, geometrySide_of_any _, geometrySide_of_any _, geometrySide_of_any _⟩

theorem r14_c_root_min_R_bernstein1_pos (c0 c1 u : ℚ)
    (h0 : (19 : ℚ) / 125 ≤ c0) (h1 : (19 : ℚ) / 125 ≤ c1) (hu : InUnitInterval u) :
    0 < bernstein1 c0 c1 u :=
  bernstein1_pos_of_strict_coeff_mins c0 c1 _ u r14_c_root_min_R_pos h0 h1 hu

/-! ## Flags (honest) -/

def jBoxIdPartialProved : Bool := true
theorem jBoxIdPartialProved_true : jBoxIdPartialProved = true := rfl

def se2PackageContradictsJCoverProved : Bool := false
theorem se2PackageContradictsJCoverProved_false :
    se2PackageContradictsJCoverProved = false := rfl

def bernsteinForcesRawEmptyProved : Bool := false
theorem bernsteinForcesRawEmptyProved_false : bernsteinForcesRawEmptyProved = false := rfl

def certPositivityForcesSE2EmptyProved : Bool := false
theorem certPositivityForcesSE2EmptyProved_false :
    certPositivityForcesSE2EmptyProved = false := rfl

def rawSE2EmptyProved : Bool := false
theorem rawSE2EmptyProved_false : rawSE2EmptyProved = false := rfl

def blockedReason : String :=
  "Partial J-box ID CLOSED: SE2FieldPackage + chart/threshold/leafHyp; 1D Bernstein \
   pointwise lower bound; R14 cover sample mins; R17/R27 grid tokens; conditional \
   package-contradicts ⇒ BernsteinForcesRawEmpty. \
   FULL ID BLOCKED: SE2PackageContradictsJCover uninhabited (no Lean (u,v) map / \
   multivariate J poly from package fields)."

def openStatus : String :=
  "CLOSED: CertJBoxIdentification partial (package + grid tokens + bernstein1 lift). \
   OPEN: SE2PackageContradictsJCover; BernsteinForcesRawEmpty; combinatorial spine. \
   Not PrincipalClaim / namedClosersDischarged."

end S6.CertJBoxIdentification
