import Mathlib.Tactic
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.OwnershipBridge
import S6Core.RigidMotionChart
import S6Core.BernsteinGridLift
import S6Core.GridContribution
import S6Core.RotatedGridBound
import S6Core.G5Budget
import S6Core.G5ExclusionFrag
import S6Core.G5GeometryBridge
import S6Core.AxisG5k0FromCover
import S6Core.AxisGridCover
import S6Core.AxisGridContribution
import S6Core.ChordLength
import S6Core.ObliqueChart
import S6Core.IntervalCover1D

/-!
# Rotated chord-measure fragments (toward G5k*GeomExport)

Proved: diameter `distSq ≤ 2`; Weierstrass `g2_alg < 2`;
`RotatedG5k0ChordExport` ⇒ `G5k0GeomExport` / `G5k0Bridge`;
six-line chord matrix algebra; projected-width ≤ 2 on unit directions;
axis/identity-C realisation ⇒ `RotatedChordCoverIneq`.
Proved: `RotatedGridRatCover` from every `PointwiseCover` (six-line ℚ cover, no axis hyp);
axis lift via alignment; meet predicates; line-package export ⇒ CoverIneq.
Proved: horiz/vert chord Δ²≤2 and |Δ|≤2; RotatedLineChordCover algebra;
SixLineMeasureLift ⇒ CoverIneq / G5k0Bridge / GeomExport / LinePackageExport.
Proved: corner diameter-miss (4 corners vs opposite sides) for any PointwiseCover;
onesided axial sum ≤2; ChordMatrixExport ⇒ SixLineMeasureLift.
Proved: AxisCoverBridge ⇒ ChordMatrixExport; axis bottom LineChordCover; roles contrib ≤2.
Proved: real containsR/horizSliceR Inf-Sup chords; RotatedLineMeasureLift from any
RotatedGridRatCover (bottom line Euclidean cover).
Proved: |Δx|/|Δy| ≤ |c|+|s|; parallel miss bottom↔top and left↔right (μ>1);
vertSliceR Inf-Sup; RotatedSixLineRealLift (all six grid lines) from any rat cover.
Proved: distSq on containsR; clamped [0,2μ] lens; all four corner outer pairs ≤ 2;
PointwiseCover corner clamped packing.
Proved: corner mid-miss when μ²>2; corner outer+mid pack skeleton (μ²>2).
Proved: centre outer-miss when μ²>2 (RoleSelection / PointwiseCover);
projWidth mid-miss (|c|+|s|<μ) for all four corners (partial μ²≤2 path).
Proved: four-corner clampedSquareTotal ≤2 under projWidth (mids+far sides empty).
Proved: μ²>2 auto corner clampedSquareTotal; centre outer clamped=0;
chord/clamped ≤ projWidth; mid-sum ≤ 2·projWidth.
Open: filler packing; ChordMatrixExport; full BodyChartAxis / IdentityC;
G3 from covers (s²=2/ℚ blocked); unconditional PrincipalClaim.
-/

namespace S6.RotatedChordMeasure

open S6.Obligation2
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.OwnershipBridge
open S6.BernsteinGridLift
open S6.GridContribution
open S6.RotatedGridBound
open S6.G5Budget
open S6.G5ExclusionFrag
open S6.G5GeometryBridge

theorem chord_distSq_le_two (g : RotatedSquare) (p q : Pt)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q) :
    distSq p q ≤ 2 :=
  rotated_unit_diameter g p q hp hq

theorem chord_len_sq_le_two (g : RotatedSquare) (p q : Pt) (ℓ : ℚ)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q)
    (hℓ : ℓ * ℓ = distSq p q) :
    ℓ * ℓ ≤ 2 := by
  rw [hℓ]; exact chord_distSq_le_two g p q hp hq

theorem weierstrass_corner_budget (t : ℚ) (ht0 : 0 < t) (ht : t < 1 / 2) :
    g2_alg t < 2 :=
  corner_g2_alg_lt_two t ht0 ht

theorem four_corner_lengths_le_eight (c1 c2 c3 c4 : ℚ)
    (h1 : c1 ≤ 2) (h2 : c2 ≤ 2) (h3 : c3 ≤ 2) (h4 : c4 ≤ 2) :
    c1 + c2 + c3 + c4 ≤ 8 := by nlinarith

theorem chord_bounds_impossible (μ corners CF : ℚ) (hμ : 1 < μ)
    (hcorners : corners ≤ 8) (hCF : CF ≤ 4)
    (hcover : (12 : ℚ) * μ ≤ corners + CF) : False :=
  (G5GridHypLe.mk μ corners CF hμ hcorners hCF hcover).impossible

/-- Open: G5 k=0 cover exports chord corners≤8, CF≤4, cover ineq. -/
def RotatedG5k0ChordExport : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ corners CF : ℚ,
          corners ≤ 8 ∧ CF ≤ 4 ∧ (12 : ℚ) * T.μ ≤ corners + CF

/-- CF≤4 + cover + μ>1 ⇒ CF<4 (else 12μ ≤ corners+4 ≤ 12, contradiction). -/
theorem CF_strict_of_le_four (μ corners CF : ℚ) (hμ : 1 < μ)
    (hcorners : corners ≤ 8) (hCF : CF ≤ 4)
    (hcover : (12 : ℚ) * μ ≤ corners + CF) : CF < 4 := by
  by_contra hne
  have hge : (4 : ℚ) ≤ CF := le_of_not_gt hne
  have hEq : CF = 4 := le_antisymm hCF hge
  have : (12 : ℚ) * μ ≤ corners + 4 := by simpa [hEq] using hcover
  nlinarith [hμ, hcorners, this]

theorem G5k0Bridge_of_rotatedChordExport (h : RotatedG5k0ChordExport) :
    G5k0Bridge := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨corners, CF, hc, hCF, hcover⟩
  exact False.elim (chord_bounds_impossible T.μ corners CF T.hμ hc hCF hcover)

theorem G5k0GeomExport_of_rotatedChordExport (h : RotatedG5k0ChordExport) :
    G5k0GeomExport := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨corners, CF, hc, hCF, hcover⟩
  have hstrict := CF_strict_of_le_four T.μ corners CF T.hμ hc hCF hcover
  exact ⟨⟨corners, CF, T.hμ, hc, hstrict, hcover⟩⟩

def rotatedChordAlgebraicClosed : Bool := true
theorem rotatedChordAlgebraicClosed_true : rotatedChordAlgebraicClosed = true := rfl

def rotatedG5k0ChordExportProved : Bool := false
theorem rotatedG5k0ChordExportProved_false : rotatedG5k0ChordExportProved = false := rfl

def openRotatedChordExports : List String :=
  ["RotatedChordLinePackageExport / Euclidean chords from RotatedGridRatCover",
   "g2_alg geometric reading as outer chord sum"]


/-- Four unit-square diameter bounds ⇒ corners ≤ 8 (chord-export algebra). -/
theorem corners_le_eight_of_unit_diameters (c1 c2 c3 c4 : ℚ)
    (h1 : c1 ≤ 2) (h2 : c2 ≤ 2) (h3 : c3 ≤ 2) (h4 : c4 ≤ 2) :
    c1 + c2 + c3 + c4 ≤ 8 :=
  four_corner_lengths_le_eight c1 c2 c3 c4 h1 h2 h3 h4

/-- Two mid chords each ≤ 2 ⇒ CF ≤ 4. -/
theorem CF_le_four_of_unit_diameters (m1 m2 : ℚ) (h1 : m1 ≤ 2) (h2 : m2 ≤ 2) :
    m1 + m2 ≤ 4 := by nlinarith

/-- Package: if a G5 k=0 cover exports four corner chords ≤2, two mid chords ≤2,
and the grid covering inequality, then `RotatedG5k0ChordExport` holds. -/
def RotatedChordBoundPackage : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ (c1 c2 c3 c4 m1 m2 : ℚ),
          c1 ≤ 2 ∧ c2 ≤ 2 ∧ c3 ≤ 2 ∧ c4 ≤ 2 ∧ m1 ≤ 2 ∧ m2 ≤ 2 ∧
            (12 : ℚ) * T.μ ≤ (c1 + c2 + c3 + c4) + (m1 + m2)

theorem RotatedG5k0ChordExport_of_boundPackage (h : RotatedChordBoundPackage) :
    RotatedG5k0ChordExport := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨c1, c2, c3, c4, m1, m2, h1, h2, h3, h4, hm1, hm2, hcover⟩
  refine ⟨c1 + c2 + c3 + c4, m1 + m2, ?_, ?_, hcover⟩
  · exact corners_le_eight_of_unit_diameters c1 c2 c3 c4 h1 h2 h3 h4
  · exact CF_le_four_of_unit_diameters m1 m2 hm1 hm2

theorem G5k0GeomExport_of_boundPackage (h : RotatedChordBoundPackage) :
    G5k0GeomExport :=
  G5k0GeomExport_of_rotatedChordExport (RotatedG5k0ChordExport_of_boundPackage h)

theorem G5k0Bridge_of_boundPackage (h : RotatedChordBoundPackage) : G5k0Bridge :=
  G5k0Bridge_of_rotatedChordExport (RotatedG5k0ChordExport_of_boundPackage h)

/-- Corner owners of any PointwiseCover each have diameter ≤ 2 on their corner pair
(already true pairwise on one square; here: each owner square has diam ≤ 2). -/
theorem owner_square_diameter {T : Target} (cov : PointwiseCover T) (i : Fin 6)
    (p q : Pt)
    (hp : RotatedSquare.contains (cov.squares i) p)
    (hq : RotatedSquare.contains (cov.squares i) q) :
    distSq p q ≤ 2 :=
  chord_distSq_le_two (cov.squares i) p q hp hq

def rotatedChordBoundPackageProved : Bool := false
theorem rotatedChordBoundPackageProved_false : rotatedChordBoundPackageProved = false := rfl


open S6.AxisG5k0FromCover
open S6.AxisGridCover
open S6.ObliqueChart
open S6.ChordLength (UnitDir)

/-- Axis / identity-C realisation ⇒ `RotatedG5k0ChordExport` (via GeomExport). -/
theorem RotatedG5k0ChordExport_of_axisRealisation (h : AxisAlignedG5k0Realisation) :
    RotatedG5k0ChordExport := by
  intro T cov hcls hk
  rcases G5k0GeomExport_of_axisRealisation h T cov hcls hk with ⟨E⟩
  exact ⟨E.corners, E.CF, E.hcorners, le_of_lt E.hCF, E.hcover⟩

theorem RotatedG5k0ChordExport_of_identityCRealisation
    (h : AxisAlignedIdentityCRealisation) : RotatedG5k0ChordExport :=
  RotatedG5k0ChordExport_of_axisRealisation
    (AxisAlignedG5k0Realisation_of_identityCRealisation h)

def rotatedExportFromAxisPathClosed : Bool := true
theorem rotatedExportFromAxisPathClosed_true :
    rotatedExportFromAxisPathClosed = true := rfl


/-! ## Bound-package split: diameters held; cover ineq residual -/

/-- Max unit-diameter proxies cannot satisfy cover ineq when `μ>1`. -/
theorem max_diameter_cover_ineq_impossible (μ : ℚ) (hμ : 1 < μ) :
    ¬((12 : ℚ) * μ ≤ (2 + 2 + 2 + 2) + (2 + 2)) := by
  intro h; nlinarith

/-- All-max diameter proxies never inhabit the package cover ineq. -/
theorem RotatedChordBoundPackage_needs_tight_chords :
    ∀ (μ : ℚ), 1 < μ →
      ¬∃ (c1 c2 c3 c4 m1 m2 : ℚ),
        c1 = 2 ∧ c2 = 2 ∧ c3 = 2 ∧ c4 = 2 ∧ m1 = 2 ∧ m2 = 2 ∧
          (12 : ℚ) * μ ≤ (c1 + c2 + c3 + c4) + (m1 + m2) := by
  intro μ hμ ⟨_, _, _, _, _, _, h1, h2, h3, h4, hm1, hm2, hcover⟩
  subst h1; subst h2; subst h3; subst h4; subst hm1; subst hm2
  exact max_diameter_cover_ineq_impossible μ hμ hcover

/-- Diameter upper bounds `≤ 2` are always available (take proxies `= 2`). -/
def RotatedChordDiameterBounds : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ (c1 c2 c3 c4 m1 m2 : ℚ),
          c1 ≤ 2 ∧ c2 ≤ 2 ∧ c3 ≤ 2 ∧ c4 ≤ 2 ∧ m1 ≤ 2 ∧ m2 ≤ 2

theorem RotatedChordDiameterBounds_held : RotatedChordDiameterBounds := by
  intro T cov _ _
  exact ⟨2, 2, 2, 2, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- Residual: cover inequality at some diameter-bounded chord measures. -/
def RotatedChordCoverIneq : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ (c1 c2 c3 c4 m1 m2 : ℚ),
          c1 ≤ 2 ∧ c2 ≤ 2 ∧ c3 ≤ 2 ∧ c4 ≤ 2 ∧ m1 ≤ 2 ∧ m2 ≤ 2 ∧
            (12 : ℚ) * T.μ ≤ (c1 + c2 + c3 + c4) + (m1 + m2)

theorem RotatedChordBoundPackage_iff_coverIneq :
    RotatedChordBoundPackage ↔ RotatedChordCoverIneq :=
  ⟨fun h => h, fun h => h⟩

theorem RotatedG5k0ChordExport_of_coverIneq (h : RotatedChordCoverIneq) :
    RotatedG5k0ChordExport :=
  RotatedG5k0ChordExport_of_boundPackage h

theorem G5k0GeomExport_of_coverIneq (h : RotatedChordCoverIneq) : G5k0GeomExport :=
  G5k0GeomExport_of_boundPackage h

theorem G5k0Bridge_of_coverIneq (h : RotatedChordCoverIneq) : G5k0Bridge :=
  G5k0Bridge_of_boundPackage h

def rotatedChordDiameterBoundsClosed : Bool := true
theorem rotatedChordDiameterBoundsClosed_true :
    rotatedChordDiameterBoundsClosed = true := rfl


/-! ## Six-line chord matrix + CoverIneq packaging -/

/-- Explicit `Fin 6` sum (ℚ; avoids Finset friction). -/
def sum6 (f : Fin 6 → ℚ) : ℚ :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5

theorem sum6_le_of_le (f g : Fin 6 → ℚ) (h : ∀ i, f i ≤ g i) :
    sum6 f ≤ sum6 g := by
  simp only [sum6]; nlinarith [h 0, h 1, h 2, h 3, h 4, h 5]

/-- Chord lengths of six squares on six target lines. -/
structure SixLineChordMatrix where
  μ : ℚ
  chord : Fin 6 → Fin 6 → ℚ
  nonneg : ∀ ℓ i, 0 ≤ chord ℓ i
  lineCover : ∀ ℓ, (2 : ℚ) * μ ≤ sum6 (fun i => chord ℓ i)

theorem SixLineChordMatrix.total_ge (M : SixLineChordMatrix) :
    (12 : ℚ) * M.μ ≤ sum6 (fun ℓ => sum6 (fun i => M.chord ℓ i)) := by
  have h0 := M.lineCover 0
  have h1 := M.lineCover 1
  have h2 := M.lineCover 2
  have h3 := M.lineCover 3
  have h4 := M.lineCover 4
  have h5 := M.lineCover 5
  simp only [sum6] at h0 h1 h2 h3 h4 h5 ⊢
  nlinarith

def SixLineChordMatrix.squareTotal (M : SixLineChordMatrix) (i : Fin 6) : ℚ :=
  sum6 (fun ℓ => M.chord ℓ i)

theorem SixLineChordMatrix.total_eq_square_sum (M : SixLineChordMatrix) :
    sum6 (fun ℓ => sum6 (fun i => M.chord ℓ i)) =
      sum6 (fun i => M.squareTotal i) := by
  simp only [sum6, SixLineChordMatrix.squareTotal]
  ring

/-- Six lines covered + each square total ≤ 2 ⇒ False when μ>1. -/
theorem SixLineChordMatrix.impossible_of_square_ub (M : SixLineChordMatrix)
    (hμ : 1 < M.μ) (hub : ∀ i, M.squareTotal i ≤ 2) : False := by
  have htot := M.total_ge
  rw [M.total_eq_square_sum] at htot
  have hsumle : sum6 (fun i => M.squareTotal i) ≤ 12 := by
    have h := sum6_le_of_le (fun i => M.squareTotal i) (fun _ => (2 : ℚ)) hub
    have : sum6 (fun _ : Fin 6 => (2 : ℚ)) = 12 := by simp only [sum6]; norm_num
    linarith
  nlinarith

/-- G5k0 chord package: four corner + two mid measures. -/
structure RotatedChordLinePackage (μ : ℚ) where
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  m1 : ℚ
  m2 : ℚ
  hc1 : c1 ≤ 2
  hc2 : c2 ≤ 2
  hc3 : c3 ≤ 2
  hc4 : c4 ≤ 2
  hm1 : m1 ≤ 2
  hm2 : m2 ≤ 2
  hcover : (12 : ℚ) * μ ≤ (c1 + c2 + c3 + c4) + (m1 + m2)

theorem RotatedChordCoverIneq_of_linePackage
    (H : ∀ (T : Target) (cov : PointwiseCover T),
      isG5Class cov →
        (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
          Nonempty (RotatedChordLinePackage T.μ)) :
    RotatedChordCoverIneq := by
  intro T cov hcls hk
  obtain ⟨P⟩ := H T cov hcls hk
  exact ⟨P.c1, P.c2, P.c3, P.c4, P.m1, P.m2, P.hc1, P.hc2, P.hc3, P.hc4, P.hm1, P.hm2, P.hcover⟩

theorem RotatedChordLinePackage_impossible {μ : ℚ} (P : RotatedChordLinePackage μ)
    (hμ : 1 < μ) : False := by
  nlinarith [P.hc1, P.hc2, P.hc3, P.hc4, P.hm1, P.hm2, P.hcover, hμ]

/-- Axis G5k0 realisation ⇒ CoverIneq (split GeomExport corners/CF). -/
theorem RotatedChordCoverIneq_of_axisRealisation (h : AxisAlignedG5k0Realisation) :
    RotatedChordCoverIneq := by
  intro T cov hcls hk
  rcases G5k0GeomExport_of_axisRealisation h T cov hcls hk with ⟨E⟩
  have hc : E.corners / 4 ≤ 2 := by linarith [E.hcorners]
  have hm : E.CF / 2 ≤ 2 := by linarith [E.hCF]
  refine ⟨E.corners / 4, E.corners / 4, E.corners / 4, E.corners / 4,
    E.CF / 2, E.CF / 2, hc, hc, hc, hc, hm, hm, ?_⟩
  have hsum : (E.corners / 4 + E.corners / 4 + E.corners / 4 + E.corners / 4) +
      (E.CF / 2 + E.CF / 2) = E.corners + E.CF := by ring
  nlinarith [E.hcover, hsum]

theorem RotatedChordCoverIneq_of_identityC (h : AxisAlignedIdentityCRealisation) :
    RotatedChordCoverIneq :=
  RotatedChordCoverIneq_of_axisRealisation
    (AxisAlignedG5k0Realisation_of_identityCRealisation h)

def sixLineChordAlgebraClosed : Bool := true
theorem sixLineChordAlgebraClosed_true : sixLineChordAlgebraClosed = true := rfl

def rotatedChordCoverIneqFromAxisPathClosed : Bool := true
theorem rotatedChordCoverIneqFromAxisPathClosed_true :
    rotatedChordCoverIneqFromAxisPathClosed = true := rfl


/-! ## Rotated six-line ℚ cover from PointwiseCover -/

/-- ℚ pointwise cover of the six target grid lines by rotated squares. -/
structure RotatedGridRatCover (μ : ℚ) (squares : Fin 6 → RotatedSquare) : Prop where
  bottom : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (q, 0)
  top : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (q, 2 * μ)
  left : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (0, q)
  right : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (2 * μ, q)
  hMid : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (q, μ)
  vMid : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (μ, q)

/-- Every `PointwiseCover` induces a rotated six-line ℚ cover (no axis-align). -/
theorem RotatedGridRatCover_of_pointwise (T : Target) (cov : PointwiseCover T) :
    RotatedGridRatCover T.μ cov.squares where
  bottom := fun q hq0 hq1 => cov.covers (q, 0) (grid_point_in_target_bottom T q hq0 hq1)
  top := fun q hq0 hq1 => cov.covers (q, 2 * T.μ) (grid_point_in_target_top T q hq0 hq1)
  left := fun q hq0 hq1 => cov.covers (0, q) (grid_point_in_target_left T q hq0 hq1)
  right := fun q hq0 hq1 => cov.covers (2 * T.μ, q) (grid_point_in_target_right T q hq0 hq1)
  hMid := fun q hq0 hq1 => cov.covers (q, T.μ) (grid_point_in_target_hMid T q hq0 hq1)
  vMid := fun q hq0 hq1 => cov.covers (T.μ, q) (grid_point_in_target_vMid T q hq0 hq1)

theorem AxisGridRatCover_of_rotated_axis (μ : ℚ) (squares : Fin 6 → RotatedSquare)
    (H : RotatedGridRatCover μ squares)
    (halign : ∀ i, isAxisAligned (squares i)) :
    AxisGridRatCover μ (fun i => toAxisSquare (squares i)) where
  bottom := by
    intro q hq0 hq1
    rcases H.bottom q hq0 hq1 with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (squares i) (halign i) (q, 0)).mp hi⟩
  top := by
    intro q hq0 hq1
    rcases H.top q hq0 hq1 with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (squares i) (halign i) (q, 2 * μ)).mp hi⟩
  left := by
    intro q hq0 hq1
    rcases H.left q hq0 hq1 with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (squares i) (halign i) (0, q)).mp hi⟩
  right := by
    intro q hq0 hq1
    rcases H.right q hq0 hq1 with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (squares i) (halign i) (2 * μ, q)).mp hi⟩
  hMid := by
    intro q hq0 hq1
    rcases H.hMid q hq0 hq1 with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (squares i) (halign i) (q, μ)).mp hi⟩
  vMid := by
    intro q hq0 hq1
    rcases H.vMid q hq0 hq1 with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (squares i) (halign i) (μ, q)).mp hi⟩

theorem AxisGridRatCover_of_pointwise_via_rotated (T : Target) (cov : PointwiseCover T)
    (halign : ∀ i, isAxisAligned (cov.squares i)) :
    AxisGridRatCover T.μ (axisSquaresOf cov) := by
  have H := RotatedGridRatCover_of_pointwise T cov
  have h := AxisGridRatCover_of_rotated_axis T.μ cov.squares H halign
  unfold axisSquaresOf
  exact h

def meetsHoriz (g : RotatedSquare) (Y : ℚ) : Prop :=
  ∃ x : ℚ, RotatedSquare.contains g (x, Y)

def meetsVert (g : RotatedSquare) (X : ℚ) : Prop :=
  ∃ y : ℚ, RotatedSquare.contains g (X, y)

theorem meetsHoriz_of_contains (g : RotatedSquare) (x Y : ℚ)
    (h : RotatedSquare.contains g (x, Y)) : meetsHoriz g Y := ⟨x, h⟩

theorem meetsVert_of_contains (g : RotatedSquare) (X y : ℚ)
    (h : RotatedSquare.contains g (X, y)) : meetsVert g X := ⟨y, h⟩

theorem ratCover_bottom_meets (μ : ℚ) (squares : Fin 6 → RotatedSquare)
    (H : RotatedGridRatCover μ squares) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 2 * μ) :
    ∃ i, meetsHoriz (squares i) 0 := by
  rcases H.bottom q hq0 hq1 with ⟨i, hi⟩
  exact ⟨i, meetsHoriz_of_contains _ q 0 hi⟩

/-- Open residual: export a `RotatedChordLinePackage` from covers (Euclidean chords). -/
def RotatedChordLinePackageExport : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        Nonempty (RotatedChordLinePackage T.μ)

theorem RotatedChordCoverIneq_of_linePackageExport (h : RotatedChordLinePackageExport) :
    RotatedChordCoverIneq :=
  RotatedChordCoverIneq_of_linePackage h

def rotatedGridRatCoverClosed : Bool := true
theorem rotatedGridRatCoverClosed_true : rotatedGridRatCoverClosed = true := rfl

def rotatedChordLinePackageExportProved : Bool := false
theorem rotatedChordLinePackageExportProved_false :
    rotatedChordLinePackageExportProved = false := rfl

def rotatedChordCoverIneqProved : Bool := false
theorem rotatedChordCoverIneqProved_false : rotatedChordCoverIneqProved = false := rfl

/-! ## Euclidean chord extents + six-line measure-lift packaging -/

open S6.IntervalCover1D
open MeasureTheory Set

theorem horiz_chord_sq_le_two (g : RotatedSquare) (Y x1 x2 : ℚ)
    (h1 : RotatedSquare.contains g (x1, Y))
    (h2 : RotatedSquare.contains g (x2, Y)) :
    (x1 - x2) * (x1 - x2) ≤ 2 := by
  have h := chord_distSq_le_two g (x1, Y) (x2, Y) h1 h2
  simp only [distSq] at h
  nlinarith

theorem vert_chord_sq_le_two (g : RotatedSquare) (X y1 y2 : ℚ)
    (h1 : RotatedSquare.contains g (X, y1))
    (h2 : RotatedSquare.contains g (X, y2)) :
    (y1 - y2) * (y1 - y2) ≤ 2 := by
  have h := chord_distSq_le_two g (X, y1) (X, y2) h1 h2
  simp only [distSq] at h
  nlinarith

/-- Horizontal chord length (absolute) ≤ 2 via diameter `distSq ≤ 2`. -/
theorem abs_horiz_chord_le_two (g : RotatedSquare) (Y x1 x2 : ℚ)
    (h1 : RotatedSquare.contains g (x1, Y))
    (h2 : RotatedSquare.contains g (x2, Y)) :
    |x1 - x2| ≤ 2 := by
  have hsq := horiz_chord_sq_le_two g Y x1 x2 h1 h2
  have hnn : 0 ≤ |x1 - x2| := abs_nonneg _
  have : |x1 - x2| * |x1 - x2| ≤ (2 : ℚ) * 2 := by
    have : |x1 - x2| * |x1 - x2| = (x1 - x2) * (x1 - x2) := by
      simp [abs_mul_abs_self]
    linarith
  nlinarith

theorem abs_vert_chord_le_two (g : RotatedSquare) (X y1 y2 : ℚ)
    (h1 : RotatedSquare.contains g (X, y1))
    (h2 : RotatedSquare.contains g (X, y2)) :
    |y1 - y2| ≤ 2 := by
  have hsq := vert_chord_sq_le_two g X y1 y2 h1 h2
  have : |y1 - y2| * |y1 - y2| = (y1 - y2) * (y1 - y2) := by
    simp [abs_mul_abs_self]
  nlinarith

/-- One target line covered by six Euclidean chord intervals of length ≤ 2. -/
structure RotatedLineChordCover (μ : ℚ) where
  lo : Fin 6 → ℝ
  hi : Fin 6 → ℝ
  hle : ∀ i, lo i ≤ hi i
  hchord_le_two : ∀ i, hi i - lo i ≤ 2
  hcover : Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, Icc (lo i) (hi i)

theorem RotatedLineChordCover.sum_ge {μ : ℚ} (hμ : 1 < μ)
    (C : RotatedLineChordCover μ) :
    (2 : ℝ) * μ ≤ ∑ i : Fin 6, (C.hi i - C.lo i) := by
  have hab : (0 : ℝ) ≤ (2 : ℝ) * μ := by exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  simpa using cover_Icc_sum_diff (0 : ℝ) ((2 : ℝ) * μ) hab C.lo C.hi C.hle C.hcover

theorem RotatedLineChordCover.sum_le_twelve {μ : ℚ} (C : RotatedLineChordCover μ) :
    ∑ i : Fin 6, (C.hi i - C.lo i) ≤ (12 : ℝ) := by
  have hbound : ∀ i ∈ (Finset.univ : Finset (Fin 6)), C.hi i - C.lo i ≤ (2 : ℝ) :=
    fun i _ => C.hchord_le_two i
  have hsum := Finset.sum_le_sum hbound
  have hconst : ∑ _i : Fin 6, (2 : ℝ) = 12 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  linarith

/-- Proved (v0.21): lift bottom line of `RotatedGridRatCover` to a Euclidean interval cover. -/
def RotatedLineMeasureLift : Prop :=
  ∀ (μ : ℚ), 1 < μ → ∀ (squares : Fin 6 → RotatedSquare),
    RotatedGridRatCover μ squares → Nonempty (RotatedLineChordCover μ)

/-- Open: G5 k=0 cover exports a six-line chord matrix with per-square total ≤ 2. -/
def RotatedSixLineMeasureLift : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ (M : SixLineChordMatrix),
          M.μ = T.μ ∧ (∀ i, M.squareTotal i ≤ 2)

theorem G5k0Bridge_of_sixLineMeasureLift (h : RotatedSixLineMeasureLift) :
    G5k0Bridge := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨M, hμEq, hub⟩
  have hμ : 1 < M.μ := by simpa [hμEq] using T.hμ
  exact False.elim (M.impossible_of_square_ub hμ hub)

theorem RotatedChordBoundPackage_of_sixLineMeasureLift (h : RotatedSixLineMeasureLift) :
    RotatedChordBoundPackage := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨M, hμEq, hub⟩
  have hμ : 1 < M.μ := by simpa [hμEq] using T.hμ
  exact (M.impossible_of_square_ub hμ hub).elim

theorem RotatedChordCoverIneq_of_sixLineMeasureLift (h : RotatedSixLineMeasureLift) :
    RotatedChordCoverIneq :=
  RotatedChordBoundPackage_of_sixLineMeasureLift h

theorem G5k0GeomExport_of_sixLineMeasureLift (h : RotatedSixLineMeasureLift) :
    G5k0GeomExport :=
  G5k0GeomExport_of_rotatedChordExport
    (RotatedG5k0ChordExport_of_boundPackage
      (RotatedChordBoundPackage_of_sixLineMeasureLift h))

theorem RotatedChordLinePackageExport_of_sixLineMeasureLift
    (h : RotatedSixLineMeasureLift) : RotatedChordLinePackageExport := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨M, hμEq, hub⟩
  have hμ : 1 < M.μ := by simpa [hμEq] using T.hμ
  exact (M.impossible_of_square_ub hμ hub).elim

def rotatedHorizVertChordClosed : Bool := true
theorem rotatedHorizVertChordClosed_true : rotatedHorizVertChordClosed = true := rfl

def rotatedLineChordCoverAlgebraClosed : Bool := true
theorem rotatedLineChordCoverAlgebraClosed_true :
    rotatedLineChordCoverAlgebraClosed = true := rfl

def rotatedSixLineMeasureLiftProved : Bool := false
theorem rotatedSixLineMeasureLiftProved_false :
    rotatedSixLineMeasureLiftProved = false := rfl

def rotatedLineMeasureLiftProved : Bool := true
theorem rotatedLineMeasureLiftProved_true : rotatedLineMeasureLiftProved = true := rfl


/-! ## Corner diameter-miss + one-sided axial sum (toward squareTotal ≤ 2) -/

/-- Point at height `2μ` cannot share a unit square with the SW corner when `μ > 1`. -/
theorem contains_SW_misses_top (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 0)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, 2 * μ) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 0) (x, 2 * μ) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg x, hμ]

theorem contains_SW_misses_right (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 0)) (y : ℚ) :
    ¬ RotatedSquare.contains g (2 * μ, y) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 0) (2 * μ, y) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg y, hμ]

theorem contains_SE_misses_top (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 0)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, 2 * μ) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 0) (x, 2 * μ) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg (x - 2 * μ), hμ]

theorem contains_SE_misses_left (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 0)) (y : ℚ) :
    ¬ RotatedSquare.contains g (0, y) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 0) (0, y) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg y, hμ]

theorem contains_NE_misses_bottom (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 2 * μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, 0) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 2 * μ) (x, 0) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg (x - 2 * μ), hμ]

theorem contains_NE_misses_left (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 2 * μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (0, y) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 2 * μ) (0, y) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg (y - 2 * μ), hμ]

theorem contains_NW_misses_bottom (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 2 * μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, 0) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 2 * μ) (x, 0) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg x, hμ]

theorem contains_NW_misses_right (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 2 * μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (2 * μ, y) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 2 * μ) (2 * μ, y) h ht
  simp only [distSq] at hd
  nlinarith [sq_nonneg (y - 2 * μ), hμ]

/-- Nonnegative axial extents with squared sum ≤ 2 ⇒ sum ≤ 2. -/
theorem onesided_axial_sum_le_two (xb yb : ℚ) (hx : 0 ≤ xb) (hy : 0 ≤ yb)
    (hsq : xb * xb + yb * yb ≤ 2) : xb + yb ≤ 2 := by
  have hamg : 2 * xb * yb ≤ xb * xb + yb * yb := by
    nlinarith [sq_nonneg (xb - yb)]
  nlinarith

theorem SW_onesided_axial_sum_le_two (g : RotatedSquare) (xb yb : ℚ)
    (_h0 : RotatedSquare.contains g (0, 0))
    (hb : RotatedSquare.contains g (xb, 0))
    (hl : RotatedSquare.contains g (0, yb))
    (hx : 0 ≤ xb) (hy : 0 ≤ yb) : xb + yb ≤ 2 := by
  have hd := chord_distSq_le_two g (xb, 0) (0, yb) hb hl
  simp only [distSq] at hd
  exact onesided_axial_sum_le_two xb yb hx hy (by nlinarith)

theorem SE_onesided_axial_sum_le_two (g : RotatedSquare) (μ xb yb : ℚ)
    (_h0 : RotatedSquare.contains g (2 * μ, 0))
    (hb : RotatedSquare.contains g (2 * μ - xb, 0))
    (hr : RotatedSquare.contains g (2 * μ, yb))
    (hx : 0 ≤ xb) (hy : 0 ≤ yb) : xb + yb ≤ 2 := by
  have hd := chord_distSq_le_two g (2 * μ - xb, 0) (2 * μ, yb) hb hr
  simp only [distSq] at hd
  exact onesided_axial_sum_le_two xb yb hx hy (by nlinarith)

theorem NE_onesided_axial_sum_le_two (g : RotatedSquare) (μ xb yb : ℚ)
    (_h0 : RotatedSquare.contains g (2 * μ, 2 * μ))
    (ht : RotatedSquare.contains g (2 * μ - xb, 2 * μ))
    (hr : RotatedSquare.contains g (2 * μ, 2 * μ - yb))
    (hx : 0 ≤ xb) (hy : 0 ≤ yb) : xb + yb ≤ 2 := by
  have hd := chord_distSq_le_two g (2 * μ - xb, 2 * μ) (2 * μ, 2 * μ - yb) ht hr
  simp only [distSq] at hd
  exact onesided_axial_sum_le_two xb yb hx hy (by nlinarith)


theorem NW_onesided_axial_sum_le_two (g : RotatedSquare) (μ xb yb : ℚ)
    (_h0 : RotatedSquare.contains g (0, 2 * μ))
    (ht : RotatedSquare.contains g (xb, 2 * μ))
    (hl : RotatedSquare.contains g (0, 2 * μ - yb))
    (hx : 0 ≤ xb) (hy : 0 ≤ yb) : xb + yb ≤ 2 := by
  have hd := chord_distSq_le_two g (xb, 2 * μ) (0, 2 * μ - yb) ht hl
  simp only [distSq] at hd
  exact onesided_axial_sum_le_two xb yb hx hy (by nlinarith)

theorem meetsHoriz_SW_not_top (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 0)) : ¬ meetsHoriz g (2 * μ) := by
  rintro ⟨x, hx⟩; exact contains_SW_misses_top g μ hμ h x hx

theorem meetsVert_SW_not_right (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 0)) : ¬ meetsVert g (2 * μ) := by
  rintro ⟨y, hy⟩; exact contains_SW_misses_right g μ hμ h y hy

theorem meetsHoriz_SE_not_top (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 0)) : ¬ meetsHoriz g (2 * μ) := by
  rintro ⟨x, hx⟩; exact contains_SE_misses_top g μ hμ h x hx

theorem meetsVert_SE_not_left (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 0)) : ¬ meetsVert g 0 := by
  rintro ⟨y, hy⟩; exact contains_SE_misses_left g μ hμ h y hy

theorem meetsHoriz_NE_not_bottom (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 2 * μ)) : ¬ meetsHoriz g 0 := by
  rintro ⟨x, hx⟩; exact contains_NE_misses_bottom g μ hμ h x hx

theorem meetsVert_NE_not_left (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (2 * μ, 2 * μ)) : ¬ meetsVert g 0 := by
  rintro ⟨y, hy⟩; exact contains_NE_misses_left g μ hμ h y hy

theorem meetsHoriz_NW_not_bottom (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 2 * μ)) : ¬ meetsHoriz g 0 := by
  rintro ⟨x, hx⟩; exact contains_NW_misses_bottom g μ hμ h x hx

theorem meetsVert_NW_not_right (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : RotatedSquare.contains g (0, 2 * μ)) : ¬ meetsVert g (2 * μ) := by
  rintro ⟨y, hy⟩; exact contains_NW_misses_right g μ hμ h y hy

/-- Every `PointwiseCover`'s corner owners miss the opposite outer sides (`μ>1`). -/
theorem PointwiseCover_corner_diameter_miss {T : Target} (cov : PointwiseCover T) :
    let C := cov.toCornerOwners
    (¬ meetsHoriz (C.squares C.i1) (2 * T.μ)) ∧
      (¬ meetsVert (C.squares C.i1) (2 * T.μ)) ∧
      (¬ meetsHoriz (C.squares C.i2) (2 * T.μ)) ∧
      (¬ meetsVert (C.squares C.i2) 0) ∧
      (¬ meetsHoriz (C.squares C.i3) 0) ∧
      (¬ meetsVert (C.squares C.i3) 0) ∧
      (¬ meetsHoriz (C.squares C.i4) 0) ∧
      (¬ meetsVert (C.squares C.i4) (2 * T.μ)) := by
  intro C
  have hμ := T.hμ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact meetsHoriz_SW_not_top _ T.μ hμ (by simpa [Target.v1] using C.h1)
  · exact meetsVert_SW_not_right _ T.μ hμ (by simpa [Target.v1] using C.h1)
  · exact meetsHoriz_SE_not_top _ T.μ hμ (by simpa [Target.v2] using C.h2)
  · exact meetsVert_SE_not_left _ T.μ hμ (by simpa [Target.v2] using C.h2)
  · exact meetsHoriz_NE_not_bottom _ T.μ hμ (by simpa [Target.v3] using C.h3)
  · exact meetsVert_NE_not_left _ T.μ hμ (by simpa [Target.v3] using C.h3)
  · exact meetsHoriz_NW_not_bottom _ T.μ hμ (by simpa [Target.v4] using C.h4)
  · exact meetsVert_NW_not_right _ T.μ hμ (by simpa [Target.v4] using C.h4)

theorem corner_onesided_sums_of_samples (gSW gSE gNE gNW : RotatedSquare) (μ : ℚ)
    (hSW : RotatedSquare.contains gSW (0, 0))
    (hSE : RotatedSquare.contains gSE (2 * μ, 0))
    (hNE : RotatedSquare.contains gNE (2 * μ, 2 * μ))
    (hNW : RotatedSquare.contains gNW (0, 2 * μ))
    (bSW lSW bSE rSE tNE rNE tNW lNW : ℚ)
    (hbSW : RotatedSquare.contains gSW (bSW, 0))
    (hlSW : RotatedSquare.contains gSW (0, lSW))
    (hbSE : RotatedSquare.contains gSE (2 * μ - bSE, 0))
    (hrSE : RotatedSquare.contains gSE (2 * μ, rSE))
    (htNE : RotatedSquare.contains gNE (2 * μ - tNE, 2 * μ))
    (hrNE : RotatedSquare.contains gNE (2 * μ, 2 * μ - rNE))
    (htNW : RotatedSquare.contains gNW (tNW, 2 * μ))
    (hlNW : RotatedSquare.contains gNW (0, 2 * μ - lNW))
    (hnn : 0 ≤ bSW ∧ 0 ≤ lSW ∧ 0 ≤ bSE ∧ 0 ≤ rSE ∧
      0 ≤ tNE ∧ 0 ≤ rNE ∧ 0 ≤ tNW ∧ 0 ≤ lNW) :
    bSW + lSW ≤ 2 ∧ bSE + rSE ≤ 2 ∧ tNE + rNE ≤ 2 ∧ tNW + lNW ≤ 2 :=
  ⟨SW_onesided_axial_sum_le_two gSW bSW lSW hSW hbSW hlSW hnn.1 hnn.2.1,
    SE_onesided_axial_sum_le_two gSE μ bSE rSE hSE hbSE hrSE hnn.2.2.1 hnn.2.2.2.1,
    NE_onesided_axial_sum_le_two gNE μ tNE rNE hNE htNE hrNE hnn.2.2.2.2.1 hnn.2.2.2.2.2.1,
    NW_onesided_axial_sum_le_two gNW μ tNW lNW hNW htNW hlNW
      hnn.2.2.2.2.2.2.1 hnn.2.2.2.2.2.2.2⟩

def SixLineChordMatrix.mk' (μ : ℚ) (chord : Fin 6 → Fin 6 → ℚ)
    (nonneg : ∀ ℓ i, 0 ≤ chord ℓ i)
    (lineCover : ∀ ℓ, (2 : ℚ) * μ ≤ sum6 (fun i => chord ℓ i)) :
    SixLineChordMatrix :=
  ⟨μ, chord, nonneg, lineCover⟩

/-- Open: export chord table with line covers + squareTotal ≤ 2. -/
def RotatedChordMatrixExport : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ (chord : Fin 6 → Fin 6 → ℚ),
          (∀ ℓ i, 0 ≤ chord ℓ i) ∧
          (∀ ℓ, (2 : ℚ) * T.μ ≤ sum6 (fun i => chord ℓ i)) ∧
          (∀ i, sum6 (fun ℓ => chord ℓ i) ≤ 2)

theorem RotatedSixLineMeasureLift_of_chordMatrixExport
    (h : RotatedChordMatrixExport) : RotatedSixLineMeasureLift := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨chord, hnn, hline, hub⟩
  refine ⟨SixLineChordMatrix.mk' T.μ chord hnn hline, rfl, ?_⟩
  intro i
  simpa [SixLineChordMatrix.squareTotal, SixLineChordMatrix.mk'] using hub i

theorem G5k0Bridge_of_chordMatrixExport (h : RotatedChordMatrixExport) : G5k0Bridge :=
  G5k0Bridge_of_sixLineMeasureLift (RotatedSixLineMeasureLift_of_chordMatrixExport h)

theorem RotatedChordCoverIneq_of_chordMatrixExport (h : RotatedChordMatrixExport) :
    RotatedChordCoverIneq :=
  RotatedChordCoverIneq_of_sixLineMeasureLift
    (RotatedSixLineMeasureLift_of_chordMatrixExport h)

def rotatedCornerDiameterMissClosed : Bool := true
theorem rotatedCornerDiameterMissClosed_true :
    rotatedCornerDiameterMissClosed = true := rfl

def rotatedOnesidedAxialSumClosed : Bool := true
theorem rotatedOnesidedAxialSumClosed_true : rotatedOnesidedAxialSumClosed = true := rfl

def pointwiseCoverCornerDiameterMissClosed : Bool := true
theorem pointwiseCoverCornerDiameterMissClosed_true :
    pointwiseCoverCornerDiameterMissClosed = true := rfl

def rotatedChordMatrixExportProved : Bool := false
theorem rotatedChordMatrixExportProved_false :
    rotatedChordMatrixExportProved = false := rfl


/-! ## Axis path inhabits ChordMatrixExport / bottom LineChordCover -/

open S6.AxisGridContribution
open S6.AxisG5k0FromCover
open S6.OwnershipBridge (AxisSquare)
open Set

theorem sum6_eq_sum (f : Fin 6 → ℚ) : sum6 f = ∑ i : Fin 6, f i := by
  simp only [sum6]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp; ring

theorem axisGridContrib_le_two_of_roles {μ : ℚ} {squares : Fin 6 → AxisSquare}
    (R : AxisG5k0Roles μ squares) (k : Fin 6) :
    axisGridContrib (squares k) μ ≤ 2 := by
  have hμ := R.hμ
  rw [axisGridContrib_eq_outer_mid]
  rcases R.hpart k with hk | hk | hk | hk | hk | hk
  · subst hk
    have hm : midContrib (squares R.iSW) μ = 0 :=
      R.onlyFillers R.iSW R.hj1SW.symm R.hj2SW.symm
    have ho := axis_contains_origin_outer_le_two (squares R.iSW) μ hμ R.hSW
    simp only [outerContrib, midContrib] at ho hm ⊢
    linarith
  · subst hk
    have hm : midContrib (squares R.iSE) μ = 0 :=
      R.onlyFillers R.iSE R.hj1SE.symm R.hj2SE.symm
    have ho := axis_contains_se_outer_le_two (squares R.iSE) μ hμ R.hSE
    simp only [outerContrib, midContrib] at ho hm ⊢
    linarith
  · subst hk
    have hm : midContrib (squares R.iNE) μ = 0 :=
      R.onlyFillers R.iNE R.hj1NE.symm R.hj2NE.symm
    have ho := axis_contains_ne_outer_le_two (squares R.iNE) μ hμ R.hNE
    simp only [outerContrib, midContrib] at ho hm ⊢
    linarith
  · subst hk
    have hm : midContrib (squares R.iNW) μ = 0 :=
      R.onlyFillers R.iNW R.hj1NW.symm R.hj2NW.symm
    have ho := axis_contains_nw_outer_le_two (squares R.iNW) μ hμ R.hNW
    simp only [outerContrib, midContrib] at ho hm ⊢
    linarith
  · subst hk
    have ho : outerContrib (squares R.j1) μ = 0 :=
      R.onlyOwners R.j1 R.hj1SW R.hj1SE R.hj1NE R.hj1NW
    have hm := axis_mid_sum_le_two (squares R.j1) μ hμ
    simp only [outerContrib, midContrib] at ho hm ⊢
    linarith
  · subst hk
    have ho : outerContrib (squares R.j2) μ = 0 :=
      R.onlyOwners R.j2 R.hj2SW R.hj2SE R.hj2NE R.hj2NW
    have hm := axis_mid_sum_le_two (squares R.j2) μ hμ
    simp only [outerContrib, midContrib] at ho hm ⊢
    linarith

def axisSixLineChord (squares : Fin 6 → AxisSquare) (μ : ℚ) : Fin 6 → Fin 6 → ℚ
  | ⟨0, _⟩, i => bottomLen (squares i) μ
  | ⟨1, _⟩, i => topLen (squares i) μ
  | ⟨2, _⟩, i => leftLen (squares i) μ
  | ⟨3, _⟩, i => rightLen (squares i) μ
  | ⟨4, _⟩, i => hMidLen (squares i) μ
  | ⟨5, _⟩, i => vMidLen (squares i) μ

theorem axisSixLineChord_nonneg (squares : Fin 6 → AxisSquare) (μ : ℚ) (ℓ i : Fin 6) :
    0 ≤ axisSixLineChord squares μ ℓ i := by
  fin_cases ℓ
  · exact bottomLen_nonneg _ _
  · exact len_nonneg_top _ _
  · exact len_nonneg_left _ _
  · exact len_nonneg_right _ _
  · exact len_nonneg_hMid _ _
  · exact len_nonneg_vMid _ _

theorem axisSixLineChord_square_sum (squares : Fin 6 → AxisSquare) (μ : ℚ) (i : Fin 6) :
    sum6 (fun ℓ => axisSixLineChord squares μ ℓ i) = axisGridContrib (squares i) μ := by
  simp only [sum6, axisSixLineChord, axisGridContrib]

theorem axisSixLine_lineCover (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridLineCover μ squares) (ℓ : Fin 6) :
    (2 : ℚ) * μ ≤ sum6 (fun i => axisSixLineChord squares μ ℓ i) := by
  fin_cases ℓ
  · have hQ : (2 : ℚ) * μ ≤ ∑ i : Fin 6, bottomLen (squares i) μ := by
      exact_mod_cast H.bottom_sum hμ
    simpa [sum6_eq_sum, axisSixLineChord] using hQ
  · have hQ : (2 : ℚ) * μ ≤ ∑ i : Fin 6, topLen (squares i) μ := by
      exact_mod_cast H.top_sum hμ
    simpa [sum6_eq_sum, axisSixLineChord] using hQ
  · have hQ : (2 : ℚ) * μ ≤ ∑ i : Fin 6, leftLen (squares i) μ := by
      exact_mod_cast H.left_sum hμ
    simpa [sum6_eq_sum, axisSixLineChord] using hQ
  · have hQ : (2 : ℚ) * μ ≤ ∑ i : Fin 6, rightLen (squares i) μ := by
      exact_mod_cast H.right_sum hμ
    simpa [sum6_eq_sum, axisSixLineChord] using hQ
  · have hQ : (2 : ℚ) * μ ≤ ∑ i : Fin 6, hMidLen (squares i) μ := by
      exact_mod_cast H.hMid_sum hμ
    simpa [sum6_eq_sum, axisSixLineChord] using hQ
  · have hQ : (2 : ℚ) * μ ≤ ∑ i : Fin 6, vMidLen (squares i) μ := by
      exact_mod_cast H.vMid_sum hμ
    simpa [sum6_eq_sum, axisSixLineChord] using hQ

theorem RotatedChordMatrixExport_of_axisCoverBridge (h : AxisG5k0CoverBridge) :
    RotatedChordMatrixExport := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨squares, Hrat, ⟨R⟩⟩
  have Hline := AxisGridLineCover_of_ratCover T.μ R.hμ squares Hrat
  refine ⟨axisSixLineChord squares T.μ, ?_, ?_, ?_⟩
  · intro ℓ i; exact axisSixLineChord_nonneg squares T.μ ℓ i
  · intro ℓ; exact axisSixLine_lineCover T.μ R.hμ squares Hline ℓ
  · intro i
    rw [axisSixLineChord_square_sum]
    exact axisGridContrib_le_two_of_roles R i

theorem RotatedChordMatrixExport_of_axisRealisation (h : AxisAlignedG5k0Realisation) :
    RotatedChordMatrixExport :=
  RotatedChordMatrixExport_of_axisCoverBridge (AxisG5k0CoverBridge_of_axisRealisation h)

theorem RotatedSixLineMeasureLift_of_axisCoverBridge (h : AxisG5k0CoverBridge) :
    RotatedSixLineMeasureLift :=
  RotatedSixLineMeasureLift_of_chordMatrixExport
    (RotatedChordMatrixExport_of_axisCoverBridge h)

/-- Clamped bottom chord endpoints (empty / inverted → `{0}`). -/
noncomputable def axisBottomChordLo (s : AxisSquare) (μ : ℚ) : ℝ :=
  if s.y ≤ 0 ∧ 0 ≤ s.y + 1 then
    let lo := bottomLo s μ
    let hi := bottomHi s μ
    if lo ≤ hi then lo else (0 : ℝ)
  else (0 : ℝ)

noncomputable def axisBottomChordHi (s : AxisSquare) (μ : ℚ) : ℝ :=
  if s.y ≤ 0 ∧ 0 ≤ s.y + 1 then
    let lo := bottomLo s μ
    let hi := bottomHi s μ
    if lo ≤ hi then hi else (0 : ℝ)
  else (0 : ℝ)

theorem axisBottomChord_le (s : AxisSquare) (μ : ℚ) :
    axisBottomChordLo s μ ≤ axisBottomChordHi s μ := by
  dsimp [axisBottomChordLo, axisBottomChordHi]
  split_ifs <;> simp [*]

theorem axisBottomChord_len_le_two (s : AxisSquare) (μ : ℚ) :
    axisBottomChordHi s μ - axisBottomChordLo s μ ≤ 2 := by
  dsimp [axisBottomChordLo, axisBottomChordHi]
  split_ifs with h hle
  · have h1 : bottomHi s μ - bottomLo s μ ≤ 1 := by
      dsimp [bottomLo, bottomHi]
      have := sub_le_sub (min_le_left ((s.x : ℝ) + 1) ((2 : ℝ) * μ))
        (le_max_left (s.x : ℝ) 0)
      linarith
    linarith
  · norm_num
  · norm_num

theorem bottomInterval_subset_chordIcc (s : AxisSquare) (μ : ℚ) :
    bottomInterval s μ ⊆ Icc (axisBottomChordLo s μ) (axisBottomChordHi s μ) := by
  intro x hx
  dsimp [bottomInterval] at hx
  by_cases h : s.y ≤ 0 ∧ 0 ≤ s.y + 1
  · have hx' : x ∈ Icc (bottomLo s μ) (bottomHi s μ) := by
      simpa [h] using hx
    dsimp [axisBottomChordLo, axisBottomChordHi]
    by_cases hle : bottomLo s μ ≤ bottomHi s μ
    · simpa [h, hle] using hx'
    · have : Icc (bottomLo s μ) (bottomHi s μ) = ∅ :=
        Icc_eq_empty_of_lt (lt_of_not_ge hle)
      rw [this] at hx'
      cases hx'
  · simp only [h, ite_false] at hx
    cases hx

theorem RotatedLineChordCover_of_axis_bottom (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, (squares i).contains (q, 0)) :
    Nonempty (RotatedLineChordCover μ) := by
  have hreal := bottom_rat_cover_implies_real μ hμ squares hQ
  refine ⟨{
    lo := fun i => axisBottomChordLo (squares i) μ
    hi := fun i => axisBottomChordHi (squares i) μ
    hle := fun i => axisBottomChord_le (squares i) μ
    hchord_le_two := fun i => axisBottomChord_len_le_two (squares i) μ
    hcover := ?_ }⟩
  intro x hx
  rcases mem_iUnion.mp (hreal hx) with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, bottomInterval_subset_chordIcc (squares i) μ hi⟩

theorem axis_aligned_implies_bottom_lineLift (μ : ℚ) (hμ : 1 < μ)
    (rs : Fin 6 → RotatedSquare)
    (H : RotatedGridRatCover μ rs) (halign : ∀ i, isAxisAligned (rs i)) :
    Nonempty (RotatedLineChordCover μ) := by
  have Hax := AxisGridRatCover_of_rotated_axis μ rs H (fun i => by simpa using (halign i))
  exact RotatedLineChordCover_of_axis_bottom μ hμ (fun i => toAxisSquare (rs i)) Hax.bottom

def axisPathChordMatrixExportClosed : Bool := true
theorem axisPathChordMatrixExportClosed_true :
    axisPathChordMatrixExportClosed = true := rfl

def axisBottomLineChordCoverClosed : Bool := true
theorem axisBottomLineChordCoverClosed_true :
    axisBottomLineChordCoverClosed = true := rfl


/-! ## Real chord slices: general RotatedGridRatCover ⇒ LineMeasureLift -/

open S6.ChordLength (UnitDir)
open S6.RigidMotionChart (inAxisSquare rotateBy)
open S6.ObliqueChart (unitDir_projectedWidth_le_two unitDir_projectedWidth_sq_le_two)
open Set Classical

def rotateInvR (u : UnitDir) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((u.c : ℝ) * p.1 + (u.s : ℝ) * p.2,
    (-(u.s : ℝ)) * p.1 + (u.c : ℝ) * p.2)

def toBodyR (g : RotatedSquare) (p : ℝ × ℝ) : ℝ × ℝ :=
  rotateInvR g.dir (p.1 - (g.shift.1 : ℝ), p.2 - (g.shift.2 : ℝ))

def containsR (g : RotatedSquare) (p : ℝ × ℝ) : Prop :=
  let q := toBodyR g p
  0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1

theorem toBodyR_cast (g : RotatedSquare) (x y : ℚ) :
    toBodyR g ((x : ℝ), (y : ℝ)) =
      (((RotatedSquare.toBody g (x, y)).1 : ℝ),
        ((RotatedSquare.toBody g (x, y)).2 : ℝ)) := by
  apply Prod.ext
  · simp only [toBodyR, rotateInvR, RotatedSquare.toBody, rotateInv, unitDirInv, rotateBy]
    push_cast; ring
  · simp only [toBodyR, rotateInvR, RotatedSquare.toBody, rotateInv, unitDirInv, rotateBy]
    push_cast; ring

theorem contains_implies_containsR (g : RotatedSquare) (x y : ℚ)
    (h : RotatedSquare.contains g (x, y)) :
    containsR g ((x : ℝ), (y : ℝ)) := by
  simp only [containsR, toBodyR_cast]
  simp only [RotatedSquare.contains, inAxisSquare] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1,
    by exact_mod_cast h.2.2.1, by exact_mod_cast h.2.2.2⟩

theorem applyR_x_of_toBodyR (g : RotatedSquare) (x Y : ℝ) :
    x = (g.shift.1 : ℝ) + (g.dir.c : ℝ) * (toBodyR g (x, Y)).1
      - (g.dir.s : ℝ) * (toBodyR g (x, Y)).2 := by
  have hc : (g.dir.c : ℝ) * (g.dir.c : ℝ) + (g.dir.s : ℝ) * (g.dir.s : ℝ) = 1 := by
    exact_mod_cast g.dir.hc
  apply Eq.symm
  simp only [toBodyR, rotateInvR]
  calc
    (g.shift.1 : ℝ) + (g.dir.c : ℝ) *
          ((g.dir.c : ℝ) * (x - (g.shift.1 : ℝ)) + (g.dir.s : ℝ) * (Y - (g.shift.2 : ℝ)))
        - (g.dir.s : ℝ) *
          ((-(g.dir.s : ℝ)) * (x - (g.shift.1 : ℝ)) + (g.dir.c : ℝ) * (Y - (g.shift.2 : ℝ)))
        = (g.shift.1 : ℝ) + ((g.dir.c : ℝ) * (g.dir.c : ℝ) + (g.dir.s : ℝ) * (g.dir.s : ℝ)) *
            (x - (g.shift.1 : ℝ)) := by ring
    _ = (g.shift.1 : ℝ) + 1 * (x - (g.shift.1 : ℝ)) := by rw [hc]
    _ = x := by ring

theorem abs_horiz_delta_containsR (g : RotatedSquare) (Y x₁ x₂ : ℝ)
    (h1 : containsR g (x₁, Y)) (h2 : containsR g (x₂, Y)) :
    |x₁ - x₂| ≤ |(g.dir.c : ℝ)| + |(g.dir.s : ℝ)| := by
  have e1 := applyR_x_of_toBodyR g x₁ Y
  have e2 := applyR_x_of_toBodyR g x₂ Y
  obtain ⟨hu1, hu1b, hv1, hv1b⟩ := h1
  obtain ⟨hu2, hu2b, hv2, hv2b⟩ := h2
  have hdu : |(toBodyR g (x₁, Y)).1 - (toBodyR g (x₂, Y)).1| ≤ 1 := by
    cases' le_total (toBodyR g (x₁, Y)).1 (toBodyR g (x₂, Y)).1 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hdv : |(toBodyR g (x₁, Y)).2 - (toBodyR g (x₂, Y)).2| ≤ 1 := by
    cases' le_total (toBodyR g (x₁, Y)).2 (toBodyR g (x₂, Y)).2 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hEq : x₁ - x₂ =
      (g.dir.c : ℝ) * ((toBodyR g (x₁, Y)).1 - (toBodyR g (x₂, Y)).1)
      - (g.dir.s : ℝ) * ((toBodyR g (x₁, Y)).2 - (toBodyR g (x₂, Y)).2) := by
    linarith
  rw [hEq]
  refine le_trans (abs_sub _ _) ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_of_le_one_right (abs_nonneg (g.dir.c : ℝ)) hdu,
    mul_le_of_le_one_right (abs_nonneg (g.dir.s : ℝ)) hdv]

theorem abs_horiz_delta_containsR_le_two (g : RotatedSquare) (Y x₁ x₂ : ℝ)
    (h1 : containsR g (x₁, Y)) (h2 : containsR g (x₂, Y)) :
    |x₁ - x₂| ≤ 2 :=
  (abs_horiz_delta_containsR g Y x₁ x₂ h1 h2).trans
    (by exact_mod_cast unitDir_projectedWidth_le_two g.dir)

def horizSliceR (g : RotatedSquare) (Y : ℚ) : Set ℝ :=
  {x | containsR g (x, (Y : ℝ))}

theorem mem_horizSliceR_of_contains (g : RotatedSquare) (Y x : ℚ)
    (h : RotatedSquare.contains g (x, Y)) :
    (x : ℝ) ∈ horizSliceR g Y :=
  contains_implies_containsR g x Y h

theorem horizSliceR_isClosed (g : RotatedSquare) (Y : ℚ) :
    IsClosed (horizSliceR g Y) := by
  let f1 : ℝ → ℝ := fun x => (toBodyR g (x, (Y : ℝ))).1
  let f2 : ℝ → ℝ := fun x => (toBodyR g (x, (Y : ℝ))).2
  have hf1 : Continuous f1 := by simp only [f1, toBodyR, rotateInvR]; continuity
  have hf2 : Continuous f2 := by simp only [f2, toBodyR, rotateInvR]; continuity
  have hEq : horizSliceR g Y =
      {x | 0 ≤ f1 x} ∩ {x | f1 x ≤ 1} ∩ {x | 0 ≤ f2 x} ∩ {x | f2 x ≤ 1} := by
    ext x; simp [horizSliceR, containsR, f1, f2]; tauto
  rw [hEq]
  exact (((isClosed_le continuous_const hf1).inter (isClosed_le hf1 continuous_const)).inter
    (isClosed_le continuous_const hf2)).inter (isClosed_le hf2 continuous_const)

theorem horizSliceR_bddBelow (g : RotatedSquare) (Y : ℚ)
    (hne : (horizSliceR g Y).Nonempty) : BddBelow (horizSliceR g Y) := by
  obtain ⟨x0, hx0⟩ := hne
  refine ⟨x0 - 2, fun y hy => ?_⟩
  have hd := abs_horiz_delta_containsR_le_two g Y x0 y hx0 hy
  cases' abs_cases (x0 - y) with h' h' <;> linarith

theorem horizSliceR_bddAbove (g : RotatedSquare) (Y : ℚ)
    (hne : (horizSliceR g Y).Nonempty) : BddAbove (horizSliceR g Y) := by
  obtain ⟨x0, hx0⟩ := hne
  refine ⟨x0 + 2, fun y hy => ?_⟩
  have hd := abs_horiz_delta_containsR_le_two g Y x0 y hx0 hy
  cases' abs_cases (x0 - y) with h' h' <;> linarith

noncomputable def horizChordLo (g : RotatedSquare) (Y : ℚ) : ℝ :=
  if _hne : (horizSliceR g Y).Nonempty then sInf (horizSliceR g Y) else 0

noncomputable def horizChordHi (g : RotatedSquare) (Y : ℚ) : ℝ :=
  if _hne : (horizSliceR g Y).Nonempty then sSup (horizSliceR g Y) else 0

theorem horizChord_le (g : RotatedSquare) (Y : ℚ) :
    horizChordLo g Y ≤ horizChordHi g Y := by
  dsimp [horizChordLo, horizChordHi]
  split_ifs with hne
  · exact csInf_le_csSup hne (horizSliceR_bddBelow g Y hne) (horizSliceR_bddAbove g Y hne)
  · rfl

theorem horizChord_len_le_two (g : RotatedSquare) (Y : ℚ) :
    horizChordHi g Y - horizChordLo g Y ≤ 2 := by
  dsimp [horizChordLo, horizChordHi]
  split_ifs with hne
  · have hs : sSup (horizSliceR g Y) ≤ sInf (horizSliceR g Y) + 2 := by
      apply csSup_le hne
      intro x hx
      have : x - 2 ≤ sInf (horizSliceR g Y) := by
        apply le_csInf hne
        intro y hy
        have hd := abs_horiz_delta_containsR_le_two g Y x y hx hy
        cases' abs_cases (x - y) with h' h' <;> linarith
      linarith
    linarith
  · norm_num

theorem slice_subset_chordIcc (g : RotatedSquare) (Y : ℚ) :
    horizSliceR g Y ⊆ Icc (horizChordLo g Y) (horizChordHi g Y) := by
  intro x hx
  have hne : (horizSliceR g Y).Nonempty := ⟨x, hx⟩
  dsimp [horizChordLo, horizChordHi]
  simp only [hne, mem_Icc]
  exact ⟨csInf_le (horizSliceR_bddBelow g Y hne) hx,
    le_csSup (horizSliceR_bddAbove g Y hne) hx⟩

theorem horizSliceUnion_isClosed (squares : Fin 6 → RotatedSquare) (Y : ℚ) :
    IsClosed (⋃ i, horizSliceR (squares i) Y) :=
  isClosed_iUnion_of_finite (fun i => horizSliceR_isClosed (squares i) Y)

theorem bottom_rotated_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → RotatedSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (q, 0)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆ ⋃ i, Icc (horizChordLo (squares i) 0) (horizChordHi (squares i) 0) := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  have hslice : Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) ⊆ ⋃ i, horizSliceR (squares i) 0 := by
    refine Icc_subset_of_closed_of_rats _ (horizSliceUnion_isClosed squares 0) (2 * μ) hL ?_
    intro q hq0 hqL
    rcases hQ q hq0 hqL with ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, mem_horizSliceR_of_contains _ 0 q hi⟩
  intro x hx
  rcases mem_iUnion.mp (hslice hx) with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, slice_subset_chordIcc (squares i) 0 hi⟩

theorem RotatedLineChordCover_of_rotated_bottom (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → RotatedSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (q, 0)) :
    Nonempty (RotatedLineChordCover μ) := by
  have hreal := bottom_rotated_rat_cover_implies_real μ hμ squares hQ
  exact ⟨{
    lo := fun i => horizChordLo (squares i) 0
    hi := fun i => horizChordHi (squares i) 0
    hle := fun i => horizChord_le (squares i) 0
    hchord_le_two := fun i => horizChord_len_le_two (squares i) 0
    hcover := hreal }⟩

theorem RotatedLineMeasureLift_of_ratCover_bottom : RotatedLineMeasureLift := by
  intro μ hμ squares H
  exact RotatedLineChordCover_of_rotated_bottom μ hμ squares H.bottom

theorem rotatedLineMeasureLift_held : RotatedLineMeasureLift :=
  RotatedLineMeasureLift_of_ratCover_bottom

def rotatedRealChordSliceClosed : Bool := true
theorem rotatedRealChordSliceClosed_true : rotatedRealChordSliceClosed = true := rfl


/-! ## Six-line real lift + parallel miss (toward general ChordMatrixExport) -/

open S6.ObliqueChart (unitDir_projectedWidth_le_two)

theorem applyR_y_of_toBodyR (g : RotatedSquare) (X y : ℝ) :
    y = (g.shift.2 : ℝ) + (g.dir.s : ℝ) * (toBodyR g (X, y)).1
      + (g.dir.c : ℝ) * (toBodyR g (X, y)).2 := by
  have hc : (g.dir.c : ℝ) * (g.dir.c : ℝ) + (g.dir.s : ℝ) * (g.dir.s : ℝ) = 1 := by
    exact_mod_cast g.dir.hc
  apply Eq.symm
  simp only [toBodyR, rotateInvR]
  calc
    (g.shift.2 : ℝ) + (g.dir.s : ℝ) *
          ((g.dir.c : ℝ) * (X - (g.shift.1 : ℝ)) + (g.dir.s : ℝ) * (y - (g.shift.2 : ℝ)))
        + (g.dir.c : ℝ) *
          ((-(g.dir.s : ℝ)) * (X - (g.shift.1 : ℝ)) + (g.dir.c : ℝ) * (y - (g.shift.2 : ℝ)))
        = (g.shift.2 : ℝ) + ((g.dir.c : ℝ) * (g.dir.c : ℝ) + (g.dir.s : ℝ) * (g.dir.s : ℝ)) *
            (y - (g.shift.2 : ℝ)) := by ring
    _ = (g.shift.2 : ℝ) + 1 * (y - (g.shift.2 : ℝ)) := by rw [hc]
    _ = y := by ring

theorem abs_delta_y_containsR (g : RotatedSquare) (x₁ y₁ x₂ y₂ : ℝ)
    (h1 : containsR g (x₁, y₁)) (h2 : containsR g (x₂, y₂)) :
    |y₁ - y₂| ≤ |(g.dir.c : ℝ)| + |(g.dir.s : ℝ)| := by
  have e1 := applyR_y_of_toBodyR g x₁ y₁
  have e2 := applyR_y_of_toBodyR g x₂ y₂
  obtain ⟨hu1, hu1b, hv1, hv1b⟩ := h1
  obtain ⟨hu2, hu2b, hv2, hv2b⟩ := h2
  have hdu : |(toBodyR g (x₁, y₁)).1 - (toBodyR g (x₂, y₂)).1| ≤ 1 := by
    cases' le_total (toBodyR g (x₁, y₁)).1 (toBodyR g (x₂, y₂)).1 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hdv : |(toBodyR g (x₁, y₁)).2 - (toBodyR g (x₂, y₂)).2| ≤ 1 := by
    cases' le_total (toBodyR g (x₁, y₁)).2 (toBodyR g (x₂, y₂)).2 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hEq : y₁ - y₂ =
      (g.dir.s : ℝ) * ((toBodyR g (x₁, y₁)).1 - (toBodyR g (x₂, y₂)).1) +
        (g.dir.c : ℝ) * ((toBodyR g (x₁, y₁)).2 - (toBodyR g (x₂, y₂)).2) := by
    linarith
  rw [hEq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_of_le_one_right (abs_nonneg (g.dir.s : ℝ)) hdu,
    mul_le_of_le_one_right (abs_nonneg (g.dir.c : ℝ)) hdv]

theorem abs_delta_x_containsR (g : RotatedSquare) (x₁ y₁ x₂ y₂ : ℝ)
    (h1 : containsR g (x₁, y₁)) (h2 : containsR g (x₂, y₂)) :
    |x₁ - x₂| ≤ |(g.dir.c : ℝ)| + |(g.dir.s : ℝ)| := by
  have e1 := applyR_x_of_toBodyR g x₁ y₁
  have e2 := applyR_x_of_toBodyR g x₂ y₂
  obtain ⟨hu1, hu1b, hv1, hv1b⟩ := h1
  obtain ⟨hu2, hu2b, hv2, hv2b⟩ := h2
  have hdu : |(toBodyR g (x₁, y₁)).1 - (toBodyR g (x₂, y₂)).1| ≤ 1 := by
    cases' le_total (toBodyR g (x₁, y₁)).1 (toBodyR g (x₂, y₂)).1 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hdv : |(toBodyR g (x₁, y₁)).2 - (toBodyR g (x₂, y₂)).2| ≤ 1 := by
    cases' le_total (toBodyR g (x₁, y₁)).2 (toBodyR g (x₂, y₂)).2 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hEq : x₁ - x₂ =
      (g.dir.c : ℝ) * ((toBodyR g (x₁, y₁)).1 - (toBodyR g (x₂, y₂)).1) -
        (g.dir.s : ℝ) * ((toBodyR g (x₁, y₁)).2 - (toBodyR g (x₂, y₂)).2) := by
    linarith
  rw [hEq]
  refine le_trans (abs_sub _ _) ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_of_le_one_right (abs_nonneg (g.dir.c : ℝ)) hdu,
    mul_le_of_le_one_right (abs_nonneg (g.dir.s : ℝ)) hdv]

theorem abs_delta_y_le_two (g : RotatedSquare) (x₁ y₁ x₂ y₂ : ℝ)
    (h1 : containsR g (x₁, y₁)) (h2 : containsR g (x₂, y₂)) :
    |y₁ - y₂| ≤ 2 :=
  (abs_delta_y_containsR g x₁ y₁ x₂ y₂ h1 h2).trans
    (by exact_mod_cast unitDir_projectedWidth_le_two g.dir)

theorem abs_delta_x_le_two (g : RotatedSquare) (x₁ y₁ x₂ y₂ : ℝ)
    (h1 : containsR g (x₁, y₁)) (h2 : containsR g (x₂, y₂)) :
    |x₁ - x₂| ≤ 2 :=
  (abs_delta_x_containsR g x₁ y₁ x₂ y₂ h1 h2).trans
    (by exact_mod_cast unitDir_projectedWidth_le_two g.dir)

theorem projectedWidth_lt_two_mu (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ) :
    (|g.dir.c| + |g.dir.s| : ℚ) < 2 * μ := by
  have hle : |g.dir.c| + |g.dir.s| ≤ 2 := unitDir_projectedWidth_le_two g.dir
  have : (2 : ℚ) < 2 * μ := by nlinarith [hμ]
  linarith

theorem parallel_miss_bottom_top (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (x₁ x₂ : ℚ)
    (h0 : RotatedSquare.contains g (x₁, 0))
    (h1 : RotatedSquare.contains g (x₂, 2 * μ)) : False := by
  have hr0 := contains_implies_containsR g x₁ (0 : ℚ) h0
  have hr1 := contains_implies_containsR g x₂ (2 * μ) h1
  have hd := abs_delta_y_le_two g (x₁ : ℝ) ((0 : ℚ) : ℝ) (x₂ : ℝ) ((2 * μ : ℚ) : ℝ) hr0 hr1
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have : |((2 * μ : ℚ) : ℝ)| ≤ (2 : ℝ) := by
      simpa [abs_sub_comm, Rat.cast_zero] using hd
    rwa [abs_of_nonneg hnn] at this
  linarith

theorem parallel_miss_left_right (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (y₁ y₂ : ℚ)
    (h0 : RotatedSquare.contains g (0, y₁))
    (h1 : RotatedSquare.contains g (2 * μ, y₂)) : False := by
  have hr0 := contains_implies_containsR g (0 : ℚ) y₁ h0
  have hr1 := contains_implies_containsR g (2 * μ) y₂ h1
  have hd := abs_delta_x_le_two g ((0 : ℚ) : ℝ) (y₁ : ℝ) ((2 * μ : ℚ) : ℝ) (y₂ : ℝ) hr0 hr1
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have : |((2 * μ : ℚ) : ℝ)| ≤ (2 : ℝ) := by
      simpa [abs_sub_comm, Rat.cast_zero] using hd
    rwa [abs_of_nonneg hnn] at this
  linarith

def vertSliceR (g : RotatedSquare) (X : ℚ) : Set ℝ :=
  {y | containsR g ((X : ℝ), y)}

theorem mem_vertSliceR_of_contains (g : RotatedSquare) (X y : ℚ)
    (h : RotatedSquare.contains g (X, y)) : (y : ℝ) ∈ vertSliceR g X :=
  contains_implies_containsR g X y h

theorem vertSliceR_isClosed (g : RotatedSquare) (X : ℚ) : IsClosed (vertSliceR g X) := by
  let f1 : ℝ → ℝ := fun y => (toBodyR g ((X : ℝ), y)).1
  let f2 : ℝ → ℝ := fun y => (toBodyR g ((X : ℝ), y)).2
  have hf1 : Continuous f1 := by simp only [f1, toBodyR, rotateInvR]; continuity
  have hf2 : Continuous f2 := by simp only [f2, toBodyR, rotateInvR]; continuity
  have : vertSliceR g X = f1 ⁻¹' Icc 0 1 ∩ f2 ⁻¹' Icc 0 1 := by
    ext y; simp [vertSliceR, containsR, f1, f2, mem_preimage, mem_Icc, mem_inter_iff]
    constructor
    · intro ⟨a, b, c, d⟩; exact ⟨⟨a, b⟩, ⟨c, d⟩⟩
    · intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨a, b, c, d⟩
  rw [this]
  exact (isClosed_Icc.preimage hf1).inter (isClosed_Icc.preimage hf2)

theorem vertSliceR_bddBelow (g : RotatedSquare) (X : ℚ)
    (hne : (vertSliceR g X).Nonempty) : BddBelow (vertSliceR g X) := by
  rcases hne with ⟨y0, hy0⟩
  refine ⟨y0 - 2, fun y hy => ?_⟩
  have := abs_delta_y_le_two g (X : ℝ) y0 (X : ℝ) y hy0 hy
  cases' abs_cases (y0 - y) with h' h' <;> linarith

theorem vertSliceR_bddAbove (g : RotatedSquare) (X : ℚ)
    (hne : (vertSliceR g X).Nonempty) : BddAbove (vertSliceR g X) := by
  rcases hne with ⟨y0, hy0⟩
  refine ⟨y0 + 2, fun y hy => ?_⟩
  have := abs_delta_y_le_two g (X : ℝ) y0 (X : ℝ) y hy0 hy
  cases' abs_cases (y0 - y) with h' h' <;> linarith

noncomputable def vertChordLo (g : RotatedSquare) (X : ℚ) : ℝ :=
  if _hne : (vertSliceR g X).Nonempty then sInf (vertSliceR g X) else 0

noncomputable def vertChordHi (g : RotatedSquare) (X : ℚ) : ℝ :=
  if _hne : (vertSliceR g X).Nonempty then sSup (vertSliceR g X) else 0

theorem vertChord_le (g : RotatedSquare) (X : ℚ) :
    vertChordLo g X ≤ vertChordHi g X := by
  dsimp [vertChordLo, vertChordHi]
  split_ifs with hne
  · exact csInf_le_csSup hne (vertSliceR_bddBelow g X hne) (vertSliceR_bddAbove g X hne)
  · rfl

theorem vertChord_len_le_two (g : RotatedSquare) (X : ℚ) :
    vertChordHi g X - vertChordLo g X ≤ 2 := by
  dsimp [vertChordLo, vertChordHi]
  split_ifs with hne
  · have hs : sSup (vertSliceR g X) ≤ sInf (vertSliceR g X) + 2 := by
      apply csSup_le hne
      intro y hy
      have : y - 2 ≤ sInf (vertSliceR g X) := by
        apply le_csInf hne
        intro z hz
        have hd := abs_delta_y_le_two g (X : ℝ) y (X : ℝ) z hy hz
        cases' abs_cases (y - z) with h' h' <;> linarith
      linarith
    linarith
  · norm_num

theorem slice_subset_vertChordIcc (g : RotatedSquare) (X : ℚ) :
    vertSliceR g X ⊆ Icc (vertChordLo g X) (vertChordHi g X) := by
  intro y hy
  have hne : (vertSliceR g X).Nonempty := ⟨y, hy⟩
  dsimp [vertChordLo, vertChordHi]
  simp only [hne, mem_Icc]
  exact ⟨csInf_le (vertSliceR_bddBelow g X hne) hy,
    le_csSup (vertSliceR_bddAbove g X hne) hy⟩

theorem vertSliceUnion_isClosed (squares : Fin 6 → RotatedSquare) (X : ℚ) :
    IsClosed (⋃ i, vertSliceR (squares i) X) :=
  isClosed_iUnion_of_finite (fun i => vertSliceR_isClosed (squares i) X)

theorem line_vert_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ) (X : ℚ)
    (squares : Fin 6 → RotatedSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (X, q)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆
      ⋃ i, Icc (vertChordLo (squares i) X) (vertChordHi (squares i) X) := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  have hslice : Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) ⊆ ⋃ i, vertSliceR (squares i) X := by
    refine S6.AxisGridCover.Icc_subset_of_closed_of_rats _
      (vertSliceUnion_isClosed squares X) (2 * μ) hL ?_
    intro q hq0 hqL
    rcases hQ q hq0 hqL with ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, mem_vertSliceR_of_contains _ X q hi⟩
  intro y hy
  rcases mem_iUnion.mp (hslice hy) with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, slice_subset_vertChordIcc (squares i) X hi⟩

theorem line_horiz_rat_cover_implies_real (μ : ℚ) (hμ : 1 < μ) (Y : ℚ)
    (squares : Fin 6 → RotatedSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (q, Y)) :
    Icc (0 : ℝ) ((2 : ℝ) * μ) ⊆
      ⋃ i, Icc (horizChordLo (squares i) Y) (horizChordHi (squares i) Y) := by
  have hL : (0 : ℚ) ≤ 2 * μ := by nlinarith [hμ]
  have hEq : Icc (0 : ℝ) ((2 : ℝ) * μ) = Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) := by simp
  rw [hEq]
  have hslice : Icc (0 : ℝ) ((2 * μ : ℚ) : ℝ) ⊆ ⋃ i, horizSliceR (squares i) Y := by
    refine S6.AxisGridCover.Icc_subset_of_closed_of_rats _
      (horizSliceUnion_isClosed squares Y) (2 * μ) hL ?_
    intro q hq0 hqL
    rcases hQ q hq0 hqL with ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, mem_horizSliceR_of_contains _ Y q hi⟩
  intro x hx
  rcases mem_iUnion.mp (hslice hx) with ⟨i, hi⟩
  exact mem_iUnion.mpr ⟨i, slice_subset_chordIcc (squares i) Y hi⟩

theorem RotatedLineChordCover_of_horiz_line (μ : ℚ) (hμ : 1 < μ) (Y : ℚ)
    (squares : Fin 6 → RotatedSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (q, Y)) :
    Nonempty (RotatedLineChordCover μ) :=
  ⟨{ lo := fun i => horizChordLo (squares i) Y
     hi := fun i => horizChordHi (squares i) Y
     hle := fun i => horizChord_le (squares i) Y
     hchord_le_two := fun i => horizChord_len_le_two (squares i) Y
     hcover := line_horiz_rat_cover_implies_real μ hμ Y squares hQ }⟩

theorem RotatedLineChordCover_of_vert_line (μ : ℚ) (hμ : 1 < μ) (X : ℚ)
    (squares : Fin 6 → RotatedSquare)
    (hQ : ∀ q : ℚ, 0 ≤ q → q ≤ 2 * μ → ∃ i, RotatedSquare.contains (squares i) (X, q)) :
    Nonempty (RotatedLineChordCover μ) :=
  ⟨{ lo := fun i => vertChordLo (squares i) X
     hi := fun i => vertChordHi (squares i) X
     hle := fun i => vertChord_le (squares i) X
     hchord_le_two := fun i => vertChord_len_le_two (squares i) X
     hcover := line_vert_rat_cover_implies_real μ hμ X squares hQ }⟩

/-- Six Euclidean line covers from any `RotatedGridRatCover` (no axis hyp). -/
structure RotatedSixLineRealCovers (μ : ℚ) where
  bottom : RotatedLineChordCover μ
  top : RotatedLineChordCover μ
  left : RotatedLineChordCover μ
  right : RotatedLineChordCover μ
  hMid : RotatedLineChordCover μ
  vMid : RotatedLineChordCover μ

def RotatedSixLineRealLift : Prop :=
  ∀ (μ : ℚ), 1 < μ → ∀ (squares : Fin 6 → RotatedSquare),
    RotatedGridRatCover μ squares → Nonempty (RotatedSixLineRealCovers μ)

theorem RotatedSixLineRealLift_of_ratCover : RotatedSixLineRealLift := by
  intro μ hμ squares H
  exact ⟨{
    bottom := (RotatedLineChordCover_of_horiz_line μ hμ 0 squares H.bottom).some
    top := (RotatedLineChordCover_of_horiz_line μ hμ (2 * μ) squares H.top).some
    left := (RotatedLineChordCover_of_vert_line μ hμ 0 squares H.left).some
    right := (RotatedLineChordCover_of_vert_line μ hμ (2 * μ) squares H.right).some
    hMid := (RotatedLineChordCover_of_horiz_line μ hμ μ squares H.hMid).some
    vMid := (RotatedLineChordCover_of_vert_line μ hμ μ squares H.vMid).some }⟩

theorem rotatedSixLineRealLift_held : RotatedSixLineRealLift :=
  RotatedSixLineRealLift_of_ratCover

def rotatedSixLineRealLiftProved : Bool := true
theorem rotatedSixLineRealLiftProved_true : rotatedSixLineRealLiftProved = true := rfl

def rotatedParallelMissClosed : Bool := true
theorem rotatedParallelMissClosed_true : rotatedParallelMissClosed = true := rfl


/-! ## Clamped outer packing (toward squareTotal ≤ 2) -/

theorem onesided_axial_sum_le_two_real (xb yb : ℝ) (hx : 0 ≤ xb) (hy : 0 ≤ yb)
    (hsq : xb * xb + yb * yb ≤ 2) : xb + yb ≤ 2 := by
  have hamg : 2 * xb * yb ≤ xb * xb + yb * yb := by
    nlinarith [sq_nonneg (xb - yb)]
  nlinarith

theorem distSq_containsR_le_two (g : RotatedSquare) (x₁ y₁ x₂ y₂ : ℝ)
    (h1 : containsR g (x₁, y₁)) (h2 : containsR g (x₂, y₂)) :
    (x₁ - x₂) * (x₁ - x₂) + (y₁ - y₂) * (y₁ - y₂) ≤ 2 := by
  obtain ⟨hu1, hu1b, hv1, hv1b⟩ := h1
  obtain ⟨hu2, hu2b, hv2, hv2b⟩ := h2
  have hc : (g.dir.c : ℝ) * (g.dir.c : ℝ) + (g.dir.s : ℝ) * (g.dir.s : ℝ) = 1 := by
    exact_mod_cast g.dir.hc
  have e1x := applyR_x_of_toBodyR g x₁ y₁
  have e1y := applyR_y_of_toBodyR g x₁ y₁
  have e2x := applyR_x_of_toBodyR g x₂ y₂
  have e2y := applyR_y_of_toBodyR g x₂ y₂
  set du := (toBodyR g (x₁, y₁)).1 - (toBodyR g (x₂, y₂)).1
  set dv := (toBodyR g (x₁, y₁)).2 - (toBodyR g (x₂, y₂)).2
  have hdx : x₁ - x₂ = (g.dir.c : ℝ) * du - (g.dir.s : ℝ) * dv := by
    simp only [du, dv]; linarith
  have hdy : y₁ - y₂ = (g.dir.s : ℝ) * du + (g.dir.c : ℝ) * dv := by
    simp only [du, dv]; linarith
  have hrot :
      ((g.dir.c : ℝ) * du - (g.dir.s : ℝ) * dv) *
          ((g.dir.c : ℝ) * du - (g.dir.s : ℝ) * dv) +
        ((g.dir.s : ℝ) * du + (g.dir.c : ℝ) * dv) *
          ((g.dir.s : ℝ) * du + (g.dir.c : ℝ) * dv) =
        ((g.dir.c : ℝ) * (g.dir.c : ℝ) + (g.dir.s : ℝ) * (g.dir.s : ℝ)) *
          (du * du + dv * dv) := by ring
  have hEq : (x₁ - x₂) * (x₁ - x₂) + (y₁ - y₂) * (y₁ - y₂) = du * du + dv * dv := by
    rw [hdx, hdy, hrot, hc]; ring
  have hdu : |du| ≤ 1 := by
    simp only [du]
    cases' le_total (toBodyR g (x₁, y₁)).1 (toBodyR g (x₂, y₂)).1 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hdv : |dv| ≤ 1 := by
    simp only [dv]
    cases' le_total (toBodyR g (x₁, y₁)).2 (toBodyR g (x₂, y₂)).2 with h h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hdu2 : du * du ≤ 1 := by have := sq_abs du; nlinarith [hdu]
  have hdv2 : dv * dv ≤ 1 := by have := sq_abs dv; nlinarith [hdv]
  nlinarith [hEq]

theorem horizChordHi_mem (g : RotatedSquare) (Y : ℚ)
    (hne : (horizSliceR g Y).Nonempty) :
    horizChordHi g Y ∈ horizSliceR g Y := by
  dsimp [horizChordHi]; simp only [hne]
  exact (horizSliceR_isClosed g Y).csSup_mem hne (horizSliceR_bddAbove g Y hne)

theorem vertChordHi_mem (g : RotatedSquare) (X : ℚ)
    (hne : (vertSliceR g X).Nonempty) :
    vertChordHi g X ∈ vertSliceR g X := by
  dsimp [vertChordHi]; simp only [hne]
  exact (vertSliceR_isClosed g X).csSup_mem hne (vertSliceR_bddAbove g X hne)

noncomputable def clampedHorizLen (g : RotatedSquare) (Y μ : ℚ) : ℝ :=
  let lo := max (horizChordLo g Y) 0
  let hi := min (horizChordHi g Y) ((2 : ℝ) * μ)
  max (hi - lo) 0

noncomputable def clampedVertLen (g : RotatedSquare) (X μ : ℚ) : ℝ :=
  let lo := max (vertChordLo g X) 0
  let hi := min (vertChordHi g X) ((2 : ℝ) * μ)
  max (hi - lo) 0

theorem SW_clamped_outer_sum_le_two (g : RotatedSquare) (μ : ℚ) (_hμ : 1 < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    clampedHorizLen g 0 μ + clampedVertLen g 0 μ ≤ 2 := by
  have hr0 := contains_implies_containsR g (0 : ℚ) (0 : ℚ) hSW
  have hneB : (horizSliceR g (0 : ℚ)).Nonempty := ⟨((0 : ℚ) : ℝ), hr0⟩
  have hneL : (vertSliceR g (0 : ℚ)).Nonempty := ⟨((0 : ℚ) : ℝ), hr0⟩
  have hHiB := horizChordHi_mem g 0 hneB
  have hHiL := vertChordHi_mem g 0 hneL
  have h0B : ((0 : ℚ) : ℝ) ∈ horizSliceR g 0 := hr0
  have h0L : ((0 : ℚ) : ℝ) ∈ vertSliceR g 0 := hr0
  have hleB : horizChordLo g 0 ≤ ((0 : ℚ) : ℝ) := (slice_subset_chordIcc g 0 h0B).1
  have hgeB : ((0 : ℚ) : ℝ) ≤ horizChordHi g 0 := (slice_subset_chordIcc g 0 h0B).2
  have hleL : vertChordLo g 0 ≤ ((0 : ℚ) : ℝ) := (slice_subset_vertChordIcc g 0 h0L).1
  have hgeL : ((0 : ℚ) : ℝ) ≤ vertChordHi g 0 := (slice_subset_vertChordIcc g 0 h0L).2
  have hB : containsR g (horizChordHi g 0, ((0 : ℚ) : ℝ)) := hHiB
  have hL : containsR g (((0 : ℚ) : ℝ), vertChordHi g 0) := hHiL
  have hsq := distSq_containsR_le_two g (horizChordHi g 0) ((0 : ℚ) : ℝ)
    ((0 : ℚ) : ℝ) (vertChordHi g 0) hB hL
  have hsq' : horizChordHi g 0 * horizChordHi g 0 + vertChordHi g 0 * vertChordHi g 0 ≤ 2 := by
    convert hsq using 1; ring
  have hx0 : (0 : ℝ) ≤ horizChordHi g 0 := by exact_mod_cast hgeB
  have hy0 : (0 : ℝ) ≤ vertChordHi g 0 := by exact_mod_cast hgeL
  have hsum := onesided_axial_sum_le_two_real (horizChordHi g 0) (vertChordHi g 0) hx0 hy0 hsq'
  have hb : clampedHorizLen g 0 μ ≤ horizChordHi g 0 := by
    change max (min (horizChordHi g 0) ((2 : ℝ) * μ) - max (horizChordLo g 0) 0) 0 ≤
      horizChordHi g 0
    have hlo : max (horizChordLo g 0) (0 : ℝ) = 0 := max_eq_right (by exact_mod_cast hleB)
    rw [hlo, sub_zero]
    exact max_le (min_le_left _ _) hx0
  have hl : clampedVertLen g 0 μ ≤ vertChordHi g 0 := by
    change max (min (vertChordHi g 0) ((2 : ℝ) * μ) - max (vertChordLo g 0) 0) 0 ≤
      vertChordHi g 0
    have hlo : max (vertChordLo g 0) (0 : ℝ) = 0 := max_eq_right (by exact_mod_cast hleL)
    rw [hlo, sub_zero]
    exact max_le (min_le_left _ _) hy0
  linarith

theorem horizChordLo_mem (g : RotatedSquare) (Y : ℚ)
    (hne : (horizSliceR g Y).Nonempty) :
    horizChordLo g Y ∈ horizSliceR g Y := by
  dsimp [horizChordLo]; simp only [hne]
  exact (horizSliceR_isClosed g Y).csInf_mem hne (horizSliceR_bddBelow g Y hne)

theorem vertChordLo_mem (g : RotatedSquare) (X : ℚ)
    (hne : (vertSliceR g X).Nonempty) :
    vertChordLo g X ∈ vertSliceR g X := by
  dsimp [vertChordLo]; simp only [hne]
  exact (vertSliceR_isClosed g X).csInf_mem hne (vertSliceR_bddBelow g X hne)

theorem SW_clamped_outer_packing_held (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    clampedHorizLen g 0 μ + clampedVertLen g 0 μ ≤ 2 :=
  SW_clamped_outer_sum_le_two g μ hμ hSW

theorem rat_two_mu (μ : ℚ) : ((2 * μ : ℚ) : ℝ) = (2 : ℝ) * μ := by push_cast; ring

theorem clampedHorizLen_le_two_mu_sub_lo (g : RotatedSquare) (Y μ : ℚ)
    (hlo : horizChordLo g Y ≤ ((2 * μ : ℚ) : ℝ)) :
    clampedHorizLen g Y μ ≤ ((2 * μ : ℚ) : ℝ) - horizChordLo g Y := by
  change max (min (horizChordHi g Y) ((2 : ℝ) * μ) - max (horizChordLo g Y) 0) 0 ≤
    ((2 * μ : ℚ) : ℝ) - horizChordLo g Y
  set A := min (horizChordHi g Y) ((2 : ℝ) * μ)
  set B := max (horizChordLo g Y) (0 : ℝ)
  set C := ((2 * μ : ℚ) : ℝ)
  set D := horizChordLo g Y
  have hAC : A ≤ C := by
    have : A ≤ (2 : ℝ) * μ := min_le_right _ _
    simpa [A, C, rat_two_mu μ] using this
  have hDB : D ≤ B := le_max_left _ _
  have hlen : A - B ≤ C - D := by linarith
  have hnn : (0 : ℝ) ≤ C - D := sub_nonneg.mpr hlo
  simpa [A, B, C, D] using max_le hlen hnn

theorem clampedVertLen_le_two_mu_sub_lo (g : RotatedSquare) (X μ : ℚ)
    (hlo : vertChordLo g X ≤ ((2 * μ : ℚ) : ℝ)) :
    clampedVertLen g X μ ≤ ((2 * μ : ℚ) : ℝ) - vertChordLo g X := by
  change max (min (vertChordHi g X) ((2 : ℝ) * μ) - max (vertChordLo g X) 0) 0 ≤
    ((2 * μ : ℚ) : ℝ) - vertChordLo g X
  set A := min (vertChordHi g X) ((2 : ℝ) * μ)
  set B := max (vertChordLo g X) (0 : ℝ)
  set C := ((2 * μ : ℚ) : ℝ)
  set D := vertChordLo g X
  have hAC : A ≤ C := by
    have : A ≤ (2 : ℝ) * μ := min_le_right _ _
    simpa [A, C, rat_two_mu μ] using this
  have hDB : D ≤ B := le_max_left _ _
  have hlen : A - B ≤ C - D := by linarith
  have hnn : (0 : ℝ) ≤ C - D := sub_nonneg.mpr hlo
  simpa [A, B, C, D] using max_le hlen hnn

theorem clampedHorizLen_le_hi (g : RotatedSquare) (Y μ : ℚ)
    (hle : horizChordLo g Y ≤ (0 : ℝ)) (hge : (0 : ℝ) ≤ horizChordHi g Y) :
    clampedHorizLen g Y μ ≤ horizChordHi g Y := by
  change max (min (horizChordHi g Y) ((2 : ℝ) * μ) - max (horizChordLo g Y) 0) 0 ≤
    horizChordHi g Y
  have hlo : max (horizChordLo g Y) (0 : ℝ) = 0 := max_eq_right hle
  rw [hlo, sub_zero]
  exact max_le (min_le_left _ _) hge

theorem clampedVertLen_le_hi (g : RotatedSquare) (X μ : ℚ)
    (hle : vertChordLo g X ≤ (0 : ℝ)) (hge : (0 : ℝ) ≤ vertChordHi g X) :
    clampedVertLen g X μ ≤ vertChordHi g X := by
  change max (min (vertChordHi g X) ((2 : ℝ) * μ) - max (vertChordLo g X) 0) 0 ≤
    vertChordHi g X
  have hlo : max (vertChordLo g X) (0 : ℝ) = 0 := max_eq_right hle
  rw [hlo, sub_zero]
  exact max_le (min_le_left _ _) hge

theorem SE_clamped_outer_sum_le_two (g : RotatedSquare) (μ : ℚ) (_hμ : 1 < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    clampedHorizLen g 0 μ + clampedVertLen g (2 * μ) μ ≤ 2 := by
  have hr0 := contains_implies_containsR g (2 * μ) (0 : ℚ) hSE
  have hneB : (horizSliceR g (0 : ℚ)).Nonempty := ⟨((2 * μ : ℚ) : ℝ), hr0⟩
  have hneR : (vertSliceR g (2 * μ)).Nonempty := ⟨((0 : ℚ) : ℝ), hr0⟩
  have hLoB := horizChordLo_mem g 0 hneB
  have hHiR := vertChordHi_mem g (2 * μ) hneR
  have h0B : ((2 * μ : ℚ) : ℝ) ∈ horizSliceR g 0 := hr0
  have h0R : ((0 : ℚ) : ℝ) ∈ vertSliceR g (2 * μ) := hr0
  have hgeLo : horizChordLo g 0 ≤ ((2 * μ : ℚ) : ℝ) := (slice_subset_chordIcc g 0 h0B).1
  have hleL0 : vertChordLo g (2 * μ) ≤ ((0 : ℚ) : ℝ) :=
    (slice_subset_vertChordIcc g (2 * μ) h0R).1
  have hgeR : ((0 : ℚ) : ℝ) ≤ vertChordHi g (2 * μ) :=
    (slice_subset_vertChordIcc g (2 * μ) h0R).2
  have hsq := distSq_containsR_le_two g (horizChordLo g 0) ((0 : ℚ) : ℝ)
    ((2 * μ : ℚ) : ℝ) (vertChordHi g (2 * μ)) hLoB hHiR
  set xb : ℝ := ((2 * μ : ℚ) : ℝ) - horizChordLo g 0
  set yb : ℝ := vertChordHi g (2 * μ)
  have hxb0 : (0 : ℝ) ≤ xb := sub_nonneg.mpr hgeLo
  have hyb0 : (0 : ℝ) ≤ yb := by exact_mod_cast hgeR
  have hsq' : xb * xb + yb * yb ≤ 2 := by dsimp [xb, yb]; convert hsq using 1; ring
  have hsum := onesided_axial_sum_le_two_real xb yb hxb0 hyb0 hsq'
  have hb : clampedHorizLen g 0 μ ≤ xb := by
    simpa [xb] using clampedHorizLen_le_two_mu_sub_lo g 0 μ hgeLo
  have hr : clampedVertLen g (2 * μ) μ ≤ yb :=
    clampedVertLen_le_hi g (2 * μ) μ (by exact_mod_cast hleL0) hyb0
  linarith

theorem NE_clamped_outer_sum_le_two (g : RotatedSquare) (μ : ℚ) (_hμ : 1 < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    clampedHorizLen g (2 * μ) μ + clampedVertLen g (2 * μ) μ ≤ 2 := by
  have hr0 := contains_implies_containsR g (2 * μ) (2 * μ) hNE
  have hneT : (horizSliceR g (2 * μ)).Nonempty := ⟨((2 * μ : ℚ) : ℝ), hr0⟩
  have hneR : (vertSliceR g (2 * μ)).Nonempty := ⟨((2 * μ : ℚ) : ℝ), hr0⟩
  have hLoT := horizChordLo_mem g (2 * μ) hneT
  have hLoR := vertChordLo_mem g (2 * μ) hneR
  have h0T : ((2 * μ : ℚ) : ℝ) ∈ horizSliceR g (2 * μ) := hr0
  have h0R : ((2 * μ : ℚ) : ℝ) ∈ vertSliceR g (2 * μ) := hr0
  have hgeLoT : horizChordLo g (2 * μ) ≤ ((2 * μ : ℚ) : ℝ) :=
    (slice_subset_chordIcc g (2 * μ) h0T).1
  have hgeLoR : vertChordLo g (2 * μ) ≤ ((2 * μ : ℚ) : ℝ) :=
    (slice_subset_vertChordIcc g (2 * μ) h0R).1
  have hsq := distSq_containsR_le_two g (horizChordLo g (2 * μ)) ((2 * μ : ℚ) : ℝ)
    ((2 * μ : ℚ) : ℝ) (vertChordLo g (2 * μ)) hLoT hLoR
  set xb : ℝ := ((2 * μ : ℚ) : ℝ) - horizChordLo g (2 * μ)
  set yb : ℝ := ((2 * μ : ℚ) : ℝ) - vertChordLo g (2 * μ)
  have hxb0 : (0 : ℝ) ≤ xb := sub_nonneg.mpr hgeLoT
  have hyb0 : (0 : ℝ) ≤ yb := sub_nonneg.mpr hgeLoR
  have hsq' : xb * xb + yb * yb ≤ 2 := by dsimp [xb, yb]; convert hsq using 1; ring
  have hsum := onesided_axial_sum_le_two_real xb yb hxb0 hyb0 hsq'
  have ht : clampedHorizLen g (2 * μ) μ ≤ xb := by
    simpa [xb] using clampedHorizLen_le_two_mu_sub_lo g (2 * μ) μ hgeLoT
  have hr : clampedVertLen g (2 * μ) μ ≤ yb := by
    simpa [yb] using clampedVertLen_le_two_mu_sub_lo g (2 * μ) μ hgeLoR
  linarith

theorem NW_clamped_outer_sum_le_two (g : RotatedSquare) (μ : ℚ) (_hμ : 1 < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    clampedHorizLen g (2 * μ) μ + clampedVertLen g 0 μ ≤ 2 := by
  have hr0 := contains_implies_containsR g (0 : ℚ) (2 * μ) hNW
  have hneT : (horizSliceR g (2 * μ)).Nonempty := ⟨((0 : ℚ) : ℝ), hr0⟩
  have hneL : (vertSliceR g (0 : ℚ)).Nonempty := ⟨((2 * μ : ℚ) : ℝ), hr0⟩
  have hHiT := horizChordHi_mem g (2 * μ) hneT
  have hLoL := vertChordLo_mem g 0 hneL
  have h0T : ((0 : ℚ) : ℝ) ∈ horizSliceR g (2 * μ) := hr0
  have h0L : ((2 * μ : ℚ) : ℝ) ∈ vertSliceR g 0 := hr0
  have hleT0 : horizChordLo g (2 * μ) ≤ ((0 : ℚ) : ℝ) :=
    (slice_subset_chordIcc g (2 * μ) h0T).1
  have hgeT : ((0 : ℚ) : ℝ) ≤ horizChordHi g (2 * μ) :=
    (slice_subset_chordIcc g (2 * μ) h0T).2
  have hgeLoL : vertChordLo g 0 ≤ ((2 * μ : ℚ) : ℝ) :=
    (slice_subset_vertChordIcc g 0 h0L).1
  have hsq := distSq_containsR_le_two g (horizChordHi g (2 * μ)) ((2 * μ : ℚ) : ℝ)
    ((0 : ℚ) : ℝ) (vertChordLo g 0) hHiT hLoL
  set xb : ℝ := horizChordHi g (2 * μ)
  set yb : ℝ := ((2 * μ : ℚ) : ℝ) - vertChordLo g 0
  have hxb0 : (0 : ℝ) ≤ xb := by exact_mod_cast hgeT
  have hyb0 : (0 : ℝ) ≤ yb := sub_nonneg.mpr hgeLoL
  have hsq' : xb * xb + yb * yb ≤ 2 := by dsimp [xb, yb]; convert hsq using 1; ring
  have hsum := onesided_axial_sum_le_two_real xb yb hxb0 hyb0 hsq'
  have ht : clampedHorizLen g (2 * μ) μ ≤ xb :=
    clampedHorizLen_le_hi g (2 * μ) μ (by exact_mod_cast hleT0) hxb0
  have hl : clampedVertLen g 0 μ ≤ yb := by
    simpa [yb] using clampedVertLen_le_two_mu_sub_lo g 0 μ hgeLoL
  linarith

theorem PointwiseCover_corner_clamped_outer_le_two {T : Target} (cov : PointwiseCover T) :
    let C := cov.toCornerOwners
    clampedHorizLen (C.squares C.i1) 0 T.μ + clampedVertLen (C.squares C.i1) 0 T.μ ≤ 2 ∧
      clampedHorizLen (C.squares C.i2) 0 T.μ +
        clampedVertLen (C.squares C.i2) (2 * T.μ) T.μ ≤ 2 ∧
      clampedHorizLen (C.squares C.i3) (2 * T.μ) T.μ +
        clampedVertLen (C.squares C.i3) (2 * T.μ) T.μ ≤ 2 ∧
      clampedHorizLen (C.squares C.i4) (2 * T.μ) T.μ +
        clampedVertLen (C.squares C.i4) 0 T.μ ≤ 2 := by
  intro C
  have hμ := T.hμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SW_clamped_outer_sum_le_two _ T.μ hμ (by simpa [Target.v1] using C.h1)
  · exact SE_clamped_outer_sum_le_two _ T.μ hμ (by simpa [Target.v2] using C.h2)
  · exact NE_clamped_outer_sum_le_two _ T.μ hμ (by simpa [Target.v3] using C.h3)
  · exact NW_clamped_outer_sum_le_two _ T.μ hμ (by simpa [Target.v4] using C.h4)

def rotatedSWClampedOuterPackingClosed : Bool := true
theorem rotatedSWClampedOuterPackingClosed_true :
    rotatedSWClampedOuterPackingClosed = true := rfl

def rotatedCornerClampedOuterPackingProved : Bool := true
theorem rotatedCornerClampedOuterPackingProved_true :
    rotatedCornerClampedOuterPackingProved = true := rfl

def rotatedCornerClampedOuterPackingClosed : Bool := true
theorem rotatedCornerClampedOuterPackingClosed_true :
    rotatedCornerClampedOuterPackingClosed = true := rfl

/-! ## Mid-miss for corners when μ² > 2 (toward mid packing) -/

theorem SW_misses_hMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hSW : RotatedSquare.contains g (0, 0)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 0) (x, μ) hSW ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg x]

theorem SW_misses_vMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hSW : RotatedSquare.contains g (0, 0)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 0) (μ, y) hSW ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg y]

theorem SE_misses_hMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 0) (x, μ) hSE ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (2 * μ - x)]

theorem SE_misses_vMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 0) (μ, y) hSE ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg y]

theorem NE_misses_hMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 2 * μ) (x, μ) hNE ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (2 * μ - x)]

theorem NE_misses_vMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hd := chord_distSq_le_two g (2 * μ, 2 * μ) (μ, y) hNE ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (2 * μ - y)]

theorem NW_misses_hMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 2 * μ) (x, μ) hNW ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg x]

theorem NW_misses_vMid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hd := chord_distSq_le_two g (0, 2 * μ) (μ, y) hNW ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (2 * μ - y)]

theorem SW_not_meets_mids_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => SW_misses_hMid_of_mu_sq_gt g μ hμ2 hSW x hx,
    fun ⟨y, hy⟩ => SW_misses_vMid_of_mu_sq_gt g μ hμ2 hSW y hy⟩

theorem SE_not_meets_mids_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => SE_misses_hMid_of_mu_sq_gt g μ hμ2 hSE x hx,
    fun ⟨y, hy⟩ => SE_misses_vMid_of_mu_sq_gt g μ hμ2 hSE y hy⟩

theorem NE_not_meets_mids_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => NE_misses_hMid_of_mu_sq_gt g μ hμ2 hNE x hx,
    fun ⟨y, hy⟩ => NE_misses_vMid_of_mu_sq_gt g μ hμ2 hNE y hy⟩

theorem NW_not_meets_mids_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => NW_misses_hMid_of_mu_sq_gt g μ hμ2 hNW x hx,
    fun ⟨y, hy⟩ => NW_misses_vMid_of_mu_sq_gt g μ hμ2 hNW y hy⟩

/-- When `μ² > 2`, every `PointwiseCover` corner owner misses both midlines. -/
theorem PointwiseCover_corner_mid_miss_of_mu_sq_gt {T : Target} (cov : PointwiseCover T)
    (hμ2 : 2 < T.μ * T.μ) :
    let C := cov.toCornerOwners
    (¬ meetsHoriz (C.squares C.i1) T.μ ∧ ¬ meetsVert (C.squares C.i1) T.μ) ∧
      (¬ meetsHoriz (C.squares C.i2) T.μ ∧ ¬ meetsVert (C.squares C.i2) T.μ) ∧
      (¬ meetsHoriz (C.squares C.i3) T.μ ∧ ¬ meetsVert (C.squares C.i3) T.μ) ∧
      (¬ meetsHoriz (C.squares C.i4) T.μ ∧ ¬ meetsVert (C.squares C.i4) T.μ) := by
  intro C
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SW_not_meets_mids_of_mu_sq_gt _ T.μ hμ2 (by simpa [Target.v1] using C.h1)
  · exact SE_not_meets_mids_of_mu_sq_gt _ T.μ hμ2 (by simpa [Target.v2] using C.h2)
  · exact NE_not_meets_mids_of_mu_sq_gt _ T.μ hμ2 (by simpa [Target.v3] using C.h3)
  · exact NW_not_meets_mids_of_mu_sq_gt _ T.μ hμ2 (by simpa [Target.v4] using C.h4)

/-- Corner outer ≤2 plus mid-miss when `μ²>2`: packing skeleton for corner tiles. -/
theorem SW_corner_pack_outer_mid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hμ2 : 2 < μ * μ) (hSW : RotatedSquare.contains g (0, 0)) :
    clampedHorizLen g 0 μ + clampedVertLen g 0 μ ≤ 2 ∧
      ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨SW_clamped_outer_sum_le_two g μ hμ hSW, SW_not_meets_mids_of_mu_sq_gt g μ hμ2 hSW⟩

theorem SE_corner_pack_outer_mid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hμ2 : 2 < μ * μ) (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    clampedHorizLen g 0 μ + clampedVertLen g (2 * μ) μ ≤ 2 ∧
      ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨SE_clamped_outer_sum_le_two g μ hμ hSE, SE_not_meets_mids_of_mu_sq_gt g μ hμ2 hSE⟩

theorem NE_corner_pack_outer_mid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hμ2 : 2 < μ * μ) (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    clampedHorizLen g (2 * μ) μ + clampedVertLen g (2 * μ) μ ≤ 2 ∧
      ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨NE_clamped_outer_sum_le_two g μ hμ hNE, NE_not_meets_mids_of_mu_sq_gt g μ hμ2 hNE⟩

theorem NW_corner_pack_outer_mid_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hμ2 : 2 < μ * μ) (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    clampedHorizLen g (2 * μ) μ + clampedVertLen g 0 μ ≤ 2 ∧
      ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨NW_clamped_outer_sum_le_two g μ hμ hNW, NW_not_meets_mids_of_mu_sq_gt g μ hμ2 hNW⟩

def rotatedCornerMidMissMuSqGtClosed : Bool := true
theorem rotatedCornerMidMissMuSqGtClosed_true :
    rotatedCornerMidMissMuSqGtClosed = true := rfl


/-! ### Centre outer-miss (μ²>2) + projWidth mid-miss (partial μ²≤2) -/

theorem centre_misses_bottom_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, 0) := by
  intro ht
  have hd := chord_distSq_le_two g (μ, μ) (x, 0) hcen ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (μ - x)]

theorem centre_misses_top_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, 2 * μ) := by
  intro ht
  have hd := chord_distSq_le_two g (μ, μ) (x, 2 * μ) hcen ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (μ - x)]

theorem centre_misses_left_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (0, y) := by
  intro ht
  have hd := chord_distSq_le_two g (μ, μ) (0, y) hcen ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (μ - y)]

theorem centre_misses_right_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (2 * μ, y) := by
  intro ht
  have hd := chord_distSq_le_two g (μ, μ) (2 * μ, y) hcen ht
  simp only [distSq] at hd
  nlinarith [mul_self_nonneg (μ - y)]

theorem centre_not_meets_outers_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) :
    ¬ meetsHoriz g 0 ∧ ¬ meetsHoriz g (2 * μ) ∧
      ¬ meetsVert g 0 ∧ ¬ meetsVert g (2 * μ) :=
  ⟨fun ⟨x, hx⟩ => centre_misses_bottom_of_mu_sq_gt g μ hμ2 hcen x hx,
    fun ⟨x, hx⟩ => centre_misses_top_of_mu_sq_gt g μ hμ2 hcen x hx,
    fun ⟨y, hy⟩ => centre_misses_left_of_mu_sq_gt g μ hμ2 hcen y hy,
    fun ⟨y, hy⟩ => centre_misses_right_of_mu_sq_gt g μ hμ2 hcen y hy⟩

theorem RoleSelection_centre_not_meets_outers_of_mu_sq_gt {T : Target}
    (R : RoleSelection T) (hμ2 : 2 < T.μ * T.μ) :
    ¬ meetsHoriz (R.cov.squares R.iC) 0 ∧
      ¬ meetsHoriz (R.cov.squares R.iC) (2 * T.μ) ∧
      ¬ meetsVert (R.cov.squares R.iC) 0 ∧
      ¬ meetsVert (R.cov.squares R.iC) (2 * T.μ) := by
  simpa [Target.centre] using
    centre_not_meets_outers_of_mu_sq_gt (R.cov.squares R.iC) T.μ hμ2 R.hCentre

theorem PointwiseCover_centre_outer_miss_of_mu_sq_gt {T : Target} (cov : PointwiseCover T)
    (hμ2 : 2 < T.μ * T.μ) :
    let R := RoleSelection.ofCover cov
    ¬ meetsHoriz (R.cov.squares R.iC) 0 ∧
      ¬ meetsHoriz (R.cov.squares R.iC) (2 * T.μ) ∧
      ¬ meetsVert (R.cov.squares R.iC) 0 ∧
      ¬ meetsVert (R.cov.squares R.iC) (2 * T.μ) := by
  intro R
  exact RoleSelection_centre_not_meets_outers_of_mu_sq_gt R hμ2

/-- (|c|+|s|)² ≤ 2 < μ² ⇒ |c|+|s| < μ. -/
theorem projWidth_lt_mu_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ)
    (hμ : 0 < μ) (hμ2 : 2 < μ * μ) :
    |g.dir.c| + |g.dir.s| < μ := by
  have hsq := unitDir_projectedWidth_sq_le_two g.dir
  have hpow : (|g.dir.c| + |g.dir.s|) ^ 2 < μ ^ 2 := by nlinarith [hsq]
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hμ) hpow

/-- Helper: μ ≥ 0 from projWidth < μ. -/
theorem mu_nonneg_of_projWidth_lt (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ) : 0 ≤ μ :=
  le_of_lt (lt_of_le_of_lt (add_nonneg (abs_nonneg g.dir.c) (abs_nonneg g.dir.s)) hpw)

/-- SW mid-miss via projected width (works for some μ²≤2 orientations). -/
theorem SW_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (0 : ℚ) hSW
  have hr1 := contains_implies_containsR g x μ ht
  have hd := abs_delta_y_containsR g ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) (x : ℝ) ((μ : ℚ) : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem SW_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (0 : ℚ) hSW
  have hr1 := contains_implies_containsR g μ y ht
  have hd := abs_delta_x_containsR g ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) ((μ : ℚ) : ℝ) (y : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem SW_not_meets_mids_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => SW_misses_hMid_of_projWidth g μ hpw hSW x hx,
    fun ⟨y, hy⟩ => SW_misses_vMid_of_projWidth g μ hpw hSW y hy⟩

theorem SE_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (0 : ℚ) hSE
  have hr1 := contains_implies_containsR g x μ ht
  have hd := abs_delta_y_containsR g ((2 * μ : ℚ) : ℝ) ((0 : ℚ) : ℝ)
    (x : ℝ) ((μ : ℚ) : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem SE_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (0 : ℚ) hSE
  have hr1 := contains_implies_containsR g μ y ht
  have hd := abs_delta_x_containsR g ((2 * μ : ℚ) : ℝ) ((0 : ℚ) : ℝ)
    ((μ : ℚ) : ℝ) (y : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤
        (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have hμR : (0 : ℝ) ≤ (μ : ℝ) := hμ0
    have : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have : ((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by
        push_cast; ring
      rw [this, abs_neg, abs_of_nonneg hμR]
    rwa [this] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem SE_not_meets_mids_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => SE_misses_hMid_of_projWidth g μ hpw hSE x hx,
    fun ⟨y, hy⟩ => SE_misses_vMid_of_projWidth g μ hpw hSE y hy⟩

theorem NE_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (2 * μ) hNE
  have hr1 := contains_implies_containsR g x μ ht
  have hd := abs_delta_y_containsR g ((2 * μ : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ)
    (x : ℝ) ((μ : ℚ) : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤
        (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have : ((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by
        push_cast; ring
      rw [this, abs_neg, abs_of_nonneg hμ0]
    rwa [this] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem NE_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (2 * μ) hNE
  have hr1 := contains_implies_containsR g μ y ht
  have hd := abs_delta_x_containsR g ((2 * μ : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ)
    ((μ : ℚ) : ℝ) (y : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤
        (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have : ((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by
        push_cast; ring
      rw [this, abs_neg, abs_of_nonneg hμ0]
    rwa [this] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem NE_not_meets_mids_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => NE_misses_hMid_of_projWidth g μ hpw hNE x hx,
    fun ⟨y, hy⟩ => NE_misses_vMid_of_projWidth g μ hpw hNE y hy⟩

theorem NW_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (x : ℚ) :
    ¬ RotatedSquare.contains g (x, μ) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (2 * μ) hNW
  have hr1 := contains_implies_containsR g x μ ht
  have hd := abs_delta_y_containsR g ((0 : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ)
    (x : ℝ) ((μ : ℚ) : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤
        (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have : |((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have : ((μ : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by
        push_cast; ring
      rw [this, abs_neg, abs_of_nonneg hμ0]
    rwa [this] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem NW_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (y : ℚ) :
    ¬ RotatedSquare.contains g (μ, y) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (2 * μ) hNW
  have hr1 := contains_implies_containsR g μ y ht
  have hd := abs_delta_x_containsR g ((0 : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ)
    ((μ : ℚ) : ℝ) (y : ℝ) hr0 hr1
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem NW_not_meets_mids_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  ⟨fun ⟨x, hx⟩ => NW_misses_hMid_of_projWidth g μ hpw hNW x hx,
    fun ⟨y, hy⟩ => NW_misses_vMid_of_projWidth g μ hpw hNW y hy⟩

/-- Specialization: μ²>2 ⇒ projWidth < μ ⇒ SW mid-miss (alternate path). -/
theorem SW_not_meets_mids_of_mu_sq_gt_via_proj (g : RotatedSquare) (μ : ℚ)
    (hμ : 0 < μ) (hμ2 : 2 < μ * μ) (hSW : RotatedSquare.contains g (0, 0)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  SW_not_meets_mids_of_projWidth g μ (projWidth_lt_mu_of_mu_sq_gt g μ hμ hμ2) hSW

theorem SE_not_meets_mids_of_mu_sq_gt_via_proj (g : RotatedSquare) (μ : ℚ)
    (hμ : 0 < μ) (hμ2 : 2 < μ * μ) (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  SE_not_meets_mids_of_projWidth g μ (projWidth_lt_mu_of_mu_sq_gt g μ hμ hμ2) hSE

theorem NE_not_meets_mids_of_mu_sq_gt_via_proj (g : RotatedSquare) (μ : ℚ)
    (hμ : 0 < μ) (hμ2 : 2 < μ * μ) (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  NE_not_meets_mids_of_projWidth g μ (projWidth_lt_mu_of_mu_sq_gt g μ hμ hμ2) hNE

theorem NW_not_meets_mids_of_mu_sq_gt_via_proj (g : RotatedSquare) (μ : ℚ)
    (hμ : 0 < μ) (hμ2 : 2 < μ * μ) (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    ¬ meetsHoriz g μ ∧ ¬ meetsVert g μ :=
  NW_not_meets_mids_of_projWidth g μ (projWidth_lt_mu_of_mu_sq_gt g μ hμ hμ2) hNW

/-- When each corner owner has `|c|+|s| < μ`, all four miss both midlines. -/
theorem PointwiseCover_corner_mid_miss_of_projWidth {T : Target} (cov : PointwiseCover T)
    (hpw1 : |(cov.squares (cov.toCornerOwners.i1)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i1)).dir.s| < T.μ)
    (hpw2 : |(cov.squares (cov.toCornerOwners.i2)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i2)).dir.s| < T.μ)
    (hpw3 : |(cov.squares (cov.toCornerOwners.i3)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i3)).dir.s| < T.μ)
    (hpw4 : |(cov.squares (cov.toCornerOwners.i4)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i4)).dir.s| < T.μ) :
    let C := cov.toCornerOwners
    (¬ meetsHoriz (C.squares C.i1) T.μ ∧ ¬ meetsVert (C.squares C.i1) T.μ) ∧
      (¬ meetsHoriz (C.squares C.i2) T.μ ∧ ¬ meetsVert (C.squares C.i2) T.μ) ∧
      (¬ meetsHoriz (C.squares C.i3) T.μ ∧ ¬ meetsVert (C.squares C.i3) T.μ) ∧
      (¬ meetsHoriz (C.squares C.i4) T.μ ∧ ¬ meetsVert (C.squares C.i4) T.μ) := by
  intro C
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SW_not_meets_mids_of_projWidth _ T.μ hpw1 (by simpa [Target.v1] using C.h1)
  · exact SE_not_meets_mids_of_projWidth _ T.μ hpw2 (by simpa [Target.v2] using C.h2)
  · exact NE_not_meets_mids_of_projWidth _ T.μ hpw3 (by simpa [Target.v3] using C.h3)
  · exact NW_not_meets_mids_of_projWidth _ T.μ hpw4 (by simpa [Target.v4] using C.h4)

def rotatedCentreOuterMissMuSqGtClosed : Bool := true
theorem rotatedCentreOuterMissMuSqGtClosed_true :
    rotatedCentreOuterMissMuSqGtClosed = true := rfl

/-- Four-corner projWidth mid-miss API closed (hypothesis `|c|+|s|<μ` per tile). -/
def rotatedProjWidthMidMissClosed : Bool := true
theorem rotatedProjWidthMidMissClosed_true :
    rotatedProjWidthMidMissClosed = true := rfl

/-- Full mid packing for all μ>1 (incl. μ²≤2) and filler tiles still open. -/
def rotatedMidPackingProved : Bool := false
theorem rotatedMidPackingProved_false : rotatedMidPackingProved = false := rfl


/-! ### Clamped mid=0 + corner squareTotal ≤ 2 under projWidth -/

theorem clampedHorizLen_eq_zero_of_empty (g : RotatedSquare) (Y μ : ℚ)
    (h : horizSliceR g Y = ∅) : clampedHorizLen g Y μ = 0 := by
  have hlo : horizChordLo g Y = 0 := by
    simp only [horizChordLo, h, Set.not_nonempty_empty, ↓reduceDIte]
  have hhi : horizChordHi g Y = 0 := by
    simp only [horizChordHi, h, Set.not_nonempty_empty, ↓reduceDIte]
  simp only [clampedHorizLen, hlo, hhi, max_self, sub_zero]
  have : min (0 : ℝ) ((2 : ℝ) * μ) ≤ 0 := min_le_left _ _
  exact max_eq_right this

theorem clampedVertLen_eq_zero_of_empty (g : RotatedSquare) (X μ : ℚ)
    (h : vertSliceR g X = ∅) : clampedVertLen g X μ = 0 := by
  have hlo : vertChordLo g X = 0 := by
    simp only [vertChordLo, h, Set.not_nonempty_empty, ↓reduceDIte]
  have hhi : vertChordHi g X = 0 := by
    simp only [vertChordHi, h, Set.not_nonempty_empty, ↓reduceDIte]
  simp only [clampedVertLen, hlo, hhi, max_self, sub_zero]
  have : min (0 : ℝ) ((2 : ℝ) * μ) ≤ 0 := min_le_left _ _
  exact max_eq_right this

/-- Six clamped grid-line contributions of one tile (real). -/
noncomputable def clampedSquareTotal (g : RotatedSquare) (μ : ℚ) : ℝ :=
  clampedHorizLen g 0 μ + clampedHorizLen g (2 * μ) μ +
    clampedVertLen g 0 μ + clampedVertLen g (2 * μ) μ +
    clampedHorizLen g μ μ + clampedVertLen g μ μ

theorem containsR_SW_misses_top (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : RotatedSquare.contains g (0, 0)) (x : ℝ) :
    ¬ containsR g (x, ((2 * μ : ℚ) : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (0 : ℚ) hSW
  have hd := abs_delta_y_le_two g ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) x ((2 * μ : ℚ) : ℝ) hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have : |((2 * μ : ℚ) : ℝ) - (0 : ℝ)| ≤ (2 : ℝ) := by simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hnn] at this
  linarith

theorem containsR_SW_misses_right (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : RotatedSquare.contains g (0, 0)) (y : ℝ) :
    ¬ containsR g (((2 * μ : ℚ) : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (0 : ℚ) hSW
  have hd := abs_delta_x_le_two g ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) y hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have : |((2 * μ : ℚ) : ℝ) - (0 : ℝ)| ≤ (2 : ℝ) := by simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hnn] at this
  linarith

theorem containsR_SW_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) (x : ℝ) :
    ¬ containsR g (x, (μ : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (0 : ℚ) hSW
  have hd := abs_delta_y_containsR g ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) x (μ : ℝ) hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem containsR_SW_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) (y : ℝ) :
    ¬ containsR g ((μ : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (0 : ℚ) hSW
  have hd := abs_delta_x_containsR g ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) (μ : ℝ) y hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem SW_horizSliceR_top_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    horizSliceR g (2 * μ) = ∅ := by
  ext x; constructor
  · intro hx; exact (containsR_SW_misses_top g μ hμ hSW x hx).elim
  · intro h; exact False.elim h

theorem SW_vertSliceR_right_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    vertSliceR g (2 * μ) = ∅ := by
  ext y; constructor
  · intro hy; exact (containsR_SW_misses_right g μ hμ hSW y hy).elim
  · intro h; exact False.elim h

theorem SW_horizSliceR_hMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    horizSliceR g μ = ∅ := by
  ext x; constructor
  · intro hx; exact (containsR_SW_misses_hMid_of_projWidth g μ hpw hSW x hx).elim
  · intro h; exact False.elim h

theorem SW_vertSliceR_vMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    vertSliceR g μ = ∅ := by
  ext y; constructor
  · intro hy; exact (containsR_SW_misses_vMid_of_projWidth g μ hpw hSW y hy).elim
  · intro h; exact False.elim h

/-- SW tile: under `|c|+|s|<μ` and `μ>1`, clamped six-line total ≤ 2. -/
theorem SW_clampedSquareTotal_le_two_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hOuter := SW_clamped_outer_sum_le_two g μ hμ hSW
  have hTop := clampedHorizLen_eq_zero_of_empty g (2 * μ) μ (SW_horizSliceR_top_empty g μ hμ hSW)
  have hRight := clampedVertLen_eq_zero_of_empty g (2 * μ) μ (SW_vertSliceR_right_empty g μ hμ hSW)
  have hHM := clampedHorizLen_eq_zero_of_empty g μ μ
    (SW_horizSliceR_hMid_empty_of_projWidth g μ hpw hSW)
  have hVM := clampedVertLen_eq_zero_of_empty g μ μ
    (SW_vertSliceR_vMid_empty_of_projWidth g μ hpw hSW)
  simp only [clampedSquareTotal, hTop, hRight, hHM, hVM, add_zero]
  simpa [add_assoc] using hOuter

def rotatedSWClampedSquareTotalProjWidthClosed : Bool := true
theorem rotatedSWClampedSquareTotalProjWidthClosed_true :
    rotatedSWClampedSquareTotalProjWidthClosed = true := rfl


/-! ### SE/NE/NW clampedSquareTotal ≤ 2 under projWidth -/

theorem containsR_SE_misses_top (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (x : ℝ) :
    ¬ containsR g (x, ((2 * μ : ℚ) : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (0 : ℚ) hSE
  have hd := abs_delta_y_le_two g ((2 * μ : ℚ) : ℝ) ((0 : ℚ) : ℝ) x ((2 * μ : ℚ) : ℝ) hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have h' : |((2 * μ : ℚ) : ℝ) - (0 : ℝ)| ≤ (2 : ℝ) := by simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hnn] at h'
  linarith

theorem containsR_SE_misses_left (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (y : ℝ) :
    ¬ containsR g (((0 : ℚ) : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (0 : ℚ) hSE
  have hd := abs_delta_x_le_two g ((2 * μ : ℚ) : ℝ) ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ) y hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have h' : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (2 : ℝ) := by
      simpa [abs_sub_comm] using hd
    have heq : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = ((2 * μ : ℚ) : ℝ) := by
      have h : ((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((2 * μ : ℚ) : ℝ) := by ring
      rw [h, abs_neg, abs_of_nonneg hnn]
    rwa [heq] at h'
  linarith

theorem containsR_SE_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (x : ℝ) :
    ¬ containsR g (x, (μ : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (0 : ℚ) hSE
  have hd := abs_delta_y_containsR g ((2 * μ : ℚ) : ℝ) ((0 : ℚ) : ℝ) x (μ : ℝ) hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem containsR_SE_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) (y : ℝ) :
    ¬ containsR g ((μ : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (0 : ℚ) hSE
  have hd := abs_delta_x_containsR g ((2 * μ : ℚ) : ℝ) ((0 : ℚ) : ℝ) (μ : ℝ) y hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have heq : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have h : (μ : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by push_cast; ring
      rw [h, abs_neg, abs_of_nonneg hμ0]
    rwa [heq] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem SE_horizSliceR_top_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    horizSliceR g (2 * μ) = ∅ := by
  ext x; exact ⟨fun hx => (containsR_SE_misses_top g μ hμ hSE x hx).elim, fun h => h.elim⟩

theorem SE_vertSliceR_left_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    vertSliceR g 0 = ∅ := by
  ext y; exact ⟨fun hy => (containsR_SE_misses_left g μ hμ hSE y hy).elim, fun h => h.elim⟩

theorem SE_horizSliceR_hMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    horizSliceR g μ = ∅ := by
  ext x; exact ⟨fun hx => (containsR_SE_misses_hMid_of_projWidth g μ hpw hSE x hx).elim,
    fun h => h.elim⟩

theorem SE_vertSliceR_vMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    vertSliceR g μ = ∅ := by
  ext y; exact ⟨fun hy => (containsR_SE_misses_vMid_of_projWidth g μ hpw hSE y hy).elim,
    fun h => h.elim⟩

theorem SE_clampedSquareTotal_le_two_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hOuter := SE_clamped_outer_sum_le_two g μ hμ hSE
  have hTop := clampedHorizLen_eq_zero_of_empty g (2 * μ) μ (SE_horizSliceR_top_empty g μ hμ hSE)
  have hLeft := clampedVertLen_eq_zero_of_empty g 0 μ (SE_vertSliceR_left_empty g μ hμ hSE)
  have hHM := clampedHorizLen_eq_zero_of_empty g μ μ
    (SE_horizSliceR_hMid_empty_of_projWidth g μ hpw hSE)
  have hVM := clampedVertLen_eq_zero_of_empty g μ μ
    (SE_vertSliceR_vMid_empty_of_projWidth g μ hpw hSE)
  -- SE outer pack is bottom + right
  simp only [clampedSquareTotal, hTop, hLeft, hHM, hVM, add_zero]
  -- goal: clampedHorizLen g 0 μ + 0 + 0 + clampedVertLen g (2μ) μ + 0 + 0 ≤ 2
  -- = clampedHorizLen g 0 μ + clampedVertLen g (2 * μ) μ ≤ 2
  simpa [add_comm, add_left_comm, add_assoc] using hOuter

theorem containsR_NE_misses_bottom (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (x : ℝ) :
    ¬ containsR g (x, ((0 : ℚ) : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (2 * μ) hNE
  have hd := abs_delta_y_le_two g ((2 * μ : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) x ((0 : ℚ) : ℝ) hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have h' : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (2 : ℝ) := by simpa [abs_sub_comm] using hd
    have heq : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = ((2 * μ : ℚ) : ℝ) := by
      have h : ((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((2 * μ : ℚ) : ℝ) := by ring
      rw [h, abs_neg, abs_of_nonneg hnn]
    rwa [heq] at h'
  linarith

theorem containsR_NE_misses_left (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (y : ℝ) :
    ¬ containsR g (((0 : ℚ) : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (2 * μ) hNE
  have hd := abs_delta_x_le_two g ((2 * μ : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) ((0 : ℚ) : ℝ) y hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have h' : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (2 : ℝ) := by
      simpa [abs_sub_comm] using hd
    have heq : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = ((2 * μ : ℚ) : ℝ) := by
      have h : ((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((2 * μ : ℚ) : ℝ) := by ring
      rw [h, abs_neg, abs_of_nonneg hnn]
    rwa [heq] at h'
  linarith

theorem containsR_NE_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (x : ℝ) :
    ¬ containsR g (x, (μ : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (2 * μ) hNE
  have hd := abs_delta_y_containsR g ((2 * μ : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) x (μ : ℝ) hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have heq : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have h : (μ : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by push_cast; ring
      rw [h, abs_neg, abs_of_nonneg hμ0]
    rwa [heq] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem containsR_NE_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) (y : ℝ) :
    ¬ containsR g ((μ : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (2 * μ) (2 * μ) hNE
  have hd := abs_delta_x_containsR g ((2 * μ : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) (μ : ℝ) y hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have heq : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have h : (μ : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by push_cast; ring
      rw [h, abs_neg, abs_of_nonneg hμ0]
    rwa [heq] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem NE_horizSliceR_bottom_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    horizSliceR g 0 = ∅ := by
  ext x; exact ⟨fun hx => (containsR_NE_misses_bottom g μ hμ hNE x hx).elim, fun h => h.elim⟩

theorem NE_vertSliceR_left_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    vertSliceR g 0 = ∅ := by
  ext y; exact ⟨fun hy => (containsR_NE_misses_left g μ hμ hNE y hy).elim, fun h => h.elim⟩

theorem NE_horizSliceR_hMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    horizSliceR g μ = ∅ := by
  ext x; exact ⟨fun hx => (containsR_NE_misses_hMid_of_projWidth g μ hpw hNE x hx).elim,
    fun h => h.elim⟩

theorem NE_vertSliceR_vMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    vertSliceR g μ = ∅ := by
  ext y; exact ⟨fun hy => (containsR_NE_misses_vMid_of_projWidth g μ hpw hNE y hy).elim,
    fun h => h.elim⟩

theorem NE_clampedSquareTotal_le_two_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hOuter := NE_clamped_outer_sum_le_two g μ hμ hNE
  have hBot := clampedHorizLen_eq_zero_of_empty g 0 μ (NE_horizSliceR_bottom_empty g μ hμ hNE)
  have hLeft := clampedVertLen_eq_zero_of_empty g 0 μ (NE_vertSliceR_left_empty g μ hμ hNE)
  have hHM := clampedHorizLen_eq_zero_of_empty g μ μ
    (NE_horizSliceR_hMid_empty_of_projWidth g μ hpw hNE)
  have hVM := clampedVertLen_eq_zero_of_empty g μ μ
    (NE_vertSliceR_vMid_empty_of_projWidth g μ hpw hNE)
  simp only [clampedSquareTotal, hBot, hLeft, hHM, hVM, add_zero]
  simpa [add_comm, add_left_comm, add_assoc] using hOuter

theorem containsR_NW_misses_bottom (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (x : ℝ) :
    ¬ containsR g (x, ((0 : ℚ) : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (2 * μ) hNW
  have hd := abs_delta_y_le_two g ((0 : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) x ((0 : ℚ) : ℝ) hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have h' : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (2 : ℝ) := by simpa [abs_sub_comm] using hd
    have heq : |((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ)| = ((2 * μ : ℚ) : ℝ) := by
      have h : ((0 : ℚ) : ℝ) - ((2 * μ : ℚ) : ℝ) = -((2 * μ : ℚ) : ℝ) := by ring
      rw [h, abs_neg, abs_of_nonneg hnn]
    rwa [heq] at h'
  linarith

theorem containsR_NW_misses_right (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (y : ℝ) :
    ¬ containsR g (((2 * μ : ℚ) : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (2 * μ) hNW
  have hd := abs_delta_x_le_two g ((0 : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) y hr0 ht
  have hgap : (2 : ℝ) < ((2 * μ : ℚ) : ℝ) := by exact_mod_cast (by nlinarith [hμ] : (2 : ℚ) < 2 * μ)
  have hnn : (0 : ℝ) ≤ ((2 * μ : ℚ) : ℝ) := by
    exact_mod_cast (by nlinarith [hμ] : (0 : ℚ) ≤ 2 * μ)
  have hlen : ((2 * μ : ℚ) : ℝ) ≤ (2 : ℝ) := by
    have h' : |((2 * μ : ℚ) : ℝ) - (0 : ℝ)| ≤ (2 : ℝ) := by simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hnn] at h'
  linarith

theorem containsR_NW_misses_hMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (x : ℝ) :
    ¬ containsR g (x, (μ : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (2 * μ) hNW
  have hd := abs_delta_y_containsR g ((0 : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) x (μ : ℝ) hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    have heq : |(μ : ℝ) - ((2 * μ : ℚ) : ℝ)| = (μ : ℝ) := by
      have h : (μ : ℝ) - ((2 * μ : ℚ) : ℝ) = -((μ : ℝ)) := by push_cast; ring
      rw [h, abs_neg, abs_of_nonneg hμ0]
    rwa [heq] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem containsR_NW_misses_vMid_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) (y : ℝ) :
    ¬ containsR g ((μ : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g (0 : ℚ) (2 * μ) hNW
  have hd := abs_delta_x_containsR g ((0 : ℚ) : ℝ) ((2 * μ : ℚ) : ℝ) (μ : ℝ) y hr0 ht
  have hμ0 : (0 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast mu_nonneg_of_projWidth_lt g μ hpw
  have hle : (μ : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
    have h' : |(μ : ℝ) - (0 : ℝ)| ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
      simpa [abs_sub_comm] using hd
    rwa [sub_zero, abs_of_nonneg hμ0] at h'
  have hpwR : (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) < (μ : ℝ) := by exact_mod_cast hpw
  linarith

theorem NW_horizSliceR_bottom_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    horizSliceR g 0 = ∅ := by
  ext x; exact ⟨fun hx => (containsR_NW_misses_bottom g μ hμ hNW x hx).elim, fun h => h.elim⟩

theorem NW_vertSliceR_right_empty (g : RotatedSquare) (μ : ℚ) (hμ : 1 < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    vertSliceR g (2 * μ) = ∅ := by
  ext y; exact ⟨fun hy => (containsR_NW_misses_right g μ hμ hNW y hy).elim, fun h => h.elim⟩

theorem NW_horizSliceR_hMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    horizSliceR g μ = ∅ := by
  ext x; exact ⟨fun hx => (containsR_NW_misses_hMid_of_projWidth g μ hpw hNW x hx).elim,
    fun h => h.elim⟩

theorem NW_vertSliceR_vMid_empty_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    vertSliceR g μ = ∅ := by
  ext y; exact ⟨fun hy => (containsR_NW_misses_vMid_of_projWidth g μ hpw hNW y hy).elim,
    fun h => h.elim⟩

theorem NW_clampedSquareTotal_le_two_of_projWidth (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hpw : |g.dir.c| + |g.dir.s| < μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hOuter := NW_clamped_outer_sum_le_two g μ hμ hNW
  have hBot := clampedHorizLen_eq_zero_of_empty g 0 μ (NW_horizSliceR_bottom_empty g μ hμ hNW)
  have hRight := clampedVertLen_eq_zero_of_empty g (2 * μ) μ (NW_vertSliceR_right_empty g μ hμ hNW)
  have hHM := clampedHorizLen_eq_zero_of_empty g μ μ
    (NW_horizSliceR_hMid_empty_of_projWidth g μ hpw hNW)
  have hVM := clampedVertLen_eq_zero_of_empty g μ μ
    (NW_vertSliceR_vMid_empty_of_projWidth g μ hpw hNW)
  simp only [clampedSquareTotal, hBot, hRight, hHM, hVM, add_zero]
  simpa [add_comm, add_left_comm, add_assoc] using hOuter

/-- All four corners: clampedSquareTotal ≤ 2 under per-tile `|c|+|s|<μ`. -/
theorem PointwiseCover_corner_clampedSquareTotal_of_projWidth {T : Target}
    (cov : PointwiseCover T) (hμ : 1 < T.μ)
    (hpw1 : |(cov.squares (cov.toCornerOwners.i1)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i1)).dir.s| < T.μ)
    (hpw2 : |(cov.squares (cov.toCornerOwners.i2)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i2)).dir.s| < T.μ)
    (hpw3 : |(cov.squares (cov.toCornerOwners.i3)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i3)).dir.s| < T.μ)
    (hpw4 : |(cov.squares (cov.toCornerOwners.i4)).dir.c| +
      |(cov.squares (cov.toCornerOwners.i4)).dir.s| < T.μ) :
    let C := cov.toCornerOwners
    clampedSquareTotal (C.squares C.i1) T.μ ≤ 2 ∧
      clampedSquareTotal (C.squares C.i2) T.μ ≤ 2 ∧
      clampedSquareTotal (C.squares C.i3) T.μ ≤ 2 ∧
      clampedSquareTotal (C.squares C.i4) T.μ ≤ 2 := by
  intro C
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SW_clampedSquareTotal_le_two_of_projWidth _ T.μ hμ hpw1
      (by simpa [Target.v1] using C.h1)
  · exact SE_clampedSquareTotal_le_two_of_projWidth _ T.μ hμ hpw2
      (by simpa [Target.v2] using C.h2)
  · exact NE_clampedSquareTotal_le_two_of_projWidth _ T.μ hμ hpw3
      (by simpa [Target.v3] using C.h3)
  · exact NW_clampedSquareTotal_le_two_of_projWidth _ T.μ hμ hpw4
      (by simpa [Target.v4] using C.h4)

def rotatedCornerClampedSquareTotalProjWidthClosed : Bool := true
theorem rotatedCornerClampedSquareTotalProjWidthClosed_true :
    rotatedCornerClampedSquareTotalProjWidthClosed = true := rfl

/-! ### Chord ≤ projWidth; mid-sum ≤ 2·projWidth; μ²>2 auto pack; centre outer clamped=0 -/

theorem horizChord_len_le_projWidth (g : RotatedSquare) (Y : ℚ) :
    horizChordHi g Y - horizChordLo g Y ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
  dsimp [horizChordLo, horizChordHi]
  split_ifs with hne
  · have hs : sSup (horizSliceR g Y) ≤
        sInf (horizSliceR g Y) + ((|g.dir.c| : ℝ) + (|g.dir.s| : ℝ)) := by
      apply csSup_le hne
      intro x hx
      have : x - ((|g.dir.c| : ℝ) + (|g.dir.s| : ℝ)) ≤ sInf (horizSliceR g Y) := by
        apply le_csInf hne
        intro y hy
        have hd := abs_horiz_delta_containsR g Y x y hx hy
        cases' abs_cases (x - y) with h' h' <;> linarith
      linarith
    linarith
  · have : (0 : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith

theorem vertChord_len_le_projWidth (g : RotatedSquare) (X : ℚ) :
    vertChordHi g X - vertChordLo g X ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) := by
  dsimp [vertChordLo, vertChordHi]
  split_ifs with hne
  · have hs : sSup (vertSliceR g X) ≤
        sInf (vertSliceR g X) + ((|g.dir.c| : ℝ) + (|g.dir.s| : ℝ)) := by
      apply csSup_le hne
      intro y hy
      have : y - ((|g.dir.c| : ℝ) + (|g.dir.s| : ℝ)) ≤ sInf (vertSliceR g X) := by
        apply le_csInf hne
        intro z hz
        have hd := abs_delta_y_containsR g (X : ℝ) y (X : ℝ) z hy hz
        cases' abs_cases (y - z) with h' h' <;> linarith
      linarith
    linarith
  · have : (0 : ℝ) ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    linarith

theorem clampedHorizLen_le_chordLen (g : RotatedSquare) (Y μ : ℚ) :
    clampedHorizLen g Y μ ≤ horizChordHi g Y - horizChordLo g Y := by
  change max (min (horizChordHi g Y) ((2 : ℝ) * μ) - max (horizChordLo g Y) 0) 0 ≤
    horizChordHi g Y - horizChordLo g Y
  set A := min (horizChordHi g Y) ((2 : ℝ) * μ)
  set B := max (horizChordLo g Y) (0 : ℝ)
  set Hi := horizChordHi g Y
  set Lo := horizChordLo g Y
  have hA : A ≤ Hi := min_le_left _ _
  have hB : Lo ≤ B := le_max_left _ _
  have hlen : A - B ≤ Hi - Lo := by linarith
  have hnn : (0 : ℝ) ≤ Hi - Lo := sub_nonneg.mpr (horizChord_le g Y)
  simpa [A, B, Hi, Lo] using max_le hlen hnn

theorem clampedVertLen_le_chordLen (g : RotatedSquare) (X μ : ℚ) :
    clampedVertLen g X μ ≤ vertChordHi g X - vertChordLo g X := by
  change max (min (vertChordHi g X) ((2 : ℝ) * μ) - max (vertChordLo g X) 0) 0 ≤
    vertChordHi g X - vertChordLo g X
  set A := min (vertChordHi g X) ((2 : ℝ) * μ)
  set B := max (vertChordLo g X) (0 : ℝ)
  set Hi := vertChordHi g X
  set Lo := vertChordLo g X
  have hA : A ≤ Hi := min_le_left _ _
  have hB : Lo ≤ B := le_max_left _ _
  have hlen : A - B ≤ Hi - Lo := by linarith
  have hnn : (0 : ℝ) ≤ Hi - Lo := sub_nonneg.mpr (vertChord_le g X)
  simpa [A, B, Hi, Lo] using max_le hlen hnn

theorem clampedHorizLen_le_projWidth (g : RotatedSquare) (Y μ : ℚ) :
    clampedHorizLen g Y μ ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) :=
  (clampedHorizLen_le_chordLen g Y μ).trans (horizChord_len_le_projWidth g Y)

theorem clampedVertLen_le_projWidth (g : RotatedSquare) (X μ : ℚ) :
    clampedVertLen g X μ ≤ (|g.dir.c| : ℝ) + (|g.dir.s| : ℝ) :=
  (clampedVertLen_le_chordLen g X μ).trans (vertChord_len_le_projWidth g X)

/-- Mid-line clamped contributions of one tile ≤ 2 · projWidth. -/
theorem clamped_mid_sum_le_two_projWidth (g : RotatedSquare) (μ : ℚ) :
    clampedHorizLen g μ μ + clampedVertLen g μ μ ≤
      (2 : ℝ) * ((|g.dir.c| : ℝ) + (|g.dir.s| : ℝ)) := by
  have hh := clampedHorizLen_le_projWidth g μ μ
  have hv := clampedVertLen_le_projWidth g μ μ
  linarith

/-! #### Centre outer ℝ empties + clamped = 0 when μ² > 2 -/

theorem containsR_centre_misses_bottom (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (x : ℝ) :
    ¬ containsR g (x, (0 : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g μ μ hcen
  have hd := distSq_containsR_le_two g (μ : ℝ) (μ : ℝ) x (0 : ℝ) hr0 ht
  have hμ2R : (2 : ℝ) < (μ : ℝ) * (μ : ℝ) := by exact_mod_cast hμ2
  nlinarith [mul_self_nonneg ((μ : ℝ) - x)]

theorem containsR_centre_misses_top (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (x : ℝ) :
    ¬ containsR g (x, ((2 * μ : ℚ) : ℝ)) := by
  intro ht
  have hr0 := contains_implies_containsR g μ μ hcen
  have hd := distSq_containsR_le_two g (μ : ℝ) (μ : ℝ) x ((2 * μ : ℚ) : ℝ) hr0 ht
  have hμ2R : (2 : ℝ) < (μ : ℝ) * (μ : ℝ) := by exact_mod_cast hμ2
  have hY : ((2 * μ : ℚ) : ℝ) = (2 : ℝ) * (μ : ℝ) := by push_cast; ring
  rw [hY] at hd
  nlinarith [mul_self_nonneg ((μ : ℝ) - x)]

theorem containsR_centre_misses_left (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (y : ℝ) :
    ¬ containsR g ((0 : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g μ μ hcen
  have hd := distSq_containsR_le_two g (μ : ℝ) (μ : ℝ) (0 : ℝ) y hr0 ht
  have hμ2R : (2 : ℝ) < (μ : ℝ) * (μ : ℝ) := by exact_mod_cast hμ2
  nlinarith [mul_self_nonneg ((μ : ℝ) - y)]

theorem containsR_centre_misses_right (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) (y : ℝ) :
    ¬ containsR g (((2 * μ : ℚ) : ℝ), y) := by
  intro ht
  have hr0 := contains_implies_containsR g μ μ hcen
  have hd := distSq_containsR_le_two g (μ : ℝ) (μ : ℝ) ((2 * μ : ℚ) : ℝ) y hr0 ht
  have hμ2R : (2 : ℝ) < (μ : ℝ) * (μ : ℝ) := by exact_mod_cast hμ2
  have hX : ((2 * μ : ℚ) : ℝ) = (2 : ℝ) * (μ : ℝ) := by push_cast; ring
  rw [hX] at hd
  nlinarith [mul_self_nonneg ((μ : ℝ) - y)]

theorem centre_horizSliceR_bottom_empty (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) :
    horizSliceR g 0 = ∅ := by
  ext x; constructor
  · intro hx
    have : containsR g (x, (0 : ℝ)) := by simpa [horizSliceR] using hx
    exact (containsR_centre_misses_bottom g μ hμ2 hcen x this).elim
  · intro h; exact h.elim

theorem centre_horizSliceR_top_empty (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) :
    horizSliceR g (2 * μ) = ∅ := by
  ext x; constructor
  · intro hx
    have : containsR g (x, ((2 * μ : ℚ) : ℝ)) := by simpa [horizSliceR] using hx
    exact (containsR_centre_misses_top g μ hμ2 hcen x this).elim
  · intro h; exact h.elim

theorem centre_vertSliceR_left_empty (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) :
    vertSliceR g 0 = ∅ := by
  ext y; constructor
  · intro hy
    have : containsR g ((0 : ℝ), y) := by simpa [vertSliceR] using hy
    exact (containsR_centre_misses_left g μ hμ2 hcen y this).elim
  · intro h; exact h.elim

theorem centre_vertSliceR_right_empty (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) :
    vertSliceR g (2 * μ) = ∅ := by
  ext y; constructor
  · intro hy
    have : containsR g (((2 * μ : ℚ) : ℝ), y) := by simpa [vertSliceR] using hy
    exact (containsR_centre_misses_right g μ hμ2 hcen y this).elim
  · intro h; exact h.elim

theorem centre_outer_clamped_eq_zero (g : RotatedSquare) (μ : ℚ) (hμ2 : 2 < μ * μ)
    (hcen : RotatedSquare.contains g (μ, μ)) :
    clampedHorizLen g 0 μ = 0 ∧ clampedHorizLen g (2 * μ) μ = 0 ∧
      clampedVertLen g 0 μ = 0 ∧ clampedVertLen g (2 * μ) μ = 0 :=
  ⟨clampedHorizLen_eq_zero_of_empty g 0 μ (centre_horizSliceR_bottom_empty g μ hμ2 hcen),
    clampedHorizLen_eq_zero_of_empty g (2 * μ) μ (centre_horizSliceR_top_empty g μ hμ2 hcen),
    clampedVertLen_eq_zero_of_empty g 0 μ (centre_vertSliceR_left_empty g μ hμ2 hcen),
    clampedVertLen_eq_zero_of_empty g (2 * μ) μ (centre_vertSliceR_right_empty g μ hμ2 hcen)⟩

theorem RoleSelection_centre_outer_clamped_eq_zero {T : Target}
    (R : RoleSelection T) (hμ2 : 2 < T.μ * T.μ) :
    clampedHorizLen (R.cov.squares R.iC) 0 T.μ = 0 ∧
      clampedHorizLen (R.cov.squares R.iC) (2 * T.μ) T.μ = 0 ∧
      clampedVertLen (R.cov.squares R.iC) 0 T.μ = 0 ∧
      clampedVertLen (R.cov.squares R.iC) (2 * T.μ) T.μ = 0 := by
  simpa [Target.centre] using
    centre_outer_clamped_eq_zero (R.cov.squares R.iC) T.μ hμ2 R.hCentre

theorem PointwiseCover_centre_outer_clamped_eq_zero {T : Target}
    (cov : PointwiseCover T) (hμ2 : 2 < T.μ * T.μ) :
    let R := RoleSelection.ofCover cov
    clampedHorizLen (R.cov.squares R.iC) 0 T.μ = 0 ∧
      clampedHorizLen (R.cov.squares R.iC) (2 * T.μ) T.μ = 0 ∧
      clampedVertLen (R.cov.squares R.iC) 0 T.μ = 0 ∧
      clampedVertLen (R.cov.squares R.iC) (2 * T.μ) T.μ = 0 := by
  intro R
  exact RoleSelection_centre_outer_clamped_eq_zero R hμ2

/-! #### Auto corner clampedSquareTotal ≤ 2 when μ² > 2 -/

theorem SW_clampedSquareTotal_le_two_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hμ2 : 2 < μ * μ)
    (hSW : RotatedSquare.contains g (0, 0)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hμ0 : (0 : ℚ) < μ := lt_trans (by norm_num : (0 : ℚ) < 1) hμ
  have hpw := projWidth_lt_mu_of_mu_sq_gt g μ hμ0 hμ2
  exact SW_clampedSquareTotal_le_two_of_projWidth g μ hμ hpw hSW

theorem SE_clampedSquareTotal_le_two_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hμ2 : 2 < μ * μ)
    (hSE : RotatedSquare.contains g (2 * μ, 0)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hμ0 : (0 : ℚ) < μ := lt_trans (by norm_num : (0 : ℚ) < 1) hμ
  have hpw := projWidth_lt_mu_of_mu_sq_gt g μ hμ0 hμ2
  exact SE_clampedSquareTotal_le_two_of_projWidth g μ hμ hpw hSE

theorem NE_clampedSquareTotal_le_two_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hμ2 : 2 < μ * μ)
    (hNE : RotatedSquare.contains g (2 * μ, 2 * μ)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hμ0 : (0 : ℚ) < μ := lt_trans (by norm_num : (0 : ℚ) < 1) hμ
  have hpw := projWidth_lt_mu_of_mu_sq_gt g μ hμ0 hμ2
  exact NE_clampedSquareTotal_le_two_of_projWidth g μ hμ hpw hNE

theorem NW_clampedSquareTotal_le_two_of_mu_sq_gt (g : RotatedSquare) (μ : ℚ)
    (hμ : 1 < μ) (hμ2 : 2 < μ * μ)
    (hNW : RotatedSquare.contains g (0, 2 * μ)) :
    clampedSquareTotal g μ ≤ 2 := by
  have hμ0 : (0 : ℚ) < μ := lt_trans (by norm_num : (0 : ℚ) < 1) hμ
  have hpw := projWidth_lt_mu_of_mu_sq_gt g μ hμ0 hμ2
  exact NW_clampedSquareTotal_le_two_of_projWidth g μ hμ hpw hNW

/-- All four corner owners: clampedSquareTotal ≤ 2 when μ² > 2 (no per-tile projWidth hyp). -/
theorem PointwiseCover_corner_clampedSquareTotal_of_mu_sq_gt {T : Target}
    (cov : PointwiseCover T) (hμ : 1 < T.μ) (hμ2 : 2 < T.μ * T.μ) :
    let C := cov.toCornerOwners
    clampedSquareTotal (C.squares C.i1) T.μ ≤ 2 ∧
      clampedSquareTotal (C.squares C.i2) T.μ ≤ 2 ∧
      clampedSquareTotal (C.squares C.i3) T.μ ≤ 2 ∧
      clampedSquareTotal (C.squares C.i4) T.μ ≤ 2 := by
  intro C
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SW_clampedSquareTotal_le_two_of_mu_sq_gt _ T.μ hμ hμ2
      (by simpa [Target.v1] using C.h1)
  · exact SE_clampedSquareTotal_le_two_of_mu_sq_gt _ T.μ hμ hμ2
      (by simpa [Target.v2] using C.h2)
  · exact NE_clampedSquareTotal_le_two_of_mu_sq_gt _ T.μ hμ hμ2
      (by simpa [Target.v3] using C.h3)
  · exact NW_clampedSquareTotal_le_two_of_mu_sq_gt _ T.μ hμ hμ2
      (by simpa [Target.v4] using C.h4)

def rotatedMuSqGtCornerPackClosed : Bool := true
theorem rotatedMuSqGtCornerPackClosed_true : rotatedMuSqGtCornerPackClosed = true := rfl

def rotatedCentreOuterClampedZeroClosed : Bool := true
theorem rotatedCentreOuterClampedZeroClosed_true :
    rotatedCentreOuterClampedZeroClosed = true := rfl

def rotatedChordLeProjWidthClosed : Bool := true
theorem rotatedChordLeProjWidthClosed_true : rotatedChordLeProjWidthClosed = true := rfl


end S6.RotatedChordMeasure
