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
Open: inhabit RotatedSixLineMeasureLift / RotatedLineMeasureLift from rat cover.
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

/-- Open: lift one line of `RotatedGridRatCover` to a Euclidean interval cover. -/
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

def rotatedLineMeasureLiftProved : Bool := false
theorem rotatedLineMeasureLiftProved_false : rotatedLineMeasureLiftProved = false := rfl

end S6.RotatedChordMeasure
