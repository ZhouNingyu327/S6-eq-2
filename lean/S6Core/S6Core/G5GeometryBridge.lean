import Mathlib.Tactic
import S6Core.G5Budget
import S6Core.G5ExclusionFrag
import S6Core.AxisGridContribution
import S6Core.AxisGridCover
import S6Core.ParallelBudget
import S6Core.CoveringGeometry
import S6Core.MainTheorem
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.TopClassExhaustiveness
import S6Core.Exhaustiveness
import S6Core.OwnershipBridge

/-!
# G5 geometry → budget export (bridge refinement)

Refines the three open `G5k*Bridge` Props into **finer geometric export Props**
and proves:

* export Props ⇒ bridges ⇒ `G5Exclusion` (composition);
* axis-aligned outer/corner length lemmas feeding the `corners ≤ 8` bound;
* abstract packaging `RigidSquareGridExport → G5GridHyp → False`.

Full discharge of the export Props from arbitrary `PointwiseCover`
(rotated rigid squares) remains open — that is the honest residual wall.
-/

namespace S6.G5GeometryBridge

open S6.G5Budget
open S6.G5ExclusionFrag
open S6.AxisGridContribution
open S6.ParallelBudget
open S6.CoveringGeometry
open S6.MainTheorem
open S6.Obligation2
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.TopClassExhaustiveness
open S6.Exhaustiveness
open S6.OwnershipBridge

/-! ## Abstract export package → `G5GridHyp` -/

structure RigidSquareGridExport (μ : ℚ) where
  corners : ℚ
  CF : ℚ
  hμ : 1 < μ
  hcorners : corners ≤ 8
  hCF : CF < 4
  hcover : (12 : ℚ) * μ ≤ corners + CF

def RigidSquareGridExport.toHyp {μ : ℚ} (E : RigidSquareGridExport μ) : G5GridHyp where
  μ := μ
  corners := E.corners
  CF := E.CF
  hμ := E.hμ
  hcorners := E.hcorners
  hCF := E.hCF
  hcover := E.hcover

theorem RigidSquareGridExport.impossible {μ : ℚ} (E : RigidSquareGridExport μ) : False :=
  (E.toHyp).impossible

theorem nonempty_G5GridHyp_of_export {μ : ℚ} (E : RigidSquareGridExport μ) :
    Nonempty G5GridHyp :=
  ⟨E.toHyp⟩

/-! ## Finer geometric export Props (still open for full PointwiseCover) -/

/-- k=0: cover exports corners≤8, CF<4, and the grid covering inequality. -/
def G5k0GeomExport : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        Nonempty (RigidSquareGridExport T.μ)

/-- k=2: cover exports one of the three R2 packages. -/
def G5k2GeomExport : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨2, by decide⟩ →
        Nonempty G5OppositeMidHyp ∨
          Nonempty G5AdjacentMidHyp ∨
            Nonempty (RigidSquareGridExport T.μ)

/-- k=1: cover exports side-gap / no-side-gap / opposite-mid budget. -/
def G5k1GeomExport : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨1, by decide⟩ →
        (∃ h : BudgetHyp, (12 : ℚ) * h.μ ≤ 8 + 3 * h.B + h.vF) ∨
          (∃ (B : ℚ), B < 1 ∧ (12 : ℚ) * T.μ ≤ 8 + 2 * B + 2 * T.μ) ∨
            Nonempty G5OppositeMidHyp

/-! ## Export Props ⇒ bridges (proved) -/

theorem G5k0Bridge_of_geomExport (h : G5k0GeomExport) : G5k0Bridge := by
  intro T cov hcls hk
  exact (h T cov hcls hk).elim fun E => nonempty_G5GridHyp_of_export E

theorem G5k2Bridge_of_geomExport (h : G5k2GeomExport) : G5k2Bridge := by
  intro T cov hcls hk
  rcases h T cov hcls hk with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.elim fun E => nonempty_G5GridHyp_of_export E))

theorem G5k1Bridge_of_geomExport (h : G5k1GeomExport) : G5k1Bridge := h

/-- Conditional G5Exclusion from the three **geometric export** Props. -/
theorem G5Exclusion_of_geomExports
    (hk2 : G5k2GeomExport) (hk0 : G5k0GeomExport) (hk1 : G5k1GeomExport) :
    G5Exclusion :=
  G5Exclusion_of_bridges
    (G5k2Bridge_of_geomExport hk2)
    (G5k0Bridge_of_geomExport hk0)
    (G5k1Bridge_of_geomExport hk1)

/-! ## Axis-aligned corner / outer bounds (proved geometry fragment) -/

/-- Outer four sides of an axis square each contribute ≤1 ⇒ sum ≤4. -/
theorem axis_outer_sum_le_four (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ) :
    bottomLen s μ + topLen s μ + leftLen s μ + rightLen s μ ≤ 4 := by
  have hb := bottomLen_le_one s μ hμ
  have ht := topLen_le_one s μ hμ
  have hl := leftLen_le_one s μ hμ
  have hr := rightLen_le_one s μ hμ
  nlinarith

/-- Canonical SW corner tile contributes exactly 2 on the outer sides. -/
theorem axis_sw_outer_eq_two (μ : ℚ) (hμ : 1 < μ) :
    bottomLen swCorner μ + topLen swCorner μ +
      leftLen swCorner μ + rightLen swCorner μ = 2 :=
  swCorner_outer_contrib μ hμ

/-- Four tiles each contributing ≤2 on outer sides ⇒ corners budget ≤8. -/
theorem corners_budget_le_eight (c1 c2 c3 c4 : ℚ)
    (h1 : c1 ≤ 2) (h2 : c2 ≤ 2) (h3 : c3 ≤ 2) (h4 : c4 ≤ 2) :
    c1 + c2 + c3 + c4 ≤ 8 :=
  four_corners_outer_le_eight c1 c2 c3 c4 h1 h2 h3 h4

/-- Re-export: abstract R2 covering inequality is impossible under corners≤8, CF<4. -/
theorem axis_style_grid_impossible (μ corners CF : ℚ) (hμ : 1 < μ)
    (hcorners : corners ≤ 8) (hCF : CF < 4)
    (hcover : (12 : ℚ) * μ ≤ corners + CF) : False :=
  (RigidSquareGridExport.mk corners CF hμ hcorners hCF hcover).impossible

/-- Named residual wall (not a vacuous Prop): rotated corner outer-side
contribution ≤2 per tile is not yet a Lean statement over chord measures. -/
def rotatedCornerBoundOpenNote : String :=
  "Need: each corner-owning RotatedSquare of a PointwiseCover contributes    ≤2 to the four outer sides of [0,2μ]² (axis SW fragment proves =2)."

def rotatedCFBoundOpenNote : String :=
  "Need: centre/filler contribution CF < 4, or CF ≤ 2μ+2B with μ+B<2 from    ParallelBudgetData."

def gridCoverInequalityOpenNote : String :=
  "Need: 12μ ≤ corners + CF from PointwiseCover of the six grid lines."

/-! ## Status flags -/

def g5GeomExportReductionClosed : Bool := true
theorem g5GeomExportReductionClosed_true : g5GeomExportReductionClosed = true := rfl

def g5GeomExportsProvedFromPointwiseCover : Bool := false
theorem g5GeomExportsProvedFromPointwiseCover_false :
    g5GeomExportsProvedFromPointwiseCover = false := rfl

def openG5GeomExports : List String :=
  ["G5k0GeomExport", "G5k2GeomExport", "G5k1GeomExport",
   "rotatedCornerBoundOpenNote", "rotatedCFBoundOpenNote",
   "gridCoverInequalityOpenNote"]

def axisCornerOuterFragmentClosed : Bool := true
theorem axisCornerOuterFragmentClosed_true : axisCornerOuterFragmentClosed = true := rfl


/-! ## Axis four-corner owners ⇒ corners ≤ 8 (feeds G5k0GeomExport) -/

theorem axis_corners_le_eight_of_owners
    (sSW sSE sNE sNW : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : sSW.contains (0, 0)) (hSE : sSE.contains (2 * μ, 0))
    (hNE : sNE.contains (2 * μ, 2 * μ)) (hNW : sNW.contains (0, 2 * μ)) :
    (bottomLen sSW μ + topLen sSW μ + leftLen sSW μ + rightLen sSW μ) +
      (bottomLen sSE μ + topLen sSE μ + leftLen sSE μ + rightLen sSE μ) +
      (bottomLen sNE μ + topLen sNE μ + leftLen sNE μ + rightLen sNE μ) +
      (bottomLen sNW μ + topLen sNW μ + leftLen sNW μ + rightLen sNW μ) ≤ 8 :=
  axis_four_corner_owners_outer_le_eight sSW sSE sNE sNW μ hμ hSW hSE hNE hNW

/-- Axis model: corners≤8 + CF<4 + cover ineq ⇒ False (unconditional algebra). -/
theorem axis_G5Grid_impossible_of_bounds (μ corners CF : ℚ) (hμ : 1 < μ)
    (hcorners : corners ≤ 8) (hCF : CF < 4)
    (hcover : (12 : ℚ) * μ ≤ corners + CF) : False :=
  axis_style_grid_impossible μ corners CF hμ hcorners hCF hcover

/-- Axis cover: four corner-owners (outer≤2 each) + CF≤4 + cover ineq ⇒ False.
Uses non-strict CF≤4 (two filler mid-sums), which still beats `12μ > 12`. -/
theorem axis_cover_impossible_of_cf_export
    (sSW sSE sNE sNW : AxisSquare) (μ CF : ℚ) (hμ : 1 < μ) (hCF : CF ≤ 4)
    (hSW : sSW.contains (0, 0)) (hSE : sSE.contains (2 * μ, 0))
    (hNE : sNE.contains (2 * μ, 2 * μ)) (hNW : sNW.contains (0, 2 * μ))
    (hcover :
      (12 : ℚ) * μ ≤
        (bottomLen sSW μ + topLen sSW μ + leftLen sSW μ + rightLen sSW μ) +
          (bottomLen sSE μ + topLen sSE μ + leftLen sSE μ + rightLen sSE μ) +
          (bottomLen sNE μ + topLen sNE μ + leftLen sNE μ + rightLen sNE μ) +
          (bottomLen sNW μ + topLen sNW μ + leftLen sNW μ + rightLen sNW μ) + CF) :
    False := by
  set corners :=
    (bottomLen sSW μ + topLen sSW μ + leftLen sSW μ + rightLen sSW μ) +
      (bottomLen sSE μ + topLen sSE μ + leftLen sSE μ + rightLen sSE μ) +
      (bottomLen sNE μ + topLen sNE μ + leftLen sNE μ + rightLen sNE μ) +
      (bottomLen sNW μ + topLen sNW μ + leftLen sNW μ + rightLen sNW μ)
  have hcorners := axis_corners_le_eight_of_owners sSW sSE sNE sNW μ hμ hSW hSE hNE hNW
  exact axis_grid_cover_impossible_le μ corners CF hμ hcorners hCF hcover

/-- Specialisation: CF = sum of two filler mid contribs (each ≤2). -/
theorem axis_cover_impossible_of_two_fillers
    (sSW sSE sNE sNW s1 s2 : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hSW : sSW.contains (0, 0)) (hSE : sSE.contains (2 * μ, 0))
    (hNE : sNE.contains (2 * μ, 2 * μ)) (hNW : sNW.contains (0, 2 * μ))
    (hcover :
      (12 : ℚ) * μ ≤
        (bottomLen sSW μ + topLen sSW μ + leftLen sSW μ + rightLen sSW μ) +
          (bottomLen sSE μ + topLen sSE μ + leftLen sSE μ + rightLen sSE μ) +
          (bottomLen sNE μ + topLen sNE μ + leftLen sNE μ + rightLen sNE μ) +
          (bottomLen sNW μ + topLen sNW μ + leftLen sNW μ + rightLen sNW μ) +
          ((hMidLen s1 μ + vMidLen s1 μ) + (hMidLen s2 μ + vMidLen s2 μ))) :
    False := by
  have hCF := axis_two_filler_mid_le_four s1 s2 μ hμ
  exact axis_cover_impossible_of_cf_export sSW sSE sNE sNW μ
    ((hMidLen s1 μ + vMidLen s1 μ) + (hMidLen s2 μ + vMidLen s2 μ))
    hμ hCF hSW hSE hNE hNW hcover

def axisFourCornerBoundClosed : Bool := true
theorem axisFourCornerBoundClosed_true : axisFourCornerBoundClosed = true := rfl


open S6.AxisGridCover

/-- Re-export: real six-line axis cover ⇒ ∑ contrib ≥ 12μ. -/
theorem axis_grid_cover_inequality (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridLineCover μ squares) :
    (12 : ℚ) * μ ≤ ∑ i : Fin 6, axisGridContrib (squares i) μ :=
  axis_grid_cover_sum_rat μ hμ squares H

/-- Axis line cover + corners≤8 + CF≤4 on a contrib split ⇒ False. -/
theorem axis_G5_of_line_cover_corner_cf (μ : ℚ) (hμ : 1 < μ)
    (squares : Fin 6 → AxisSquare) (H : AxisGridLineCover μ squares)
    (corners CF : ℚ) (hcorners : corners ≤ 8) (hCF : CF ≤ 4)
    (hsplit : ∑ i : Fin 6, axisGridContrib (squares i) μ ≤ corners + CF) :
    False :=
  axis_line_cover_impossible_of_corner_cf μ hμ squares H corners CF hcorners hCF hsplit

def axisGridCoverIneqInBridge : Bool := true
theorem axisGridCoverIneqInBridge_true : axisGridCoverIneqInBridge = true := rfl


/-- ℚ six-line cover lifts to real `AxisGridLineCover`. -/
theorem axis_line_cover_of_rat (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares) :
    AxisGridLineCover μ squares :=
  AxisGridLineCover_of_ratCover μ hμ squares H

/-- Axis G5k0 model: ℚ grid cover + corner/filler packing ⇒ False. -/
theorem axis_G5k0_model_impossible (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares)
    (iSW iSE iNE iNW j1 j2 : Fin 6)
    (hSW : (squares iSW).contains (0, 0))
    (hSE : (squares iSE).contains (2 * μ, 0))
    (hNE : (squares iNE).contains (2 * μ, 2 * μ))
    (hNW : (squares iNW).contains (0, 2 * μ))
    (hsplit :
      ∑ k : Fin 6, axisGridContrib (squares k) μ ≤
        outerContrib (squares iSW) μ + outerContrib (squares iSE) μ +
          outerContrib (squares iNE) μ + outerContrib (squares iNW) μ +
          midContrib (squares j1) μ + midContrib (squares j2) μ) :
    False :=
  axis_rat_cover_impossible_of_owners_fillers μ hμ squares H
    iSW iSE iNE iNW j1 j2 hSW hSE hNE hNW hsplit

def axisRatCoverToLineCoverClosed : Bool := true
theorem axisRatCoverToLineCoverClosed_true : axisRatCoverToLineCoverClosed = true := rfl


/-- Axis G5k0 under role geometry packing (non-owner outer=0, non-filler mid=0). -/
theorem axis_G5k0_of_role_geometry (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares)
    (iSW iSE iNE iNW j1 j2 : Fin 6)
    (hSW : (squares iSW).contains (0, 0))
    (hSE : (squares iSE).contains (2 * μ, 0))
    (hNE : (squares iNE).contains (2 * μ, 2 * μ))
    (hNW : (squares iNW).contains (0, 2 * μ))
    (hdSW : iSW ≠ iSE) (hdSW3 : iSW ≠ iNE) (hdSW4 : iSW ≠ iNW)
    (hdSE3 : iSE ≠ iNE) (hdSE4 : iSE ≠ iNW) (hdNE4 : iNE ≠ iNW)
    (hj : j1 ≠ j2)
    (houter : OnlyOwnersTouchOuter μ squares iSW iSE iNE iNW)
    (hmid : OnlyFillersTouchMid μ squares j1 j2) :
    False :=
  axis_rat_cover_impossible_of_role_geometry μ hμ squares H
    iSW iSE iNE iNW j1 j2 hSW hSE hNE hNW
    hdSW hdSW3 hdSW4 hdSE3 hdSE4 hdNE4 hj houter hmid

/-- Interior tiles have outer contrib 0 (feeds OnlyOwnersTouchOuter). -/
theorem axis_interior_outer_zero (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (hx0 : (0 : ℚ) < s.x) (hx1 : s.x + 1 < 2 * μ)
    (hy0 : (0 : ℚ) < s.y) (hy1 : s.y + 1 < 2 * μ) :
    outerContrib s μ = 0 :=
  interior_outerContrib_eq_zero s μ hμ hx0 hx1 hy0 hy1

def axisG5k0RoleGeometryClosed : Bool := true
theorem axisG5k0RoleGeometryClosed_true : axisG5k0RoleGeometryClosed = true := rfl


/-- Re-export: ℚ cover + `AxisG5k0Roles` ⇒ False. -/
theorem axis_G5k0_roles_impossible (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares) (R : AxisG5k0Roles μ squares) : False :=
  axis_G5k0_impossible_of_roles μ squares H R

/-- From roles + rat cover, build `G5GridHypLe` (corners≤8, CF≤4, cover ineq). -/
theorem G5GridHypLe_of_axis_roles (μ : ℚ) (squares : Fin 6 → AxisSquare)
    (H : AxisGridRatCover μ squares) (R : AxisG5k0Roles μ squares) :
    Nonempty S6.G5Budget.G5GridHypLe := by
  have hpack := packing_of_role_geometry μ squares
    R.iSW R.iSE R.iNE R.iNW R.j1 R.j2
    R.hdSW R.hdSW3 R.hdSW4 R.hdSE3 R.hdSE4 R.hdNE4 R.hj
    R.onlyOwners R.onlyFillers
  have hge := axis_rat_cover_sum μ R.hμ squares H
  set corners :=
    outerContrib (squares R.iSW) μ + outerContrib (squares R.iSE) μ +
      outerContrib (squares R.iNE) μ + outerContrib (squares R.iNW) μ
  set CF := midContrib (squares R.j1) μ + midContrib (squares R.j2) μ
  have hcorners : corners ≤ 8 := by
    dsimp [corners, outerContrib]
    exact axis_four_corner_owners_outer_le_eight
      (squares R.iSW) (squares R.iSE) (squares R.iNE) (squares R.iNW) μ R.hμ
      R.hSW R.hSE R.hNE R.hNW
  have hCF : CF ≤ 4 := by
    dsimp [CF, midContrib]
    exact axis_two_filler_mid_le_four (squares R.j1) (squares R.j2) μ R.hμ
  have hcover : (12 : ℚ) * μ ≤ corners + CF := by
    have : ∑ k : Fin 6, axisGridContrib (squares k) μ = corners + CF := by
      simpa [corners, CF, add_assoc] using hpack
    exact le_trans hge (le_of_eq this)
  exact ⟨⟨μ, corners, CF, R.hμ, hcorners, hCF, hcover⟩⟩

/-- Conditional: if every G5 k=0 PointwiseCover realises axis roles + rat cover,
then `G5k0Bridge` holds (via `False` from roles, or equivalently nonempty grid hyp).
Here we package the axis-model bridge Prop. -/
def AxisG5k0CoverBridge : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ (squares : Fin 6 → AxisSquare),
          AxisGridRatCover T.μ squares ∧ Nonempty (AxisG5k0Roles T.μ squares)

theorem G5k0_impossible_of_axis_bridge (h : AxisG5k0CoverBridge)
    (T : Target) (cov : PointwiseCover T)
    (hcls : isG5Class cov)
    (hk : (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩) :
    False := by
  rcases h T cov hcls hk with ⟨squares, Hrat, ⟨R⟩⟩
  exact axis_G5k0_impossible_of_roles T.μ squares Hrat R

def axisG5k0RolesToImpossibleClosed : Bool := true
theorem axisG5k0RolesToImpossibleClosed_true :
    axisG5k0RolesToImpossibleClosed = true := rfl


/-- Axis cover-bridge package ⇒ `G5k0Bridge`. -/
theorem G5k0Bridge_of_axisCoverBridge (h : AxisG5k0CoverBridge) : G5k0Bridge := by
  intro T cov hcls hk
  exact False.elim (G5k0_impossible_of_axis_bridge h T cov hcls hk)

/-- Axis cover-bridge ⇒ `G5k0GeomExport` (rebuild corners/CF from roles). -/
theorem G5k0GeomExport_of_axisCoverBridge (h : AxisG5k0CoverBridge) : G5k0GeomExport := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨squares, Hrat, ⟨R⟩⟩
  have hpack := packing_of_role_geometry T.μ squares
    R.iSW R.iSE R.iNE R.iNW R.j1 R.j2
    R.hdSW R.hdSW3 R.hdSW4 R.hdSE3 R.hdSE4 R.hdNE4 R.hj
    R.onlyOwners R.onlyFillers
  have hge := axis_rat_cover_sum T.μ R.hμ squares Hrat
  set corners :=
    outerContrib (squares R.iSW) T.μ + outerContrib (squares R.iSE) T.μ +
      outerContrib (squares R.iNE) T.μ + outerContrib (squares R.iNW) T.μ
  set CF := midContrib (squares R.j1) T.μ + midContrib (squares R.j2) T.μ
  have hcorners : corners ≤ 8 := by
    dsimp [corners, outerContrib]
    exact axis_four_corner_owners_outer_le_eight
      (squares R.iSW) (squares R.iSE) (squares R.iNE) (squares R.iNW) T.μ R.hμ
      R.hSW R.hSE R.hNE R.hNW
  have hCF : CF ≤ 4 := by
    dsimp [CF, midContrib]
    exact axis_two_filler_mid_le_four (squares R.j1) (squares R.j2) T.μ R.hμ
  have hcover : (12 : ℚ) * T.μ ≤ corners + CF := by
    have : ∑ k : Fin 6, axisGridContrib (squares k) T.μ = corners + CF := by
      simpa [corners, CF, add_assoc] using hpack
    exact le_trans hge (le_of_eq this)
  have hstrict : CF < 4 := by
    by_contra hne
    have hge4 : (4 : ℚ) ≤ CF := le_of_not_gt hne
    have hEq : CF = 4 := le_antisymm hCF hge4
    have : (12 : ℚ) * T.μ ≤ corners + 4 := by simpa [hEq] using hcover
    nlinarith [T.hμ, hcorners, this]
  exact ⟨⟨corners, CF, T.hμ, hcorners, hstrict, hcover⟩⟩

def axisG5k0CoverBridgeProved : Bool := false
theorem axisG5k0CoverBridgeProved_false : axisG5k0CoverBridgeProved = false := rfl

end S6.G5GeometryBridge
