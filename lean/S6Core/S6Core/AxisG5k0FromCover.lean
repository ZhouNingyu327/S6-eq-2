import Mathlib.Tactic
import S6Core.AxisGridCover
import S6Core.AxisGridContribution
import S6Core.OwnershipBridge
import S6Core.RigidMotionChart
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.Obligation2Norm
import S6Core.PdfNormalisation
import S6Core.G5ExclusionFrag
import S6Core.G5GeometryBridge
import S6Core.G5Budget
import S6Core.ChordLength
import S6Core.Exhaustiveness

/-!
# Axis G5 k=0 roles / rat-cover from axis-aligned PointwiseCover

Proved:
* axis-aligned `RigidMotion` ↔ `AxisSquare` containment
* centre-containing axis square ⇒ strict interior (μ>1)
* axis pointwise cover of `[0,2μ]²` ⇒ `AxisGridRatCover`
* six pairwise-distinct `Fin 6` indices partition
* corner owners + two centre fillers ⇒ `AxisG5k0Roles`
* `AxisAlignedG5k0Realisation` ⇒ `AxisG5k0CoverBridge` ⇒ G5k0 export/bridge

Proved: `pullback_self`; SE(2) `comp`/`inverse`/`pullback_contains_iff`;
body-F∋body-O ↔ world-F∋O; manuscript fHasO ↔ world F∋O when C=`identityPose`;
axis pullback/translate→identity; body-chart packaging.

Proved: same-dir ⇒ body-chart axis-aligned + C=`identityPose` packaging.
Open: inhabit `AxisAlignedIdentityCRealisation` / `BodyChartAxisG5k0Realisation`
for every G5 k=0 cover, or `RotatedChordCoverIneq` from general covers.
-/

namespace S6.AxisG5k0FromCover

open S6.OwnershipBridge
open S6.RigidMotionChart (rotateBy inAxisSquare)
open S6.AxisGridCover
open S6.AxisGridContribution
open S6.Obligation2
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.Obligation2Norm
open S6.PdfNormalisation
open S6.G5ExclusionFrag
open S6.G5GeometryBridge
open S6.G5Budget
open S6.Exhaustiveness
open S6.TopClassExhaustiveness
open S6.ChordLength (UnitDir)
open S6.RigidMotionChart

/-! ## Axis-aligned rigid motions ↔ AxisSquare -/

def isAxisAligned (g : RotatedSquare) : Prop :=
  g.dir.c = 1 ∧ g.dir.s = 0

def toAxisSquare (g : RotatedSquare) : AxisSquare :=
  ⟨g.shift.1, g.shift.2⟩

theorem axisAligned_rotateInv_id (g : RotatedSquare) (h : isAxisAligned g) (p : ℚ × ℚ) :
    rotateInv g.dir p = p := by
  obtain ⟨hc, hs⟩ := h
  apply Prod.ext
  · simp [rotateInv, unitDirInv, rotateBy, hc, hs]
  · simp [rotateInv, unitDirInv, rotateBy, hc, hs]

theorem axisAligned_toBody (g : RotatedSquare) (h : isAxisAligned g) (p : ℚ × ℚ) :
    g.toBody p = (p.1 - g.shift.1, p.2 - g.shift.2) := by
  simp only [RotatedSquare.toBody]
  simpa using axisAligned_rotateInv_id g h (p.1 - g.shift.1, p.2 - g.shift.2)

theorem axisAligned_contains_iff (g : RotatedSquare) (h : isAxisAligned g) (p : ℚ × ℚ) :
    RotatedSquare.contains g p ↔ (toAxisSquare g).contains p := by
  constructor
  · intro hcon
    have hb : g.toBody p = (p.1 - g.shift.1, p.2 - g.shift.2) :=
      axisAligned_toBody g h p
    have hin : inAxisSquare (g.toBody p) := hcon
    rw [hb] at hin
    simp only [inAxisSquare] at hin
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hin
    simp only [AxisSquare.contains, toAxisSquare]
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩
  · intro hcon
    simp only [AxisSquare.contains, toAxisSquare] at hcon
    obtain ⟨⟨⟨hx0, hx1⟩, hy0⟩, hy1⟩ := hcon
    have hb : g.toBody p = (p.1 - g.shift.1, p.2 - g.shift.2) :=
      axisAligned_toBody g h p
    simp only [RotatedSquare.contains, hb, inAxisSquare]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

def axisSquaresOf {T : Target} (cov : PointwiseCover T) : Fin 6 → AxisSquare :=
  fun i => toAxisSquare (cov.squares i)

/-! ## Centre containment ⇒ strict interior -/

theorem axis_contains_centre_strict_interior (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : s.contains (μ, μ)) :
    (0 : ℚ) < s.x ∧ s.x + 1 < 2 * μ ∧ (0 : ℚ) < s.y ∧ s.y + 1 < 2 * μ := by
  simp only [AxisSquare.contains] at h
  obtain ⟨⟨⟨hx0, hx1⟩, hy0⟩, hy1⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hμ, hx1]
  · nlinarith [hμ, hx0]
  · nlinarith [hμ, hy1]
  · nlinarith [hμ, hy0]

theorem axis_contains_centre_outer_zero (s : AxisSquare) (μ : ℚ) (hμ : 1 < μ)
    (h : s.contains (μ, μ)) : outerContrib s μ = 0 := by
  have hi := axis_contains_centre_strict_interior s μ hμ h
  exact interior_outerContrib_eq_zero s μ hμ hi.1 hi.2.1 hi.2.2.1 hi.2.2.2

/-! ## Axis pointwise cover ⇒ AxisGridRatCover -/

theorem grid_point_in_target_bottom (T : Target) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 2 * T.μ) : inTarget T (q, 0) :=
  ⟨hq0, hq1, by norm_num, by nlinarith [T.hμ]⟩

theorem grid_point_in_target_top (T : Target) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 2 * T.μ) : inTarget T (q, 2 * T.μ) :=
  ⟨hq0, hq1, by nlinarith [T.hμ], by nlinarith⟩

theorem grid_point_in_target_left (T : Target) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 2 * T.μ) : inTarget T (0, q) :=
  ⟨by norm_num, by nlinarith [T.hμ], hq0, hq1⟩

theorem grid_point_in_target_right (T : Target) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 2 * T.μ) : inTarget T (2 * T.μ, q) :=
  ⟨by nlinarith [T.hμ], by nlinarith, hq0, hq1⟩

theorem grid_point_in_target_hMid (T : Target) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 2 * T.μ) : inTarget T (q, T.μ) :=
  ⟨hq0, hq1, by nlinarith [T.hμ], by nlinarith [T.hμ]⟩

theorem grid_point_in_target_vMid (T : Target) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 2 * T.μ) : inTarget T (T.μ, q) :=
  ⟨by nlinarith [T.hμ], by nlinarith [T.hμ], hq0, hq1⟩

theorem AxisGridRatCover_of_axis_pointwise (T : Target) (cov : PointwiseCover T)
    (halign : ∀ i : Fin 6, isAxisAligned (cov.squares i)) :
    AxisGridRatCover T.μ (axisSquaresOf cov) where
  bottom := by
    intro q hq0 hq1
    rcases cov.covers (q, 0) (grid_point_in_target_bottom T q hq0 hq1) with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (cov.squares i) (halign i) (q, 0)).mp hi⟩
  top := by
    intro q hq0 hq1
    rcases cov.covers (q, 2 * T.μ) (grid_point_in_target_top T q hq0 hq1) with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (cov.squares i) (halign i) (q, 2 * T.μ)).mp hi⟩
  left := by
    intro q hq0 hq1
    rcases cov.covers (0, q) (grid_point_in_target_left T q hq0 hq1) with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (cov.squares i) (halign i) (0, q)).mp hi⟩
  right := by
    intro q hq0 hq1
    rcases cov.covers (2 * T.μ, q) (grid_point_in_target_right T q hq0 hq1) with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (cov.squares i) (halign i) (2 * T.μ, q)).mp hi⟩
  hMid := by
    intro q hq0 hq1
    rcases cov.covers (q, T.μ) (grid_point_in_target_hMid T q hq0 hq1) with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (cov.squares i) (halign i) (q, T.μ)).mp hi⟩
  vMid := by
    intro q hq0 hq1
    rcases cov.covers (T.μ, q) (grid_point_in_target_vMid T q hq0 hq1) with ⟨i, hi⟩
    exact ⟨i, (axisAligned_contains_iff (cov.squares i) (halign i) (T.μ, q)).mp hi⟩

/-! ## Fin 6 partition from six pairwise-distinct indices -/

theorem fin6_partition_of_six_distinct
    (a b c d e f : Fin 6)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    ∀ k : Fin 6, k = a ∨ k = b ∨ k = c ∨ k = d ∨ k = e ∨ k = f := by
  intro k
  let s : Finset (Fin 6) := {a, b, c, d, e, f}
  have hs : s.card = 6 := by
    change ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6
    have h1 : a ∉ ({b, c, d, e, f} : Finset (Fin 6)) := by
      simp [hab, hac, had, hae, haf]
    have h2 : b ∉ ({c, d, e, f} : Finset (Fin 6)) := by
      simp [hbc, hbd, hbe, hbf]
    have h3 : c ∉ ({d, e, f} : Finset (Fin 6)) := by
      simp [hcd, hce, hcf]
    have h4 : d ∉ ({e, f} : Finset (Fin 6)) := by
      simp [hde, hdf]
    have h5 : e ∉ ({f} : Finset (Fin 6)) := by
      simp [hef]
    simp [Finset.card_insert_of_notMem, h1, h2, h3, h4, h5, Finset.card_singleton]
  have hEq : s = (Finset.univ : Finset (Fin 6)) := by
    apply Finset.eq_of_subset_of_card_le (fun _ _ => Finset.mem_univ _)
    simp [hs, Finset.card_univ, Fintype.card_fin]
  have : k ∈ s := by simpa [hEq] using Finset.mem_univ k
  simpa [s, Finset.mem_insert, Finset.mem_singleton] using this

/-! ## AxisG5k0Roles from corners + two centre fillers -/

noncomputable def AxisG5k0Roles_of_corners_and_centre_fillers
    (μ : ℚ) (hμ : 1 < μ) (squares : Fin 6 → AxisSquare)
    (iSW iSE iNE iNW j1 j2 : Fin 6)
    (hSW : (squares iSW).contains (0, 0))
    (hSE : (squares iSE).contains (2 * μ, 0))
    (hNE : (squares iNE).contains (2 * μ, 2 * μ))
    (hNW : (squares iNW).contains (0, 2 * μ))
    (hj1c : (squares j1).contains (μ, μ))
    (hj2c : (squares j2).contains (μ, μ))
    (hdSW : iSW ≠ iSE) (hdSW3 : iSW ≠ iNE) (hdSW4 : iSW ≠ iNW)
    (hdSE3 : iSE ≠ iNE) (hdSE4 : iSE ≠ iNW) (hdNE4 : iNE ≠ iNW)
    (hj : j1 ≠ j2)
    (hj1SW : j1 ≠ iSW) (hj1SE : j1 ≠ iSE) (hj1NE : j1 ≠ iNE) (hj1NW : j1 ≠ iNW)
    (hj2SW : j2 ≠ iSW) (hj2SE : j2 ≠ iSE) (hj2NE : j2 ≠ iNE) (hj2NW : j2 ≠ iNW) :
    AxisG5k0Roles μ squares := by
  have hpart := fin6_partition_of_six_distinct
    iSW iSE iNE iNW j1 j2
    hdSW hdSW3 hdSW4 (Ne.symm hj1SW) (Ne.symm hj2SW)
    hdSE3 hdSE4 (Ne.symm hj1SE) (Ne.symm hj2SE)
    hdNE4 (Ne.symm hj1NE) (Ne.symm hj2NE)
    (Ne.symm hj1NW) (Ne.symm hj2NW) hj
  have hi1 := axis_contains_centre_strict_interior (squares j1) μ hμ hj1c
  have hi2 := axis_contains_centre_strict_interior (squares j2) μ hμ hj2c
  exact
    { iSW := iSW, iSE := iSE, iNE := iNE, iNW := iNW, j1 := j1, j2 := j2
      hμ := hμ, hSW := hSW, hSE := hSE, hNE := hNE, hNW := hNW
      hdSW := hdSW, hdSW3 := hdSW3, hdSW4 := hdSW4
      hdSE3 := hdSE3, hdSE4 := hdSE4, hdNE4 := hdNE4, hj := hj
      hj1SW := hj1SW, hj1SE := hj1SE, hj1NE := hj1NE, hj1NW := hj1NW
      hj2SW := hj2SW, hj2SE := hj2SE, hj2NE := hj2NE, hj2NW := hj2NW
      hpart := hpart
      hj1x0 := hi1.1, hj1x1 := hi1.2.1, hj1y0 := hi1.2.2.1, hj1y1 := hi1.2.2.2
      hj2x0 := hi2.1, hj2x1 := hi2.2.1, hj2y0 := hi2.2.2.1, hj2y1 := hi2.2.2.2 }

/-! ## From axis-aligned PointwiseCover + F∋O world → roles -/

/-- Axis-aligned cover whose sixth tile `iF` also contains the target centre
(world-coordinate G5 reading). -/
structure AxisAlignedCentreFCover (T : Target) where
  cov : PointwiseCover T
  halign : ∀ i : Fin 6, isAxisAligned (cov.squares i)
  hFcen : RotatedSquare.contains
    (cov.squares (RoleSelection.ofCover cov).iF) (Target.centre T)

theorem roles_of_axis_centreF (T : Target) (H : AxisAlignedCentreFCover T) :
    Nonempty (AxisG5k0Roles T.μ (axisSquaresOf H.cov)) := by
  let R := RoleSelection.ofCover H.cov
  let squares := axisSquaresOf H.cov
  have hCaxis := axisAligned_contains_iff (H.cov.squares R.iC) (H.halign R.iC)
  have hFaxis := axisAligned_contains_iff (H.cov.squares R.iF) (H.halign R.iF)
  have h1 := axisAligned_contains_iff (H.cov.squares R.owners.i1) (H.halign R.owners.i1)
  have h2 := axisAligned_contains_iff (H.cov.squares R.owners.i2) (H.halign R.owners.i2)
  have h3 := axisAligned_contains_iff (H.cov.squares R.owners.i3) (H.halign R.owners.i3)
  have h4 := axisAligned_contains_iff (H.cov.squares R.owners.i4) (H.halign R.owners.i4)
  have hSW : (squares R.owners.i1).contains (0, 0) := by
    simpa [squares, axisSquaresOf, Target.v1] using (h1 _).mp R.owners.h1
  have hSE : (squares R.owners.i2).contains (2 * T.μ, 0) := by
    simpa [squares, axisSquaresOf, Target.v2] using (h2 _).mp R.owners.h2
  have hNE : (squares R.owners.i3).contains (2 * T.μ, 2 * T.μ) := by
    simpa [squares, axisSquaresOf, Target.v3] using (h3 _).mp R.owners.h3
  have hNW : (squares R.owners.i4).contains (0, 2 * T.μ) := by
    simpa [squares, axisSquaresOf, Target.v4] using (h4 _).mp R.owners.h4
  have hj1c : (squares R.iC).contains (T.μ, T.μ) := by
    simpa [squares, axisSquaresOf, Target.centre] using (hCaxis _).mp R.hCentre
  have hj2c : (squares R.iF).contains (T.μ, T.μ) := by
    simpa [squares, axisSquaresOf, Target.centre] using (hFaxis _).mp H.hFcen
  have hpd := owners_pairwise_distinct T R.owners
  have hCne := R.hC_ne_corners
  have hFne := R.hF_ne_corners
  refine ⟨AxisG5k0Roles_of_corners_and_centre_fillers T.μ T.hμ squares
    R.owners.i1 R.owners.i2 R.owners.i3 R.owners.i4 R.iC R.iF
    hSW hSE hNE hNW hj1c hj2c
    hpd.1 hpd.2.1 hpd.2.2.1 hpd.2.2.2.1 hpd.2.2.2.2.1 hpd.2.2.2.2.2
    R.hCF
    hCne.1 hCne.2.1 hCne.2.2.1 hCne.2.2.2
    hFne.1 hFne.2.1 hFne.2.2.1 hFne.2.2.2⟩

theorem ratCover_of_axis_centreF (T : Target) (H : AxisAlignedCentreFCover T) :
    AxisGridRatCover T.μ (axisSquaresOf H.cov) :=
  AxisGridRatCover_of_axis_pointwise T H.cov H.halign

theorem axis_G5k0_impossible_of_centreF (T : Target) (H : AxisAlignedCentreFCover T) :
    False := by
  rcases roles_of_axis_centreF T H with ⟨R⟩
  exact axis_G5k0_impossible_of_roles T.μ (axisSquaresOf H.cov)
    (ratCover_of_axis_centreF T H) R

/-! ## Bridge packaging: every G5 k=0 cover realises AxisAlignedCentreFCover -/

/-- Open: every G5 k=0 PointwiseCover is axis-aligned with world-coord `F∋O`. -/
def AxisAlignedG5k0Realisation : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        (∀ i : Fin 6, isAxisAligned (cov.squares i)) ∧
          RotatedSquare.contains (cov.squares (RoleSelection.ofCover cov).iF)
            (Target.centre T)

theorem AxisG5k0CoverBridge_of_axisRealisation (h : AxisAlignedG5k0Realisation) :
    AxisG5k0CoverBridge := by
  intro T cov hcls hk
  have ⟨halign, hFcen⟩ := h T cov hcls hk
  refine ⟨axisSquaresOf cov, AxisGridRatCover_of_axis_pointwise T cov halign, ?_⟩
  exact roles_of_axis_centreF T ⟨cov, halign, hFcen⟩

theorem G5k0Bridge_of_axisRealisation (h : AxisAlignedG5k0Realisation) : G5k0Bridge :=
  G5k0Bridge_of_axisCoverBridge (AxisG5k0CoverBridge_of_axisRealisation h)

theorem G5k0GeomExport_of_axisRealisation (h : AxisAlignedG5k0Realisation) :
    G5k0GeomExport :=
  G5k0GeomExport_of_axisCoverBridge (AxisG5k0CoverBridge_of_axisRealisation h)

def axisAlignedConversionClosed : Bool := true
theorem axisAlignedConversionClosed_true : axisAlignedConversionClosed = true := rfl

def axisCentreInteriorClosed : Bool := true
theorem axisCentreInteriorClosed_true : axisCentreInteriorClosed = true := rfl

def axisPointwiseToRatCoverClosed : Bool := true
theorem axisPointwiseToRatCoverClosed_true : axisPointwiseToRatCoverClosed = true := rfl

def axisRolesFromCentreFillersClosed : Bool := true
theorem axisRolesFromCentreFillersClosed_true :
    axisRolesFromCentreFillersClosed = true := rfl

/-! ## G5 ⇒ fHasO; identity-C ⇒ world F∋O (general PointwiseCover) -/

theorem unitDir_eq (u v : UnitDir) (hc : u.c = v.c) (hs : u.s = v.s) : u = v := by
  match u, v with
  | ⟨uc, us, uh⟩, ⟨vc, vs, vh⟩ =>
    cases hc; cases hs; rfl

theorem rigidMotion_eq (g₁ g₂ : RigidMotion)
    (hd : g₁.dir = g₂.dir) (hs : g₁.shift = g₂.shift) : g₁ = g₂ := by
  match g₁, g₂ with
  | ⟨d1, s1⟩, ⟨d2, s2⟩ =>
    cases hd; cases hs; rfl

theorem identityPose_inverse :
    RigidMotion.inverse identityPose = identityPose := by
  apply rigidMotion_eq
  · apply unitDir_eq <;>
      simp [RigidMotion.inverse, identityPose, rotateInv, unitDirInv, rotateBy]
  · simp [RigidMotion.inverse, identityPose, rotateInv, unitDirInv, rotateBy]

theorem pullback_identity (f : RotatedSquare) :
    RotatedSquare.pullback identityPose f = f := by
  simp only [RotatedSquare.pullback, identityPose_inverse]
  apply rigidMotion_eq
  · apply unitDir_eq <;>
      simp [RigidMotion.comp, identityPose, UnitDir.comp, rotateBy]
  · simp [RigidMotion.comp, identityPose, rotateBy]

theorem classify_eq_G5_iff_fHasO (o : Ownership) :
    classify o = TopClass.G5 ↔ o.fHasO = true := by
  constructor
  · intro h
    cases hf : o.fHasO
    · simp [classify, hf] at h
      match o.k, h with
      | ⟨0, _⟩, h => cases h
      | ⟨1, _⟩, h => revert h; cases o.midInC <;> intro h <;> cases h
      | ⟨2, _⟩, h => revert h; cases o.midsAdjacent <;> intro h <;> cases h
    · rfl
  · intro h; exact classify_G5_of_fHasO o h

theorem isG5Class_fHasO {T : Target} (cov : PointwiseCover T) (h : isG5Class cov) :
    (RoleSelection.ofCover cov).toManuscript.flags.fHasO = true :=
  (classify_eq_G5_iff_fHasO _).1 h

theorem toManuscript_F_of_identityC {T : Target} (R : RoleSelection T)
    (hC : R.cov.squares R.iC = identityPose) :
    R.toManuscript.F = R.cov.squares R.iF := by
  simp only [RoleSelection.toManuscript, hC, pullback_identity]

theorem worldF_contains_O_of_identityC_G5 {T : Target} (cov : PointwiseCover T)
    (hC : (RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC = identityPose)
    (hG5 : isG5Class cov) :
    RotatedSquare.contains
      ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iF)
      (T.μ, T.μ) := by
  set R := RoleSelection.ofCover cov
  have hf := isG5Class_fHasO cov hG5
  have hFeq := toManuscript_F_of_identityC R hC
  simp only [ManuscriptNormalisedCovering.flags, flagsOfTargetRotated, fContainsO_rot,
    ManuscriptNormalisedCovering.toRotated] at hf
  rw [hFeq] at hf
  have hO : R.toManuscript.target.O = (T.μ, T.μ) := by
    simp [ManuscriptNormalisedCovering.target, TargetMids.O, RoleSelection.toManuscript]
  rw [hO] at hf
  exact (RotatedSquare.containsB_iff _ _).1 hf


/-- Axis-aligned + identity centre tile + G5 ⇒ `AxisAlignedCentreFCover`. -/
theorem axisCentreF_of_identityC_axis {T : Target} (cov : PointwiseCover T)
    (halign : ∀ i : Fin 6, isAxisAligned (cov.squares i))
    (hC : (RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC = identityPose)
    (hG5 : isG5Class cov) :
    Nonempty (AxisAlignedCentreFCover T) := by
  have hF := worldF_contains_O_of_identityC_G5 cov hC hG5
  -- RoleSelection.ofCover cov .cov = cov definitionally enough for squares
  refine ⟨⟨cov, halign, ?_⟩⟩
  -- hF is on R.cov.squares; need cov.squares
  have hcov : (RoleSelection.ofCover cov).cov = cov := rfl
  simpa [hcov, Target.centre] using hF

/-- Full axis G5k0 discharge when cover is axis-aligned with C = identityPose. -/
theorem axis_G5k0_impossible_of_identityC_axis {T : Target} (cov : PointwiseCover T)
    (halign : ∀ i : Fin 6, isAxisAligned (cov.squares i))
    (hC : (RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC = identityPose)
    (hG5 : isG5Class cov)
    (_hk : (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩) :
    False := by
  rcases axisCentreF_of_identityC_axis cov halign hC hG5 with ⟨H⟩
  exact axis_G5k0_impossible_of_centreF T H

/-- Open hyp reduced: only need axis-align + identity-C for every G5 k=0 cover
(world F∋O is then proved). -/
def AxisAlignedIdentityCRealisation : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        (∀ i : Fin 6, isAxisAligned (cov.squares i)) ∧
          (RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC = identityPose

theorem AxisAlignedG5k0Realisation_of_identityCRealisation
    (h : AxisAlignedIdentityCRealisation) : AxisAlignedG5k0Realisation := by
  intro T cov hcls hk
  have ⟨halign, hC⟩ := h T cov hcls hk
  refine ⟨halign, ?_⟩
  have hF := worldF_contains_O_of_identityC_G5 cov hC hcls
  have hcov : (RoleSelection.ofCover cov).cov = cov := rfl
  simpa [hcov, Target.centre] using hF

theorem G5k0Bridge_of_identityCRealisation (h : AxisAlignedIdentityCRealisation) :
    G5k0Bridge :=
  G5k0Bridge_of_axisRealisation (AxisAlignedG5k0Realisation_of_identityCRealisation h)

theorem G5k0GeomExport_of_identityCRealisation (h : AxisAlignedIdentityCRealisation) :
    G5k0GeomExport :=
  G5k0GeomExport_of_axisRealisation (AxisAlignedG5k0Realisation_of_identityCRealisation h)

def axisIdentityCPathClosed : Bool := true
theorem axisIdentityCPathClosed_true : axisIdentityCPathClosed = true := rfl

def axisAlignedG5k0RealisationProved : Bool := false
theorem axisAlignedG5k0RealisationProved_false :
    axisAlignedG5k0RealisationProved = false := rfl

def axisAlignedIdentityCRealisationProved : Bool := false
theorem axisAlignedIdentityCRealisationProved_false :
    axisAlignedIdentityCRealisationProved = false := rfl

/-! ## Manuscript body-chart faithfulness (C → identityPose) -/

/-- Pulling a square into its own body chart yields `identityPose`. -/
theorem pullback_self (g : RotatedSquare) :
    RotatedSquare.pullback g g = identityPose := by
  simp only [RotatedSquare.pullback]
  apply rigidMotion_eq
  · apply unitDir_eq
    · simp only [RigidMotion.comp, RigidMotion.inverse, UnitDir.comp, unitDirInv,
        rotateInv, rotateBy, identityPose]
      have hu := g.dir.hc
      nlinarith
    · simp only [RigidMotion.comp, RigidMotion.inverse, UnitDir.comp, unitDirInv,
        rotateInv, rotateBy, identityPose]
      ring
  · simp only [RigidMotion.comp, RigidMotion.inverse, rotateInv, rotateBy, identityPose]
    apply Prod.ext <;> ring

/-! ## SE(2) laws + containment transport -/

theorem rotateBy_comp (u v : UnitDir) (p : ℚ × ℚ) :
    rotateBy (UnitDir.comp u v) p = rotateBy u (rotateBy v p) := by
  simp only [rotateBy, UnitDir.comp]
  apply Prod.ext <;> ring

theorem rotateBy_add (u : UnitDir) (p q : ℚ × ℚ) :
    rotateBy u (p.1 + q.1, p.2 + q.2) =
      ((rotateBy u p).1 + (rotateBy u q).1,
        (rotateBy u p).2 + (rotateBy u q).2) := by
  simp only [rotateBy]; apply Prod.ext <;> ring

theorem rigid_comp_apply (g h : RigidMotion) (p : ℚ × ℚ) :
    (RigidMotion.comp g h).apply p = g.apply (h.apply p) := by
  simp only [RigidMotion.comp, RigidMotion.apply, translate]
  have hr := rotateBy_comp g.dir h.dir p
  have hlin := rotateBy_add g.dir (rotateBy h.dir p) h.shift
  apply Prod.ext
  · calc
      (rotateBy (UnitDir.comp g.dir h.dir) p).1 +
          ((rotateBy g.dir h.shift).1 + g.shift.1)
          = (rotateBy g.dir (rotateBy h.dir p)).1 +
              ((rotateBy g.dir h.shift).1 + g.shift.1) := by rw [hr]
      _ = (rotateBy g.dir
              ((rotateBy h.dir p).1 + h.shift.1,
               (rotateBy h.dir p).2 + h.shift.2)).1 + g.shift.1 := by
            have := congrArg Prod.fst hlin; linarith
  · calc
      (rotateBy (UnitDir.comp g.dir h.dir) p).2 +
          ((rotateBy g.dir h.shift).2 + g.shift.2)
          = (rotateBy g.dir (rotateBy h.dir p)).2 +
              ((rotateBy g.dir h.shift).2 + g.shift.2) := by rw [hr]
      _ = (rotateBy g.dir
              ((rotateBy h.dir p).1 + h.shift.1,
               (rotateBy h.dir p).2 + h.shift.2)).2 + g.shift.2 := by
            have := congrArg Prod.snd hlin; linarith

theorem toBody_eq_inverse_apply (g : RigidMotion) (p : ℚ × ℚ) :
    RotatedSquare.toBody g p = (RigidMotion.inverse g).apply p := by
  simp only [RotatedSquare.toBody, RigidMotion.inverse, RigidMotion.apply,
    translate, rotateInv, unitDirInv, rotateBy]
  apply Prod.ext <;> ring

theorem rigid_inverse_apply_apply (g : RigidMotion) (p : ℚ × ℚ) :
    (RigidMotion.inverse g).apply (g.apply p) = p := by
  have h := toBody_apply g p
  rwa [toBody_eq_inverse_apply] at h

theorem rigid_apply_inverse_apply (g : RigidMotion) (p : ℚ × ℚ) :
    g.apply ((RigidMotion.inverse g).apply p) = p := by
  have h := apply_toBody g p
  rwa [toBody_eq_inverse_apply] at h

/-- Body coord of `pullback g f` at `g.toBody p` equals body coord of `f` at `p`. -/
theorem pullback_toBody (g f : RotatedSquare) (p : ℚ × ℚ) :
    RotatedSquare.toBody (RotatedSquare.pullback g f) (RotatedSquare.toBody g p) =
      RotatedSquare.toBody f p := by
  have hgoal :
      (RotatedSquare.pullback g f).apply (RotatedSquare.toBody f p) =
        RotatedSquare.toBody g p := by
    simp only [RotatedSquare.pullback]
    rw [rigid_comp_apply, apply_toBody, ← toBody_eq_inverse_apply]
  have h := congrArg (RotatedSquare.toBody (RotatedSquare.pullback g f)) hgoal
  rw [toBody_apply] at h
  exact h.symm

theorem pullback_contains_iff (g f : RotatedSquare) (p : ℚ × ℚ) :
    RotatedSquare.contains (RotatedSquare.pullback g f) (RotatedSquare.toBody g p) ↔
      RotatedSquare.contains f p := by
  simp only [RotatedSquare.contains, pullback_toBody]

/-- Body-chart F∋(C.toBody O) ↔ world F∋O. -/
theorem bodyF_contains_bodyO_iff_worldF {T : Target} (cov : PointwiseCover T) :
    let R := RoleSelection.ofCover cov
    let C := R.cov.squares R.iC
    let F := R.cov.squares R.iF
    RotatedSquare.contains (RotatedSquare.pullback C F) (RotatedSquare.toBody C (T.μ, T.μ)) ↔
      RotatedSquare.contains F (T.μ, T.μ) :=
  pullback_contains_iff _ _ _

/-- Manuscript `fHasO` ↔ world F∋O when C = `identityPose`. -/
theorem manuscript_fHasO_eq_world_of_identityC {T : Target} (cov : PointwiseCover T)
    (hC : (RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC =
      identityPose) :
    ((RoleSelection.ofCover cov).toManuscript.flags.fHasO = true) ↔
      RotatedSquare.contains
        ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iF)
        (T.μ, T.μ) := by
  set R := RoleSelection.ofCover cov
  have hFeq := toManuscript_F_of_identityC R hC
  constructor
  · intro hf
    simp only [ManuscriptNormalisedCovering.flags, flagsOfTargetRotated, fContainsO_rot,
      ManuscriptNormalisedCovering.toRotated] at hf
    rw [hFeq] at hf
    have hO : R.toManuscript.target.O = (T.μ, T.μ) := by
      simp [ManuscriptNormalisedCovering.target, TargetMids.O, RoleSelection.toManuscript]
    rw [hO] at hf
    exact (RotatedSquare.containsB_iff _ _).1 hf
  · intro hw
    have hO : R.toManuscript.target.O = (T.μ, T.μ) := by
      simp [ManuscriptNormalisedCovering.target, TargetMids.O, RoleSelection.toManuscript]
    simp only [ManuscriptNormalisedCovering.flags, flagsOfTargetRotated, fContainsO_rot,
      ManuscriptNormalisedCovering.toRotated, hFeq, hO]
    exact (RotatedSquare.containsB_iff _ _).2 hw

def pullbackContainsTransportClosed : Bool := true
theorem pullbackContainsTransportClosed_true :
    pullbackContainsTransportClosed = true := rfl

theorem isAxisAligned_identity : isAxisAligned identityPose := by
  simp [isAxisAligned, identityPose]

/-- Body-chart pullback of two axis-aligned squares stays axis-aligned. -/
theorem isAxisAligned_pullback_of_axis (g f : RotatedSquare)
    (hg : isAxisAligned g) (hf : isAxisAligned f) :
    isAxisAligned (RotatedSquare.pullback g f) := by
  obtain ⟨hc_g, hs_g⟩ := hg
  obtain ⟨hc_f, hs_f⟩ := hf
  simp only [isAxisAligned, RotatedSquare.pullback, RigidMotion.comp, RigidMotion.inverse,
    UnitDir.comp, unitDirInv, rotateInv, rotateBy, hc_g, hs_g, hc_f, hs_f]
  constructor <;> ring

theorem isAxisAligned_translate (t : ℚ × ℚ) (g : RotatedSquare)
    (h : isAxisAligned g) : isAxisAligned (translateSquare t g) := by
  simpa [isAxisAligned, translateSquare] using h

theorem axisAligned_zero_shift_eq_identity (g : RotatedSquare)
    (h : isAxisAligned g) (hs : g.shift = (0, 0)) : g = identityPose := by
  obtain ⟨hc, hs0⟩ := h
  apply rigidMotion_eq
  · apply unitDir_eq <;> simp [identityPose, hc, hs0]
  · simpa [identityPose] using hs

theorem translate_neg_shift (g : RotatedSquare) :
    (translateSquare (-g.shift.1, -g.shift.2) g).shift = (0, 0) := by
  simp only [translateSquare, translate]
  apply Prod.ext <;> ring

/-- Pure translation sends any axis-aligned tile to `identityPose`. -/
theorem translate_axis_to_identity (g : RotatedSquare) (h : isAxisAligned g) :
    translateSquare (-g.shift.1, -g.shift.2) g = identityPose := by
  have htr : isAxisAligned (translateSquare (-g.shift.1, -g.shift.2) g) :=
    isAxisAligned_translate _ g h
  exact axisAligned_zero_shift_eq_identity _ htr (translate_neg_shift g)

theorem axis_tile_normalisable_to_identity (g : RotatedSquare) (h : isAxisAligned g) :
    ∃ t : ℚ × ℚ, translateSquare t g = identityPose :=
  ⟨(-g.shift.1, -g.shift.2), translate_axis_to_identity g h⟩

/-- Six squares pulled into the centre tile's body chart. -/
noncomputable def bodyChartSquares {T : Target} (cov : PointwiseCover T) :
    Fin 6 → RotatedSquare :=
  let R := RoleSelection.ofCover cov
  fun i => RotatedSquare.pullback (R.cov.squares R.iC) (R.cov.squares i)

theorem bodyChartSquares_iC {T : Target} (cov : PointwiseCover T) :
    bodyChartSquares cov (RoleSelection.ofCover cov).iC = identityPose := by
  dsimp only [bodyChartSquares]
  exact pullback_self _

/-- Body-chart C is always `identityPose` (chart-placement faithfulness). -/
theorem bodyChart_C_is_identity {T : Target} (cov : PointwiseCover T) :
    bodyChartSquares cov (RoleSelection.ofCover cov).iC = identityPose :=
  bodyChartSquares_iC cov

def BodyChartAxisAligned {T : Target} (cov : PointwiseCover T) : Prop :=
  ∀ i : Fin 6, isAxisAligned (bodyChartSquares cov i)

theorem bodyChartAxisAligned_of_world_axis {T : Target} (cov : PointwiseCover T)
    (halign : ∀ i, isAxisAligned (cov.squares i)) :
    BodyChartAxisAligned cov := by
  intro i
  dsimp only [bodyChartSquares]
  have hcov : (RoleSelection.ofCover cov).cov = cov := rfl
  have hiC := halign (RoleSelection.ofCover cov).iC
  have hi := halign i
  simpa [hcov] using isAxisAligned_pullback_of_axis _ _ hiC hi

/-- World axis-aligned cover ⇒ body chart is axis-aligned with C = identity. -/
theorem axis_world_realises_body_identityC {T : Target} (cov : PointwiseCover T)
    (halign : ∀ i, isAxisAligned (cov.squares i)) :
    BodyChartAxisAligned cov ∧
      bodyChartSquares cov (RoleSelection.ofCover cov).iC = identityPose :=
  ⟨bodyChartAxisAligned_of_world_axis cov halign, bodyChartSquares_iC cov⟩

/-- Manuscript `F` is the body-chart image of world `iF`. -/
theorem toManuscript_F_eq_bodyChartF {T : Target} (cov : PointwiseCover T) :
    (RoleSelection.ofCover cov).toManuscript.F =
      bodyChartSquares cov (RoleSelection.ofCover cov).iF :=
  rfl

/-- Open: every G5 k=0 cover is axis-aligned in the centre body chart. -/
def BodyChartAxisG5k0Realisation : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        BodyChartAxisAligned cov

theorem BodyChartAxisG5k0Realisation_of_axisRealisation
    (h : AxisAlignedG5k0Realisation) : BodyChartAxisG5k0Realisation := by
  intro T cov hcls hk
  have ⟨halign, _⟩ := h T cov hcls hk
  exact bodyChartAxisAligned_of_world_axis cov halign

theorem BodyChartAxisG5k0Realisation_of_identityC
    (h : AxisAlignedIdentityCRealisation) : BodyChartAxisG5k0Realisation :=
  BodyChartAxisG5k0Realisation_of_axisRealisation
    (AxisAlignedG5k0Realisation_of_identityCRealisation h)

def bodyChartFaithfulnessClosed : Bool := true
theorem bodyChartFaithfulnessClosed_true : bodyChartFaithfulnessClosed = true := rfl

def axisTileTranslateToIdentityClosed : Bool := true
theorem axisTileTranslateToIdentityClosed_true :
    axisTileTranslateToIdentityClosed = true := rfl

def bodyChartAxisG5k0RealisationProved : Bool := false
theorem bodyChartAxisG5k0RealisationProved_false :
    bodyChartAxisG5k0RealisationProved = false := rfl

/-! ## Same-dir ⇒ body-chart axis-aligned (IdentityC packaging) -/

/-- Shared world direction with chart tile ⇒ pullback is axis-aligned
(`C⁻¹ ∘ F` has direction `identity`). -/
theorem isAxisAligned_pullback_of_same_dir (g f : RotatedSquare)
    (h : f.dir = g.dir) :
    isAxisAligned (RotatedSquare.pullback g f) := by
  have hc : g.dir.c * g.dir.c + g.dir.s * g.dir.s = 1 := g.dir.hc
  simp only [isAxisAligned, RotatedSquare.pullback, RigidMotion.comp, RigidMotion.inverse,
    UnitDir.comp, unitDirInv, h]
  constructor
  · -- c-comp: g.c*g.c - (-g.s)*g.s = g.c² + g.s² = 1
    calc
      g.dir.c * g.dir.c - (-g.dir.s) * g.dir.s
          = g.dir.c * g.dir.c + g.dir.s * g.dir.s := by ring
      _ = 1 := hc
  · -- s-comp: (-g.s)*g.c + g.c*g.s = 0
    ring

/-- Every tile shares C's world direction ⇒ body chart is axis-aligned. -/
theorem bodyChartAxisAligned_of_same_dir_as_C {T : Target} (cov : PointwiseCover T)
    (hsame : ∀ i : Fin 6,
      (cov.squares i).dir =
        ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC).dir) :
    BodyChartAxisAligned cov := by
  intro i
  dsimp only [bodyChartSquares]
  have hcov : (RoleSelection.ofCover cov).cov = cov := rfl
  have hd : ((RoleSelection.ofCover cov).cov.squares i).dir =
      ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC).dir := by
    simpa [hcov] using hsame i
  exact isAxisAligned_pullback_of_same_dir
    ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC)
    ((RoleSelection.ofCover cov).cov.squares i) hd

/-- Same-dir cover realises body-chart axis-aligned with C = identityPose. -/
theorem same_dir_realises_body_identityC {T : Target} (cov : PointwiseCover T)
    (hsame : ∀ i : Fin 6,
      (cov.squares i).dir =
        ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC).dir) :
    BodyChartAxisAligned cov ∧
      bodyChartSquares cov (RoleSelection.ofCover cov).iC = identityPose :=
  ⟨bodyChartAxisAligned_of_same_dir_as_C cov hsame, bodyChartSquares_iC cov⟩

def sameDirBodyChartClosed : Bool := true
theorem sameDirBodyChartClosed_true : sameDirBodyChartClosed = true := rfl

/-! ## SameDir realisation ⇒ BodyChartAxisG5k0 (conditional inhabit) -/

/-- Every tile shares the centre tile's world direction. -/
def SameDirAsC {T : Target} (cov : PointwiseCover T) : Prop :=
  ∀ i : Fin 6,
    (cov.squares i).dir =
      ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC).dir

theorem BodyChartAxisAligned_of_SameDirAsC {T : Target} (cov : PointwiseCover T)
    (h : SameDirAsC cov) : BodyChartAxisAligned cov :=
  bodyChartAxisAligned_of_same_dir_as_C cov h

/-- Open hyp: every G5 k=0 cover is same-dir as its centre tile. -/
def SameDirG5k0Realisation : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        SameDirAsC cov

theorem BodyChartAxisG5k0Realisation_of_sameDir (h : SameDirG5k0Realisation) :
    BodyChartAxisG5k0Realisation := by
  intro T cov hcls hk
  exact BodyChartAxisAligned_of_SameDirAsC cov (h T cov hcls hk)

theorem same_dir_realises_body_identityC_of_SameDirAsC {T : Target}
    (cov : PointwiseCover T) (h : SameDirAsC cov) :
    BodyChartAxisAligned cov ∧
      bodyChartSquares cov (RoleSelection.ofCover cov).iC = identityPose :=
  same_dir_realises_body_identityC cov h

def sameDirG5k0RealisationProved : Bool := false
theorem sameDirG5k0RealisationProved_false : sameDirG5k0RealisationProved = false := rfl

def sameDirToBodyChartClosed : Bool := true
theorem sameDirToBodyChartClosed_true : sameDirToBodyChartClosed = true := rfl

/-! ## BodyChart ↔ SameDir (reverse) + BodyChart+IdentityC ⇒ world IdentityC -/

/-- Pullback axis-aligned ⇒ shared world direction. -/
theorem dir_eq_of_pullback_axis (g f : RotatedSquare)
    (h : isAxisAligned (RotatedSquare.pullback g f)) : f.dir = g.dir := by
  have hcomp_c : g.dir.c * f.dir.c + g.dir.s * f.dir.s = 1 := by
    simpa [isAxisAligned, RotatedSquare.pullback, RigidMotion.comp, RigidMotion.inverse,
      UnitDir.comp, unitDirInv] using h.1
  have hdiff :
      (f.dir.c - g.dir.c) ^ 2 + (f.dir.s - g.dir.s) ^ 2 = 0 := by
    nlinarith [g.dir.hc, f.dir.hc, hcomp_c]
  have hzc : f.dir.c = g.dir.c := by
    nlinarith [sq_nonneg (f.dir.c - g.dir.c), sq_nonneg (f.dir.s - g.dir.s), hdiff]
  have hzs : f.dir.s = g.dir.s := by
    nlinarith [sq_nonneg (f.dir.c - g.dir.c), sq_nonneg (f.dir.s - g.dir.s), hdiff]
  exact unitDir_eq _ _ hzc hzs

theorem SameDirAsC_of_BodyChartAxisAligned {T : Target} (cov : PointwiseCover T)
    (h : BodyChartAxisAligned cov) : SameDirAsC cov := by
  intro i
  have hcov : (RoleSelection.ofCover cov).cov = cov := rfl
  have hp : isAxisAligned (bodyChartSquares cov i) := h i
  simpa [SameDirAsC, bodyChartSquares, hcov] using
    dir_eq_of_pullback_axis
      ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC)
      ((RoleSelection.ofCover cov).cov.squares i)
      (by simpa [bodyChartSquares, hcov] using hp)

theorem BodyChartAxisAligned_iff_SameDirAsC {T : Target} (cov : PointwiseCover T) :
    BodyChartAxisAligned cov ↔ SameDirAsC cov :=
  ⟨SameDirAsC_of_BodyChartAxisAligned cov, BodyChartAxisAligned_of_SameDirAsC cov⟩

theorem BodyChartAxisG5k0Realisation_iff_SameDir :
    BodyChartAxisG5k0Realisation ↔ SameDirG5k0Realisation := by
  constructor
  · intro h T cov hcls hk
    exact SameDirAsC_of_BodyChartAxisAligned cov (h T cov hcls hk)
  · exact BodyChartAxisG5k0Realisation_of_sameDir

/-- Chart tile axis + body-chart axis ⇒ world tile axis. -/
theorem isAxisAligned_of_body_axis_of_chart_axis (g f : RotatedSquare)
    (hg : isAxisAligned g) (hp : isAxisAligned (RotatedSquare.pullback g f)) :
    isAxisAligned f := by
  have hdir := dir_eq_of_pullback_axis g f hp
  exact ⟨by simpa [hdir] using hg.1, by simpa [hdir] using hg.2⟩

theorem world_axis_of_BodyChartAxis_of_C_axis {T : Target} (cov : PointwiseCover T)
    (hbody : BodyChartAxisAligned cov)
    (hC : isAxisAligned
      ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC)) :
    ∀ i : Fin 6, isAxisAligned (cov.squares i) := by
  intro i
  have hcov : (RoleSelection.ofCover cov).cov = cov := rfl
  exact isAxisAligned_of_body_axis_of_chart_axis
    ((RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC)
    (cov.squares i) (by simpa [hcov] using hC)
    (by
      have hp : isAxisAligned (bodyChartSquares cov i) := hbody i
      simpa [bodyChartSquares, hcov] using hp)

/-- Open hyp: body-chart axis + world C = identityPose for every G5 k=0. -/
def BodyChartIdentityCG5k0Realisation : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        BodyChartAxisAligned cov ∧
          (RoleSelection.ofCover cov).cov.squares (RoleSelection.ofCover cov).iC =
            identityPose

theorem AxisAlignedIdentityCRealisation_of_bodyIdentityC
    (h : BodyChartIdentityCG5k0Realisation) : AxisAlignedIdentityCRealisation := by
  intro T cov hcls hk
  obtain ⟨hbody, hC⟩ := h T cov hcls hk
  refine ⟨?_, hC⟩
  exact world_axis_of_BodyChartAxis_of_C_axis cov hbody
    (by simpa [hC] using isAxisAligned_identity)

theorem G5k0Bridge_of_bodyIdentityC (h : BodyChartIdentityCG5k0Realisation) :
    G5k0Bridge :=
  G5k0Bridge_of_identityCRealisation
    (AxisAlignedIdentityCRealisation_of_bodyIdentityC h)

theorem G5k0GeomExport_of_bodyIdentityC (h : BodyChartIdentityCG5k0Realisation) :
    G5k0GeomExport :=
  G5k0GeomExport_of_identityCRealisation
    (AxisAlignedIdentityCRealisation_of_bodyIdentityC h)

def bodyChartIdentityCG5k0RealisationProved : Bool := false
theorem bodyChartIdentityCG5k0RealisationProved_false :
    bodyChartIdentityCG5k0RealisationProved = false := rfl

def bodyChartIffSameDirClosed : Bool := true
theorem bodyChartIffSameDirClosed_true : bodyChartIffSameDirClosed = true := rfl

def bodyIdentityCToAxisIdentityCClosed : Bool := true
theorem bodyIdentityCToAxisIdentityCClosed_true :
    bodyIdentityCToAxisIdentityCClosed = true := rfl

def openAxisG5k0FromCover : List String :=
  ["AxisAlignedIdentityCRealisation (world axis + C=identityPose for every G5 k=0)",
   "BodyChartAxisG5k0Realisation / SameDirG5k0Realisation inhabit (iff packaging closed)",
   "BodyChartIdentityCG5k0Realisation inhabit (body-axis + world C=identity)",
   "RotatedChordCoverIneq / BoundPackage from general PointwiseCover",
   "Manuscript fHasO uses O=(μ,μ) not C.toBody(world O) when C≠identity (model gap)"]

end S6.AxisG5k0FromCover
