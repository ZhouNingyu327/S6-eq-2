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

Open: discharge `AxisAlignedG5k0Realisation` for every G5 k=0 `PointwiseCover`
(axis alignment + world-coord `F∋O`), or inhabit `RotatedG5k0ChordExport`.
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

def openAxisG5k0FromCover : List String :=
  ["AxisAlignedIdentityCRealisation (axis-align + C=identityPose for every G5 k=0 cover)",
   "RotatedChordBoundPackage / grid cover ineq from general PointwiseCover"]

end S6.AxisG5k0FromCover
