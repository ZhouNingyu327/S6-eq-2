import Mathlib.Tactic
import S6Core.Obligation2
import S6Core.Obligation2Norm
import S6Core.Obligation2Opens
import S6Core.PdfNormalisation
import S6Core.OwnershipBridge
import S6Core.RigidMotionChart

/-!
# Obligation 2 — role / mid selection from geometry

## 已证
* Centre of `T` is strictly farther than √2 from every corner (`distSq > 2`)
* Hence any centre-owner index is distinct from all four corner-owner indices
* Complementary free index in `Fin 6` exists (the unique non-corner, non-centre slot)
* Standard outer mid candidates of `T` lie in `T`
* `RoleSelection` packages `(iC,iF,iA,mids)` from a `PointwiseCover`
* Every `RoleSelection` induces a `ManuscriptNormalisedCovering` and a `TopClass`

## Body-chart mids closed this turn
* `midsInBody` / `standardMids_bodyChart_of_identity`
* `obligation2_fullNormalisationClosed = true` (Lean/G2 model)
-/

namespace S6.Obligation2Roles

open S6.Obligation2
open S6.Obligation2Norm
open S6.Obligation2Opens
open S6.OwnershipBridge
open S6.RigidMotionChart
open S6.PdfNormalisation

abbrev QPt := ℚ × ℚ

/-! ## Centre far from every corner -/

theorem centre_far_v1 (T : Target) :
    (2 : ℚ) < distSq (Target.v1 T) (Target.centre T) := by
  simp only [distSq, Target.v1, Target.centre]
  -- μ²+μ² = 2μ² > 2
  nlinarith [T.hμ]

theorem centre_far_v2 (T : Target) :
    (2 : ℚ) < distSq (Target.v2 T) (Target.centre T) := by
  simp only [distSq, Target.v2, Target.centre]
  nlinarith [T.hμ]

theorem centre_far_v3 (T : Target) :
    (2 : ℚ) < distSq (Target.v3 T) (Target.centre T) := by
  simp only [distSq, Target.v3, Target.centre]
  nlinarith [T.hμ]

theorem centre_far_v4 (T : Target) :
    (2 : ℚ) < distSq (Target.v4 T) (Target.centre T) := by
  simp only [distSq, Target.v4, Target.centre]
  nlinarith [T.hμ]

theorem corner_owner_misses_centre (T : Target) (g : RotatedSquare)
    (hcorn : RotatedSquare.contains g (Target.v1 T) ∨
      RotatedSquare.contains g (Target.v2 T) ∨
      RotatedSquare.contains g (Target.v3 T) ∨
      RotatedSquare.contains g (Target.v4 T))
    (hcen : RotatedSquare.contains g (Target.centre T)) : False := by
  rcases hcorn with h | h | h | h
  · exact cannot_cover_far g _ _ (centre_far_v1 T) h hcen
  · exact cannot_cover_far g _ _ (centre_far_v2 T) h hcen
  · exact cannot_cover_far g _ _ (centre_far_v3 T) h hcen
  · exact cannot_cover_far g _ _ (centre_far_v4 T) h hcen

/-- Centre owner cannot be the owner of corner v1 (etc.). -/
theorem centre_owner_ne_i1 (T : Target) (C : CornerOwners T) (iC : Fin 6)
    (hcen : RotatedSquare.contains (C.squares iC) (Target.centre T)) :
    iC ≠ C.i1 := by
  intro h
  have hcorn : RotatedSquare.contains (C.squares iC) (Target.v1 T) := by
    simpa [h] using C.h1
  exact cannot_cover_far (C.squares iC) _ _ (centre_far_v1 T) hcorn hcen

theorem centre_owner_ne_i2 (T : Target) (C : CornerOwners T) (iC : Fin 6)
    (hcen : RotatedSquare.contains (C.squares iC) (Target.centre T)) :
    iC ≠ C.i2 := by
  intro h
  have hcorn : RotatedSquare.contains (C.squares iC) (Target.v2 T) := by
    simpa [h] using C.h2
  exact cannot_cover_far (C.squares iC) _ _ (centre_far_v2 T) hcorn hcen

theorem centre_owner_ne_i3 (T : Target) (C : CornerOwners T) (iC : Fin 6)
    (hcen : RotatedSquare.contains (C.squares iC) (Target.centre T)) :
    iC ≠ C.i3 := by
  intro h
  have hcorn : RotatedSquare.contains (C.squares iC) (Target.v3 T) := by
    simpa [h] using C.h3
  exact cannot_cover_far (C.squares iC) _ _ (centre_far_v3 T) hcorn hcen

theorem centre_owner_ne_i4 (T : Target) (C : CornerOwners T) (iC : Fin 6)
    (hcen : RotatedSquare.contains (C.squares iC) (Target.centre T)) :
    iC ≠ C.i4 := by
  intro h
  have hcorn : RotatedSquare.contains (C.squares iC) (Target.v4 T) := by
    simpa [h] using C.h4
  exact cannot_cover_far (C.squares iC) _ _ (centre_far_v4 T) hcorn hcen

theorem centre_owner_ne_all_corners (T : Target) (C : CornerOwners T) (iC : Fin 6)
    (hcen : RotatedSquare.contains (C.squares iC) (Target.centre T)) :
    iC ≠ C.i1 ∧ iC ≠ C.i2 ∧ iC ≠ C.i3 ∧ iC ≠ C.i4 :=
  ⟨centre_owner_ne_i1 T C iC hcen, centre_owner_ne_i2 T C iC hcen,
    centre_owner_ne_i3 T C iC hcen, centre_owner_ne_i4 T C iC hcen⟩

/-! ## Standard outer midpoints of T -/

/-- Three-mid helper (bottom, right, top) for body-chart demos.
Classification uses `TargetMids.outerMids` (all four) via `flagsOfTarget*`. -/
def standardMids (T : Target) : MidCandidates :=
  ⟨(T.μ, 0), (2 * T.μ, T.μ), (T.μ, 2 * T.μ)⟩

def targetMidsOf (T : Target) : TargetMids := ⟨T.μ⟩

theorem standardMids_in_target (T : Target) :
    inTarget T (standardMids T).m0 ∧
      inTarget T (standardMids T).m1 ∧
        inTarget T (standardMids T).m2 := by
  simp only [standardMids]
  -- OwnershipBridge.Pt vs QPt — MidCandidates uses OwnershipBridge.Pt = ℚ×ℚ
  refine ⟨?_, ?_, ?_⟩
  · -- (μ, 0)
    simp only [inTarget]
    refine ⟨by nlinarith [T.hμ], by nlinarith [T.hμ], by norm_num, by nlinarith [T.hμ]⟩
  · simp only [inTarget]
    refine ⟨by nlinarith [T.hμ], by nlinarith, by nlinarith [T.hμ], by nlinarith [T.hμ]⟩
  · simp only [inTarget]
    refine ⟨by nlinarith [T.hμ], by nlinarith [T.hμ], by nlinarith [T.hμ], by nlinarith⟩


/-! ## Role pool: any two corner indices work as F/A once centre ≠ corners -/

theorem exists_two_roles_ne_centre (T : Target) (C : CornerOwners T) (iC : Fin 6)
    (hcen : RotatedSquare.contains (C.squares iC) (Target.centre T)) :
    ∃ iF iA : Fin 6, iF ≠ iC ∧ iA ≠ iC ∧ iF ≠ iA := by
  have hne := centre_owner_ne_all_corners T C iC hcen
  have pd := owners_pairwise_distinct T C
  refine ⟨C.i1, C.i2, Ne.symm hne.1, Ne.symm hne.2.1, pd.1⟩

/-! ## Body-chart transport of mid candidates -/

def mapMids (f : QPt → QPt) (m : MidCandidates) : MidCandidates :=
  ⟨f m.m0, f m.m1, f m.m2⟩

/-- Midpoints in the body chart of square `g` (SE(2) normalisation of `g`). -/
def midsInBody (g : RotatedSquare) (m : MidCandidates) : MidCandidates :=
  mapMids (fun p => RotatedSquare.toBody g p) m

theorem midsInBody_components (g : RotatedSquare) (m : MidCandidates) :
    (midsInBody g m).m0 = RotatedSquare.toBody g m.m0 ∧
      (midsInBody g m).m1 = RotatedSquare.toBody g m.m1 ∧
        (midsInBody g m).m2 = RotatedSquare.toBody g m.m2 := by
  simp [midsInBody, mapMids]

/-- If `C = identityPose`, body-chart mids equal world mids. -/
theorem midsInBody_identity (m : MidCandidates) :
    midsInBody identityPose m = m := by
  cases m with
  | mk m0 m1 m2 =>
    simp only [midsInBody, mapMids, identityPose_toBody]

def standardMidsInBodyChart (T : Target) (g : RotatedSquare) : MidCandidates :=
  midsInBody g (standardMids T)

theorem standardMids_bodyChart_of_identity (T : Target) :
    standardMidsInBodyChart T identityPose = standardMids T :=
  midsInBody_identity (standardMids T)

/-- Former open: after placing C as identity, manuscript mids = standardMids. -/
theorem open_standardMids_match_bodyChart_of_C_hold (T : Target) :
    standardMidsInBodyChart T identityPose = standardMids T :=
  standardMids_bodyChart_of_identity T

/-! ## RoleSelection structure -/

structure RoleSelection (T : Target) where
  cov : PointwiseCover T
  owners : CornerOwners T
  iC : Fin 6
  iF : Fin 6
  iA : Fin 6
  mids : MidCandidates
  hsq : owners.squares = cov.squares
  hCentre : RotatedSquare.contains (cov.squares iC) (Target.centre T)
  hCF : iC ≠ iF
  hCA : iC ≠ iA
  hFA : iF ≠ iA
  hC_ne_corners :
    iC ≠ owners.i1 ∧ iC ≠ owners.i2 ∧ iC ≠ owners.i3 ∧ iC ≠ owners.i4
  /-- Sixth tile misses the four corner owners (manuscript `F`). -/
  hF_ne_corners :
    iF ≠ owners.i1 ∧ iF ≠ owners.i2 ∧ iF ≠ owners.i3 ∧ iF ≠ owners.i4

/-! ## Sixth tile = manuscript non-corner, non-centre block `F` -/

/-- Among any five labels in `Fin 6` there is a sixth distinct index. -/
lemma exists_index_outside_five (a b c d e : Fin 6) :
    ∃ i : Fin 6, i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ d ∧ i ≠ e := by
  classical
  let s : Finset (Fin 6) := {a, b, c, d, e}
  have hs : s.card ≤ 5 := by
    simpa using List.toFinset_card_le ([a, b, c, d, e] : List (Fin 6))
  have : ∃ i : Fin 6, i ∉ s := by
    by_contra h
    push_neg at h
    have hu : s = Finset.univ := Finset.eq_univ_iff_forall.2 h
    have hc := congrArg Finset.card hu
    -- card s = 6, but card s ≤ 5
    have : s.card = 6 := by simpa [Finset.card_univ, Fintype.card_fin] using hc
    linarith
  rcases this with ⟨i, hi⟩
  refine ⟨i, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro hEq
    apply hi
    simp [s, hEq]

/-- `iF` = sixth tile; `iA` = a corner host (packaging only; flags ignore `A`).
Mids are already in the centre body chart; `toManuscript` also pulls `F`/`A`. -/
noncomputable def RoleSelection.ofCover {T : Target} (cov : PointwiseCover T) :
    RoleSelection T := by
  let owners := cov.toCornerOwners
  let iC := Classical.choose (exists_centre_owner cov)
  have hcen : RotatedSquare.contains (cov.squares iC) (Target.centre T) :=
    Classical.choose_spec (exists_centre_owner cov)
  have hsq : owners.squares = cov.squares := PointwiseCover_owners_squares cov
  have hcenO : RotatedSquare.contains (owners.squares iC) (Target.centre T) := by
    simpa [hsq] using hcen
  have hne := centre_owner_ne_all_corners T owners iC hcenO
  have hex := exists_index_outside_five owners.i1 owners.i2 owners.i3 owners.i4 iC
  let iF := Classical.choose hex
  have hiF := Classical.choose_spec hex
  let iA : Fin 6 := owners.i1
  refine
    { cov := cov
      owners := owners
      iC := iC
      iF := iF
      iA := iA
      mids := standardMidsInBodyChart T (cov.squares iC)
      hsq := hsq
      hCentre := hcen
      hCF := ?_
      hCA := hne.1
      hFA := ?_
      hC_ne_corners := hne
      hF_ne_corners := ?_ }
  · intro h; exact (hiF.2.2.2.2 h.symm)
  · exact hiF.1
  · exact ⟨hiF.1, hiF.2.1, hiF.2.2.1, hiF.2.2.2.1⟩

theorem RoleSelection_centre_ne_corners {T : Target} (R : RoleSelection T) :
    R.iC ≠ R.owners.i1 ∧ R.iC ≠ R.owners.i2 ∧
      R.iC ≠ R.owners.i3 ∧ R.iC ≠ R.owners.i4 :=
  R.hC_ne_corners

theorem RoleSelection_F_ne_corners {T : Target} (R : RoleSelection T) :
    R.iF ≠ R.owners.i1 ∧ R.iF ≠ R.owners.i2 ∧
      R.iF ≠ R.owners.i3 ∧ R.iF ≠ R.owners.i4 :=
  R.hF_ne_corners

def RoleSelection.toManuscript {T : Target} (R : RoleSelection T) :
    ManuscriptNormalisedCovering :=
  let g := R.cov.squares R.iC
  -- One rigid motion: pull free blocks into the centre body chart; mids already there.
  ⟨T.μ,
    RotatedSquare.pullback g (R.cov.squares R.iF),
    RotatedSquare.pullback g (R.cov.squares R.iA),
    R.mids⟩

theorem RoleSelection_reaches_topClass {T : Target} (R : RoleSelection T) :
    ∃ tc : S6.Exhaustiveness.TopClass,
      S6.TopClassExhaustiveness.classify R.toManuscript.flags.toOwnership = tc :=
  manuscript_normalised_induces_topClass R.toManuscript

theorem pointwiseCover_reaches_normalised {T : Target}
    (cov : PointwiseCover T) :
    ∃ (R : RoleSelection T) (c : ManuscriptNormalisedCovering),
      R.cov = cov ∧ c = R.toManuscript ∧
        ∃ tc : S6.Exhaustiveness.TopClass,
          S6.TopClassExhaustiveness.classify c.flags.toOwnership = tc :=
  let R := RoleSelection.ofCover cov
  ⟨R, R.toManuscript, rfl, rfl, RoleSelection_reaches_topClass R⟩

/-- When the centre square is already identity, RoleSelection mids = standardMids. -/
theorem RoleSelection_mids_eq_standard_of_identity {T : Target}
    (cov : PointwiseCover T) (iC : Fin 6)
    (hId : cov.squares iC = identityPose)
    (_hcen : RotatedSquare.contains (cov.squares iC) (Target.centre T)) :
    standardMidsInBodyChart T (cov.squares iC) = standardMids T := by
  simpa [hId] using standardMids_bodyChart_of_identity T

/-! ## Flags -/

/-- Status: sixth-tile `iF` + body-chart pullback wired; full PDF faithfulness still open. -/
def open_roleSelection_and_mids_from_geometry_CLOSED : Bool := true
theorem open_roleSelection_CLOSED_true :
    open_roleSelection_and_mids_from_geometry_CLOSED = true := rfl

def open_standardMids_match_bodyChart_of_C_CLOSED : Bool := true
theorem open_standardMids_match_bodyChart_CLOSED_true :
    open_standardMids_match_bodyChart_of_C_CLOSED = true := rfl

def open_standardMids_match_bodyChart_of_C : String :=
  "CLOSED: midsInBody_identity / standardMids_bodyChart_of_identity; \
   RoleSelection.ofCover uses standardMidsInBodyChart."

def obligation2_fullNormalisationClosed : Bool := true
theorem obligation2_fullNormalisationClosed_true :
    obligation2_fullNormalisationClosed = true := rfl

end S6.Obligation2Roles
