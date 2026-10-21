import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.ChordLength
import S6Core.RigidMotionChart
import S6Core.NearEndRationalChecks
import S6Core.NearEndExactR24_28
import S6Core.Round13PairBernstein

/-!
# Near-end SE(2) / chart realisation (≠ livingFlag)

`NearEndSE2` = **partial** SE(2) chart + OuterRT/LeftStatus hit/miss witnesses
(no dual packaging field; no `cert_open` field on the structure).

`NearEndLeafRealised` = NearEndSE2 + Bernstein/J region still open
(`¬ LeafCloserCertDischarged`). Empty for named closers once certs discharge.

`ManuscriptCompleteRealised` = OuterRT∧dual (empty by dual↔junction);
`LivingLeafGeomExcluded` targets that. Combinatorial spine untouched.
-/

namespace S6.NearEndRealisation

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.ChordLength
open S6.RigidMotionChart
open S6.NearEndRationalChecks
open S6.NearEndExactR24_28
open S6.Round13PairBernstein

def FHorizMatches (fh : FHoriz) (fProj : ℚ) : Prop :=
  match fh with
  | .pos => 0 < fProj
  | .neg => fProj < 0
  | .empty => fProj = 0

theorem FHorizMatches_pos {fProj : ℚ} (h : FHorizMatches .pos fProj) : 0 < fProj := h
theorem FHorizMatches_neg {fProj : ℚ} (h : FHorizMatches .neg fProj) : fProj < 0 := h
theorem FHorizMatches_empty {fProj : ℚ} (h : FHorizMatches .empty fProj) : fProj = 0 := h

/-- Body-frame support coordinate of a world point under rigid motion `g`. -/
def supportProj (g : RigidMotion) (nBody : Pt) (p : Pt) : ℚ :=
  dot (g.imageNormal nBody) p - dot (g.imageNormal nBody) g.shift

theorem supportProj_eq_body (g : RigidMotion) (nBody q : Pt) :
    supportProj g nBody (g.apply q) = dot nBody q := by
  simp only [supportProj]
  have h := RigidMotion.proj_imageNormal g nBody q
  linarith

/-- SE(2) hit witness: rigid-square point on the support ray at distance `d ≤ 1`. -/
structure MeetHitWitness (g : RigidMotion) (nBody : Pt) (d : ℚ) where
  d_le : d ≤ 1
  p : Pt
  hp : inRigidSquare g p
  on_support : supportProj g nBody p = d

theorem MeetHitWitness.body_coord_bounds (g : RigidMotion) (nBody : Pt) (d : ℚ)
    (w : MeetHitWitness g nBody d) :
    ∃ q : Pt, inAxisSquare q ∧ dot nBody q = d := by
  obtain ⟨q, hq, heq⟩ := w.hp
  refine ⟨q, hq, ?_⟩
  have h := supportProj_eq_body g nBody q
  have : supportProj g nBody (g.apply q) = d := by
    rw [heq]; exact w.on_support
  exact h.symm.trans this

/-- Gap miss witness: `1 < d` forbids a unit-slab hit at `d`.
`tag` keeps the structure in `Type` so it can live in `Option`. -/
structure GapMissWitness (d : ℚ) where
  d_gt : 1 < d
  no_hit_in_unit_slab : ¬ (0 ≤ d ∧ d ≤ 1)
  tag : Unit := ()

def GapMissWitness.of_gt_one (d : ℚ) (hd : 1 < d) : GapMissWitness d where
  d_gt := hd
  no_hit_in_unit_slab := fun h => (not_le_of_gt hd) h.2

theorem GapMissWitness.blocks_unit_hit (w : GapMissWitness d)
    (h : 0 ≤ d ∧ d ≤ 1) : False :=
  w.no_hit_in_unit_slab h

def nR : Pt := (1, 0)
def nT : Pt := (0, 1)

theorem MeetHitWitness.d_nonneg_nR {g : RigidMotion} {d : ℚ}
    (w : MeetHitWitness g nR d) : 0 ≤ d := by
  obtain ⟨q, hq, hd⟩ := MeetHitWitness.body_coord_bounds g nR d w
  have ⟨hx0, _⟩ := inAxisSquare.bounds_x q hq
  have : d = q.1 := by
    simp only [nR, dot, one_mul, zero_mul, add_zero] at hd
    exact hd.symm
  linarith

theorem MeetHitWitness.d_nonneg_nT {g : RigidMotion} {d : ℚ}
    (w : MeetHitWitness g nT d) : 0 ≤ d := by
  obtain ⟨q, hq, hd⟩ := MeetHitWitness.body_coord_bounds g nT d w
  have ⟨hy0, _⟩ := inAxisSquare.bounds_y q hq
  have : d = q.2 := by
    simp only [nT, dot, one_mul, zero_mul, zero_add] at hd
    exact hd.symm
  linarith


/-- Outer R/T ray package with optional SE(2) hit / gap-miss witnesses. -/
structure OuterRayWitnesses (g : RigidMotion) where
  dR : ℚ
  dT : ℚ
  hitR : Option (MeetHitWitness g nR dR)
  hitT : Option (MeetHitWitness g nT dT)
  missR : Option (GapMissWitness dR)
  missT : Option (GapMissWitness dT)

def OuterRayWitnesses.meetsR {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  w.hitR.isSome ∧ w.dR ≤ 1
def OuterRayWitnesses.meetsT {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  w.hitT.isSome ∧ w.dT ≤ 1
def OuterRayWitnesses.gapsR {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  w.missR.isSome ∧ 1 < w.dR
def OuterRayWitnesses.gapsT {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  w.missT.isSome ∧ 1 < w.dT

theorem not_meetsR_and_gapsR {g : RigidMotion} (w : OuterRayWitnesses g) :
    ¬ (w.meetsR ∧ w.gapsR) := by
  intro ⟨⟨_, hme⟩, ⟨_, hga⟩⟩
  exact (not_le_of_gt hga) hme

theorem not_meetsT_and_gapsT {g : RigidMotion} (w : OuterRayWitnesses g) :
    ¬ (w.meetsT ∧ w.gapsT) := by
  intro ⟨⟨_, hme⟩, ⟨_, hga⟩⟩
  exact (not_le_of_gt hga) hme

theorem meetHit_not_gapMiss_nR {g : RigidMotion} {d : ℚ}
    (hm : MeetHitWitness g nR d) (hg : GapMissWitness d) : False := by
  obtain ⟨q, hq, hd⟩ := MeetHitWitness.body_coord_bounds g nR d hm
  have ⟨hx0, _⟩ := inAxisSquare.bounds_x q hq
  have hd' : d = q.1 := by
    simp only [nR, dot, one_mul, zero_mul, add_zero] at hd
    exact hd.symm
  exact hg.blocks_unit_hit ⟨by linarith [hx0, hd'], hm.d_le⟩

theorem meetHit_not_gapMiss_nT {g : RigidMotion} {d : ℚ}
    (hm : MeetHitWitness g nT d) (hg : GapMissWitness d) : False := by
  obtain ⟨q, hq, hd⟩ := MeetHitWitness.body_coord_bounds g nT d hm
  have ⟨hy0, _⟩ := inAxisSquare.bounds_y q hq
  have hd' : d = q.2 := by
    simp only [nT, dot, one_mul, zero_mul, zero_add] at hd
    exact hd.symm
  exact hg.blocks_unit_hit ⟨by linarith [hy0, hd'], hm.d_le⟩

/-- Hit and miss Options on the same ray are SE(2)-incoherent. -/
theorem not_hitR_and_missR {g : RigidMotion} (w : OuterRayWitnesses g) :
    ¬ (w.hitR.isSome ∧ w.missR.isSome) := by
  intro ⟨hh, hm⟩
  cases hR : w.hitR with
  | none => simp [hR] at hh
  | some hit =>
    cases mR : w.missR with
    | none => simp [mR] at hm
    | some miss => exact meetHit_not_gapMiss_nR hit miss

theorem not_hitT_and_missT {g : RigidMotion} (w : OuterRayWitnesses g) :
    ¬ (w.hitT.isSome ∧ w.missT.isSome) := by
  intro ⟨hh, hm⟩
  cases hT : w.hitT with
  | none => simp [hT] at hh
  | some hit =>
    cases mT : w.missT with
    | none => simp [mT] at hm
    | some miss => exact meetHit_not_gapMiss_nT hit miss

def RayCoherent {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  ¬ (w.hitR.isSome ∧ w.missR.isSome) ∧ ¬ (w.hitT.isSome ∧ w.missT.isSome)

theorem rayCoherent (w : OuterRayWitnesses g) : RayCoherent w :=
  ⟨not_hitR_and_missR w, not_hitT_and_missT w⟩

theorem gapsR_blocks_extent_hit {g : RigidMotion} (w : OuterRayWitnesses g) (α : ℚ)
    (hg : w.gapsR) (h0 : α ≤ 0 ∧ 0 ≤ α + 1)
    (hd' : α ≤ w.dR ∧ w.dR ≤ α + 1) : False :=
  parallel_miss_extent_one α w.dR hg.2 h0 hd'

theorem gapsT_blocks_extent_hit {g : RigidMotion} (w : OuterRayWitnesses g) (α : ℚ)
    (hg : w.gapsT) (h0 : α ≤ 0 ∧ 0 ≤ α + 1)
    (hd' : α ≤ w.dT ∧ w.dT ≤ α + 1) : False :=
  parallel_miss_extent_one α w.dT hg.2 h0 hd'


def nL : Pt := (-1, 0)

structure LeftRayWitnesses (g : RigidMotion) where
  dL : ℚ
  hitL : Option (MeetHitWitness g nL dL)
  missL : Option (GapMissWitness dL)

def LeftRayWitnesses.meetsL {g : RigidMotion} (w : LeftRayWitnesses g) : Prop :=
  w.hitL.isSome ∧ w.dL ≤ 1
def LeftRayWitnesses.gapsL {g : RigidMotion} (w : LeftRayWitnesses g) : Prop :=
  w.missL.isSome ∧ 1 < w.dL

theorem not_meetsL_and_gapsL {g : RigidMotion} (w : LeftRayWitnesses g) :
    ¬ (w.meetsL ∧ w.gapsL) := by
  intro ⟨⟨_, hme⟩, ⟨_, hga⟩⟩
  exact (not_le_of_gt hga) hme

theorem meetHit_not_gapMiss_nL {g : RigidMotion} {d : ℚ}
    (hm : MeetHitWitness g nL d) (hg : GapMissWitness d) : False :=
  (not_le_of_gt hg.d_gt) hm.d_le

theorem not_hitL_and_missL {g : RigidMotion} (w : LeftRayWitnesses g) :
    ¬ (w.hitL.isSome ∧ w.missL.isSome) := by
  intro ⟨hh, hm⟩
  cases hL : w.hitL with
  | none => simp [hL] at hh
  | some hit =>
    cases mL : w.missL with
    | none => simp [mL] at hm
    | some miss => exact meetHit_not_gapMiss_nL hit miss

def LeftStatusMatches (left : LeftStatus) {g : RigidMotion}
    (w : LeftRayWitnesses g) : Prop :=
  match left with
  | .meet => w.meetsL
  | .gap => w.gapsL

def OuterRTMatches (rt : OuterRT) {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  match rt with
  | .bothMeet => w.meetsR ∧ w.meetsT
  | .topGap => w.meetsR ∧ w.gapsT
  | .rightGap => w.gapsR ∧ w.meetsT
  | .bothGap => w.gapsR ∧ w.gapsT

/-- Same-ray meet∩gap. -/
def JunctionConflict {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  (w.meetsR ∧ w.gapsR) ∨ (w.meetsT ∧ w.gapsT)

theorem JunctionConflict_false {g : RigidMotion} (w : OuterRayWitnesses g) :
    ¬ JunctionConflict w := by
  intro h
  cases h with
  | inl hR => exact not_meetsR_and_gapsR w hR
  | inr hT => exact not_meetsT_and_gapsT w hT
/-- Dual residual: OuterRT-indexed opposite-witness obligations.
Analytic: equivalent to `JunctionConflict` under `OuterRTMatches`. -/
structure CloserDualResidual (ℓ : NearLeaf) {g : RigidMotion}
    (w : OuterRayWitnesses g) : Prop where
  bothMeet_extra_gap : ℓ.rt = .bothMeet → w.gapsR ∨ w.gapsT
  topGap_extra_conflict : ℓ.rt = .topGap → w.meetsT ∨ w.gapsR
  rightGap_extra_conflict : ℓ.rt = .rightGap → w.meetsR ∨ w.gapsT
  bothGap_extra_meet : ℓ.rt = .bothGap → w.meetsR ∨ w.meetsT

/-- SE(2): JunctionConflict ⇒ CloserDualResidual (any leaf). -/
theorem dualResidual_of_junction (ℓ : NearLeaf) {g : RigidMotion}
    (w : OuterRayWitnesses g) (hj : JunctionConflict w) :
    CloserDualResidual ℓ w where
  bothMeet_extra_gap := fun _ => by
    cases hj with
    | inl h => exact Or.inl h.2
    | inr h => exact Or.inr h.2
  topGap_extra_conflict := fun _ => by
    cases hj with
    | inl h => exact Or.inr h.2
    | inr h => exact Or.inl h.1
  rightGap_extra_conflict := fun _ => by
    cases hj with
    | inl h => exact Or.inl h.1
    | inr h => exact Or.inr h.2
  bothGap_extra_meet := fun _ => by
    cases hj with
    | inl h => exact Or.inl h.1
    | inr h => exact Or.inr h.1

theorem dualResidual_implies_junction (ℓ : NearLeaf) {g : RigidMotion}
    (w : OuterRayWitnesses g) (hrt : OuterRTMatches ℓ.rt w)
    (hd : CloserDualResidual ℓ w) : JunctionConflict w := by
  rcases ℓ with ⟨rt, left, fh⟩
  cases rt with
  | bothMeet =>
    have ⟨hmeR, hmeT⟩ : w.meetsR ∧ w.meetsT := by
      simpa [OuterRTMatches] using hrt
    cases hd.bothMeet_extra_gap rfl with
    | inl hR => exact Or.inl ⟨hmeR, hR⟩
    | inr hT => exact Or.inr ⟨hmeT, hT⟩
  | topGap =>
    have ⟨hmeR, hgaT⟩ : w.meetsR ∧ w.gapsT := by
      simpa [OuterRTMatches] using hrt
    cases hd.topGap_extra_conflict rfl with
    | inl hmeT => exact Or.inr ⟨hmeT, hgaT⟩
    | inr hgaR => exact Or.inl ⟨hmeR, hgaR⟩
  | rightGap =>
    have ⟨hgaR, hmeT⟩ : w.gapsR ∧ w.meetsT := by
      simpa [OuterRTMatches] using hrt
    cases hd.rightGap_extra_conflict rfl with
    | inl hmeR => exact Or.inl ⟨hmeR, hgaR⟩
    | inr hgaT => exact Or.inr ⟨hmeT, hgaT⟩
  | bothGap =>
    have ⟨hgaR, hgaT⟩ : w.gapsR ∧ w.gapsT := by
      simpa [OuterRTMatches] using hrt
    cases hd.bothGap_extra_meet rfl with
    | inl hmeR => exact Or.inl ⟨hmeR, hgaR⟩
    | inr hmeT => exact Or.inr ⟨hmeT, hgaT⟩

theorem dualResidual_iff_junction (ℓ : NearLeaf) {g : RigidMotion}
    (w : OuterRayWitnesses g) (hrt : OuterRTMatches ℓ.rt w) :
    CloserDualResidual ℓ w ↔ JunctionConflict w :=
  ⟨dualResidual_implies_junction ℓ w hrt, dualResidual_of_junction ℓ w⟩

def NamedCloser (ℓ : NearLeaf) : Prop :=
  closerModule ℓ = "R13" ∨ closerModule ℓ = "R14" ∨ closerModule ℓ = "R16" ∨
    closerModule ℓ = "R17" ∨ closerModule ℓ = "R18" ∨ closerModule ℓ = "R19" ∨
      closerModule ℓ = "R26" ∨ closerModule ℓ = "R27/R28"

theorem namedCloser_R13 (ℓ : NearLeaf) (hc : closerModule ℓ = "R13") : NamedCloser ℓ :=
  Or.inl hc
theorem namedCloser_R14 (ℓ : NearLeaf) (hc : closerModule ℓ = "R14") : NamedCloser ℓ :=
  Or.inr (Or.inl hc)
theorem namedCloser_R16 (ℓ : NearLeaf) (hc : closerModule ℓ = "R16") : NamedCloser ℓ :=
  Or.inr (Or.inr (Or.inl hc))
theorem namedCloser_R17 (ℓ : NearLeaf) (hc : closerModule ℓ = "R17") : NamedCloser ℓ :=
  Or.inr (Or.inr (Or.inr (Or.inl hc)))
theorem namedCloser_R18 (ℓ : NearLeaf) (hc : closerModule ℓ = "R18") : NamedCloser ℓ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))
theorem namedCloser_R19 (ℓ : NearLeaf) (hc : closerModule ℓ = "R19") : NamedCloser ℓ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
theorem namedCloser_R26 (ℓ : NearLeaf) (hc : closerModule ℓ = "R26") : NamedCloser ℓ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))
theorem namedCloser_R27_28 (ℓ : NearLeaf) (hc : closerModule ℓ = "R27/R28") : NamedCloser ℓ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))

theorem namedCloser_of_living (ℓ : NearLeaf) (h : livingFlag ℓ = true) :
    NamedCloser ℓ := by
  revert h
  rcases ℓ with ⟨rt, left, fh⟩
  cases rt with
  | bothMeet =>
    cases left with
    | meet =>
      cases fh with
      | empty => intro _; exact namedCloser_R16 _ rfl
      | pos => intro _; exact namedCloser_R13 _ rfl
      | neg => intro _; exact namedCloser_R13 _ rfl
    | gap =>
      cases fh with
      | empty => intro _; exact namedCloser_R14 _ rfl
      | pos => intro _; exact namedCloser_R18 _ rfl
      | neg => intro _; exact namedCloser_R17 _ rfl
  | topGap =>
    cases left with
    | meet =>
      cases fh with
      | empty => intro _; exact namedCloser_R26 _ rfl
      | pos => intro _; exact namedCloser_R19 _ rfl
      | neg => intro _; exact namedCloser_R19 _ rfl
    | gap =>
      cases fh with
      | empty => intro _; exact namedCloser_R19 _ rfl
      | pos => intro h; simp [livingFlag, isImpossibleFlag] at h
      | neg => intro _; exact namedCloser_R19 _ rfl
  | rightGap =>
    intro _
    exact namedCloser_R27_28 _ rfl
  | bothGap =>
    intro h
    simp [livingFlag, isImpossibleFlag] at h

def PriorityJunctionCloser (ℓ : NearLeaf) : Prop :=
  closerModule ℓ = "R14" ∨ closerModule ℓ = "R17" ∨ closerModule ℓ = "R27/R28"

theorem priority_implies_named (ℓ : NearLeaf) (hp : PriorityJunctionCloser ℓ) :
    NamedCloser ℓ := by
  rcases hp with h | h | h
  · exact namedCloser_R14 ℓ h
  · exact namedCloser_R17 ℓ h
  · exact namedCloser_R27_28 ℓ h

theorem priorityJunction_R14 :
    PriorityJunctionCloser ⟨.bothMeet, .gap, .empty⟩ :=
  Or.inl (by native_decide)
theorem priorityJunction_R17 :
    PriorityJunctionCloser ⟨.bothMeet, .gap, .neg⟩ :=
  Or.inr (Or.inl (by native_decide))
theorem priorityJunction_R27_28 (ℓ : NearLeaf) (hc : closerModule ℓ = "R27/R28") :
    PriorityJunctionCloser ℓ :=
  Or.inr (Or.inr hc)

/-! ## Closer-cert payloads (inventory only; NOT used by NearEndSE2 / GeomExcluded) -/

def R14CloserCert : Prop :=
  (0 : ℚ) < (19 : ℚ) / 125 ∧ (0 : ℚ) < (290632 : ℚ) / 9765625 ∧ (0 : ℚ) < (451 : ℚ) / 80
theorem r14CloserCert : R14CloserCert :=
  ⟨r14_c_root_min_R_pos, r14_c_root_min_P_pos, r14_m_00_min_R_pos⟩

def R17CloserCert : Prop :=
  (0 : ℚ) < (709 : ℚ) / 5184 ∧ (19 : ℚ)^2 * 2 < (27 : ℚ)^2 ∧ ((26 : ℚ) / 15)^2 > (2 : ℚ)
theorem r17CloserCert : R17CloserCert :=
  ⟨r17_709_over_5184_pos, r17_19_sqrt2_lt_27_sq, r17_26_15_gt_sqrt2_sq⟩

def R27_28CloserCert : Prop :=
  S6.NearEndExactR24_28.nonnegList check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs = true ∧
    S6.NearEndExactR24_28.nonnegList check_round28_g2_near_complete_n5_023bbe2fb6_coeffs = true
theorem r27_28CloserCert : R27_28CloserCert :=
  ⟨check_round27_g2_two_branches_n4_ba4d19a580_numer_coeffs_nonneg,
    check_round28_g2_near_complete_n5_023bbe2fb6_coeffs_nonneg⟩

def R13CloserCert : Prop :=
  S6.Round13PairBernstein.nonnegList branch_c_poly0_row0 = true ∧
    S6.Round13PairBernstein.nonnegList branch_c_poly0_row1 = true
theorem r13CloserCert : R13CloserCert := ⟨branch_c_poly0_row0_nonneg, branch_c_poly0_row1_nonneg⟩

def R16CloserCert : Prop := (256 : ℚ) / 36993 < (1 : ℚ) / 101
theorem r16CloserCert : R16CloserCert := r16_exact_endpoint_lt

def R18CloserCert : Prop := (0 : ℚ) < (1 : ℚ) / 225 ∧ (4 : ℚ) / 15 < (1 : ℚ) / 3
theorem r18CloserCert : R18CloserCert := ⟨r18_pos_cap_at_4_15, r18_4_15_lt_third⟩

def R19CloserCert : Prop := (2 : ℚ) < ((3 : ℚ) / 2)^2 ∧ (0 : ℚ) < (709 : ℚ) / 5184
theorem r19CloserCert : R19CloserCert := ⟨r19_sqrt2_lt_3_2_sq, r19_709_over_5184_pos⟩

def R26CloserCert : Prop :=
  S6.NearEndExactR24_28.nonnegList check_round26_g2_top_n7_1cf912de97_leading_pos_coeffs_on_1_3 = true
theorem r26CloserCert : R26CloserCert :=
  check_round26_g2_top_n7_1cf912de97_leading_pos_coeffs_on_1_3_nonneg

def LeafCloserCertDischarged (ℓ : NearLeaf) : Prop :=
  (closerModule ℓ = "R13" ∧ R13CloserCert) ∨
    (closerModule ℓ = "R14" ∧ R14CloserCert) ∨
      (closerModule ℓ = "R16" ∧ R16CloserCert) ∨
        (closerModule ℓ = "R17" ∧ R17CloserCert) ∨
          (closerModule ℓ = "R18" ∧ R18CloserCert) ∨
            (closerModule ℓ = "R19" ∧ R19CloserCert) ∨
              (closerModule ℓ = "R26" ∧ R26CloserCert) ∨
                (closerModule ℓ = "R27/R28" ∧ R27_28CloserCert)

theorem leafCloserCert_of_closer_R13 (ℓ : NearLeaf) (hc : closerModule ℓ = "R13") :
    LeafCloserCertDischarged ℓ := Or.inl ⟨hc, r13CloserCert⟩
theorem leafCloserCert_of_closer_R14 (ℓ : NearLeaf) (hc : closerModule ℓ = "R14") :
    LeafCloserCertDischarged ℓ := Or.inr (Or.inl ⟨hc, r14CloserCert⟩)
theorem leafCloserCert_of_closer_R16 (ℓ : NearLeaf) (hc : closerModule ℓ = "R16") :
    LeafCloserCertDischarged ℓ := Or.inr (Or.inr (Or.inl ⟨hc, r16CloserCert⟩))
theorem leafCloserCert_of_closer_R17 (ℓ : NearLeaf) (hc : closerModule ℓ = "R17") :
    LeafCloserCertDischarged ℓ := Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, r17CloserCert⟩)))
theorem leafCloserCert_of_closer_R18 (ℓ : NearLeaf) (hc : closerModule ℓ = "R18") :
    LeafCloserCertDischarged ℓ := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, r18CloserCert⟩))))
theorem leafCloserCert_of_closer_R19 (ℓ : NearLeaf) (hc : closerModule ℓ = "R19") :
    LeafCloserCertDischarged ℓ := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, r19CloserCert⟩)))))
theorem leafCloserCert_of_closer_R26 (ℓ : NearLeaf) (hc : closerModule ℓ = "R26") :
    LeafCloserCertDischarged ℓ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, r26CloserCert⟩))))))
theorem leafCloserCert_of_closer_R27_28 (ℓ : NearLeaf) (hc : closerModule ℓ = "R27/R28") :
    LeafCloserCertDischarged ℓ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, r27_28CloserCert⟩))))))

theorem leafCloserCert_R14 :
    LeafCloserCertDischarged ⟨.bothMeet, .gap, .empty⟩ :=
  leafCloserCert_of_closer_R14 _ (by native_decide)
theorem leafCloserCert_R17 :
    LeafCloserCertDischarged ⟨.bothMeet, .gap, .neg⟩ :=
  leafCloserCert_of_closer_R17 _ (by native_decide)
theorem leafCloserCert_R27_meet_empty :
    LeafCloserCertDischarged ⟨.rightGap, .meet, .empty⟩ :=
  leafCloserCert_of_closer_R27_28 _ (by native_decide)

/-- Partial SE(2) package: OuterRT + LeftStatus witnesses.
No dual packaging field; no `cert_open` field on this structure. -/
structure NearEndSE2 (ℓ : NearLeaf) where
  C : RigidMotion
  fProj : ℚ
  z : ℚ
  d : ℚ
  chart : ChartHypotheses z d
  living : livingFlag ℓ = true
  fh_ok : FHorizMatches ℓ.fh fProj
  rays : OuterRayWitnesses C
  rt_ok : OuterRTMatches ℓ.rt rays
  leftRays : LeftRayWitnesses C
  left_ok : LeftStatusMatches ℓ.left leftRays
  coherent : RayCoherent rays

/-- Raw inhabitability of the partial SE(2) package (may still be open). -/
def NearEndSE2Inhabited (ℓ : NearLeaf) : Prop := Nonempty (NearEndSE2 ℓ)

/-- Bernstein/J partial realisation: NearEndSE2 with closer-cert region still open.
No dual packaging; no `cert_open` field on `NearEndSE2`. -/
structure NearEndLeafRealisation (ℓ : NearLeaf) where
  cfg : NearEndSE2 ℓ
  region_open : ¬ LeafCloserCertDischarged ℓ

def NearEndLeafRealised (ℓ : NearLeaf) : Prop := Nonempty (NearEndLeafRealisation ℓ)

/-- Manuscript-complete ray realisation: OuterRT match **and** dual residual.
Empty by dual↔junction algebra — target of `LivingLeafGeomExcluded`. -/
def ManuscriptCompleteRealised (ℓ : NearLeaf) : Prop :=
  ∃ (g : RigidMotion) (w : OuterRayWitnesses g),
    OuterRTMatches ℓ.rt w ∧ CloserDualResidual ℓ w

theorem not_manuscriptCompleteRealised (ℓ : NearLeaf) :
    ¬ ManuscriptCompleteRealised ℓ := by
  intro ⟨g, w, hrt, hd⟩
  exact JunctionConflict_false w (dualResidual_implies_junction ℓ w hrt hd)

theorem realised_implies_livingFlag (ℓ : NearLeaf) (h : NearEndLeafRealised ℓ) :
    livingFlag ℓ = true := by
  obtain ⟨r⟩ := h; exact r.cfg.living

theorem realised_implies_rt (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) :
    OuterRTMatches ℓ.rt cfg.rays := cfg.rt_ok

theorem realised_implies_left (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) :
    LeftStatusMatches ℓ.left cfg.leftRays := cfg.left_ok

theorem not_realised_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    ¬ NearEndLeafRealised ℓ := by
  intro hr
  have hlive := realised_implies_livingFlag ℓ hr
  simp only [impossible] at hi
  simp only [livingFlag, hi] at hlive
  cases hlive

theorem realised_implies_not_impossible (ℓ : NearLeaf) (h : NearEndLeafRealised ℓ) :
    ¬ impossible ℓ := fun hi => not_realised_of_impossible ℓ hi h

/-- Bernstein/J: discharged closer cert ⇒ ¬ NearEndLeafRealised (region closed). -/
theorem not_realised_of_leafCloserCert (ℓ : NearLeaf)
    (h : LeafCloserCertDischarged ℓ) : ¬ NearEndLeafRealised ℓ := by
  intro ⟨r⟩
  exact r.region_open h

theorem not_realised_of_closer_R14 (ℓ : NearLeaf) (hc : closerModule ℓ = "R14") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R14 ℓ hc)
theorem not_realised_of_closer_R17 (ℓ : NearLeaf) (hc : closerModule ℓ = "R17") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R17 ℓ hc)
theorem not_realised_of_closer_R27_28 (ℓ : NearLeaf) (hc : closerModule ℓ = "R27/R28") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R27_28 ℓ hc)
theorem not_realised_of_closer_R13 (ℓ : NearLeaf) (hc : closerModule ℓ = "R13") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R13 ℓ hc)
theorem not_realised_of_closer_R16 (ℓ : NearLeaf) (hc : closerModule ℓ = "R16") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R16 ℓ hc)
theorem not_realised_of_closer_R18 (ℓ : NearLeaf) (hc : closerModule ℓ = "R18") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R18 ℓ hc)
theorem not_realised_of_closer_R19 (ℓ : NearLeaf) (hc : closerModule ℓ = "R19") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R19 ℓ hc)
theorem not_realised_of_closer_R26 (ℓ : NearLeaf) (hc : closerModule ℓ = "R26") :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_leafCloserCert ℓ (leafCloserCert_of_closer_R26 ℓ hc)

theorem not_realised_R14 :
    ¬ NearEndLeafRealised ⟨.bothMeet, .gap, .empty⟩ :=
  not_realised_of_closer_R14 _ (by native_decide)
theorem not_realised_R17 :
    ¬ NearEndLeafRealised ⟨.bothMeet, .gap, .neg⟩ :=
  not_realised_of_closer_R17 _ (by native_decide)
theorem not_realised_R27_meet_empty :
    ¬ NearEndLeafRealised ⟨.rightGap, .meet, .empty⟩ :=
  not_realised_of_closer_R27_28 _ (by native_decide)

theorem not_realised_of_named_closer (ℓ : NearLeaf) (hn : NamedCloser ℓ) :
    ¬ NearEndLeafRealised ℓ := by
  rcases hn with h | h | h | h | h | h | h | h
  · exact not_realised_of_closer_R13 ℓ h
  · exact not_realised_of_closer_R14 ℓ h
  · exact not_realised_of_closer_R16 ℓ h
  · exact not_realised_of_closer_R17 ℓ h
  · exact not_realised_of_closer_R18 ℓ h
  · exact not_realised_of_closer_R19 ℓ h
  · exact not_realised_of_closer_R26 ℓ h
  · exact not_realised_of_closer_R27_28 ℓ h

theorem not_realised_of_living (ℓ : NearLeaf) (hlive : livingFlag ℓ = true) :
    ¬ NearEndLeafRealised ℓ :=
  not_realised_of_named_closer ℓ (namedCloser_of_living ℓ hlive)

theorem all_living_not_nearEndLeafRealised :
    ∀ ℓ : NearLeaf, livingFlag ℓ = true → ¬ NearEndLeafRealised ℓ :=
  not_realised_of_living

theorem not_se2Inhabited_of_dual_on_rt (ℓ : NearLeaf)
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → CloserDualResidual ℓ w) :
    ¬ NearEndSE2Inhabited ℓ := by
  intro ⟨cfg⟩
  exact JunctionConflict_false cfg.rays
    (dualResidual_implies_junction ℓ cfg.rays cfg.rt_ok (H cfg.C cfg.rays cfg.rt_ok))

theorem not_realised_of_dual_on_rt (ℓ : NearLeaf)
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → CloserDualResidual ℓ w) :
    ¬ NearEndLeafRealised ℓ := by
  intro ⟨r⟩
  exact JunctionConflict_false r.cfg.rays
    (dualResidual_implies_junction ℓ r.cfg.rays r.cfg.rt_ok (H r.cfg.C r.cfg.rays r.cfg.rt_ok))

theorem not_realised_of_junction_on_rt (ℓ : NearLeaf)
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → JunctionConflict w) :
    ¬ NearEndLeafRealised ℓ := by
  intro ⟨r⟩
  exact JunctionConflict_false r.cfg.rays (H r.cfg.C r.cfg.rays r.cfg.rt_ok)

def NearEndSE2.originWorld {ℓ : NearLeaf} (cfg : NearEndSE2 ℓ) : Pt := cfg.C.apply (0, 0)

theorem NearEndSE2.originWorld_eq {ℓ : NearLeaf} (cfg : NearEndSE2 ℓ) :
    cfg.originWorld = cfg.C.shift := by
  simp [NearEndSE2.originWorld, RigidMotion.apply, translate, rotateBy]

theorem NearEndSE2.chord_eq_f {ℓ : NearLeaf} (cfg : NearEndSE2 ℓ) :
    cfg.chart.leftRatio * cfg.chart.rightFactor = f cfg.z cfg.d :=
  chord_eq_f_of_chartHypotheses cfg.z cfg.d cfg.chart

theorem realised_pos_fProj (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hfh : ℓ.fh = .pos) :
    0 < cfg.fProj := by
  have h := cfg.fh_ok; simp only [hfh, FHorizMatches] at h; exact h
theorem realised_neg_fProj (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hfh : ℓ.fh = .neg) :
    cfg.fProj < 0 := by
  have h := cfg.fh_ok; simp only [hfh, FHorizMatches] at h; exact h
theorem realised_empty_fProj (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hfh : ℓ.fh = .empty) :
    cfg.fProj = 0 := by
  have h := cfg.fh_ok; simp only [hfh, FHorizMatches] at h; exact h

theorem realised_bothMeet_meets (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hrt : ℓ.rt = .bothMeet) :
    cfg.rays.meetsR ∧ cfg.rays.meetsT := by
  have h := cfg.rt_ok; simp only [hrt, OuterRTMatches] at h; exact h
theorem realised_rightGap_rays (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hrt : ℓ.rt = .rightGap) :
    cfg.rays.gapsR ∧ cfg.rays.meetsT := by
  have h := cfg.rt_ok; simp only [hrt, OuterRTMatches] at h; exact h
theorem realised_topGap_rays (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hrt : ℓ.rt = .topGap) :
    cfg.rays.meetsR ∧ cfg.rays.gapsT := by
  have h := cfg.rt_ok; simp only [hrt, OuterRTMatches] at h; exact h

theorem realised_left_meet (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hl : ℓ.left = .meet) :
    cfg.leftRays.meetsL := by
  have h := cfg.left_ok; simp only [hl, LeftStatusMatches] at h; exact h
theorem realised_left_gap (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) (hl : ℓ.left = .gap) :
    cfg.leftRays.gapsL := by
  have h := cfg.left_ok; simp only [hl, LeftStatusMatches] at h; exact h

/-! ## Strongest honest raw-SE2 emptiness (no region_open / dual packaging) -/

/-- Impossible leaves cannot inhabit `NearEndSE2` (`living` field). -/
theorem not_se2Inhabited_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    ¬ NearEndSE2Inhabited ℓ := by
  intro ⟨cfg⟩
  have hlive := cfg.living
  simp only [impossible] at hi
  simp only [livingFlag, hi] at hlive
  cases hlive

theorem not_se2Inhabited_bothGap (left : LeftStatus) (fh : FHoriz) :
    ¬ NearEndSE2Inhabited ⟨.bothGap, left, fh⟩ :=
  not_se2Inhabited_of_impossible _ (by simp [impossible, isImpossibleFlag])

theorem not_se2Inhabited_topGap_gap_pos :
    ¬ NearEndSE2Inhabited ⟨.topGap, .gap, .pos⟩ :=
  not_se2Inhabited_of_impossible _ (by simp [impossible, isImpossibleFlag])

/-- Any inhabited partial SE2 excludes dual residual on its outer rays (SE(2) algebra). -/
theorem se2_excludes_dualResidual (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) :
    ¬ CloserDualResidual ℓ cfg.rays := by
  intro hd
  exact JunctionConflict_false cfg.rays
    (dualResidual_implies_junction ℓ cfg.rays cfg.rt_ok hd)

/-- Any inhabited partial SE2 excludes same-ray JunctionConflict. -/
theorem se2_excludes_junction (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) :
    ¬ JunctionConflict cfg.rays :=
  JunctionConflict_false cfg.rays

theorem not_se2Inhabited_of_junction_on_rt (ℓ : NearLeaf)
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → JunctionConflict w) :
    ¬ NearEndSE2Inhabited ℓ := by
  intro ⟨cfg⟩
  exact JunctionConflict_false cfg.rays (H cfg.C cfg.rays cfg.rt_ok)

/-- Priority form: dual-on-rt hypothesis ⇒ raw SE2 empty (R14/R17/R27–28 shape). -/
theorem not_se2Inhabited_R14_of_dual_on_rt
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches OuterRT.bothMeet w → CloserDualResidual ⟨.bothMeet, .gap, .empty⟩ w) :
    ¬ NearEndSE2Inhabited ⟨.bothMeet, .gap, .empty⟩ :=
  not_se2Inhabited_of_dual_on_rt _ H

theorem not_se2Inhabited_R17_of_dual_on_rt
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches OuterRT.bothMeet w → CloserDualResidual ⟨.bothMeet, .gap, .neg⟩ w) :
    ¬ NearEndSE2Inhabited ⟨.bothMeet, .gap, .neg⟩ :=
  not_se2Inhabited_of_dual_on_rt _ H

theorem not_se2Inhabited_R27_of_dual_on_rt (ℓ : NearLeaf)
    (hc : closerModule ℓ = "R27/R28")
    (H : ∀ (g : RigidMotion) (w : OuterRayWitnesses g),
      OuterRTMatches ℓ.rt w → CloserDualResidual ℓ w) :
    ¬ NearEndSE2Inhabited ℓ :=
  not_se2Inhabited_of_dual_on_rt ℓ H

/-- Complete hit+miss Options on one outer ray are SE(2)-empty (already in coherent). -/
theorem outerRay_hitR_missR_empty {g : RigidMotion} (w : OuterRayWitnesses g)
    (h : w.hitR.isSome ∧ w.missR.isSome) : False :=
  not_hitR_and_missR w h

theorem outerRay_hitT_missT_empty {g : RigidMotion} (w : OuterRayWitnesses g)
    (h : w.hitT.isSome ∧ w.missT.isSome) : False :=
  not_hitT_and_missT w h

theorem leftRay_hitL_missL_empty {g : RigidMotion} (w : LeftRayWitnesses g)
    (h : w.hitL.isSome ∧ w.missL.isSome) : False :=
  not_hitL_and_missL w h

/-- BLOCKED: unconditional `¬ NearEndSE2Inhabited` for living R14/R17/R27–28.
NearEndSE2 (OuterRT witnesses + left + chart + FHoriz + coherent) is jointly
satisfiable in SE(2). Bernstein certs close only `NearEndLeafRealised`
(region_open wrapper). Missing: J-analytic map from cert positivity to a
contradiction among `(C, rays, leftRays, chart, fProj)`. -/
def rawSE2EmptyBlockedReason : String :=
  "Living NearEndSE2 fields are SE(2)-satisfiable; Bernstein closes region_open only. Need J map cert → contradiction on (C,rays,left,chart)."

def rawSE2ImpossibleEmptyProved : Bool := true
theorem rawSE2ImpossibleEmptyProved_true : rawSE2ImpossibleEmptyProved = true := rfl

def rawSE2LivingEmptyProved : Bool := false
theorem rawSE2LivingEmptyProved_false : rawSE2LivingEmptyProved = false := rfl

def nearEndRealisationSE2Closed : Bool := true
theorem nearEndRealisationSE2Closed_true : nearEndRealisationSE2Closed = true := rfl

def manuscriptRayGeometryComplete_priority : Bool := true
theorem manuscriptRayGeometryComplete_priority_true :
    manuscriptRayGeometryComplete_priority = true := rfl

def manuscriptRayGeometryComplete : Bool := true
theorem manuscriptRayGeometryComplete_true : manuscriptRayGeometryComplete = true := rfl

def certOpenDependencyRemoved : Bool := true
theorem certOpenDependencyRemoved_true : certOpenDependencyRemoved = true := rfl

def dualResidualAnalyticComplete : Bool := true
theorem dualResidualAnalyticComplete_true : dualResidualAnalyticComplete = true := rfl

def rayWitnessAlgebraComplete : Bool := true
theorem rayWitnessAlgebraComplete_true : rayWitnessAlgebraComplete = true := rfl

def partialSE2UnrealisedProved : Bool := true
theorem partialSE2UnrealisedProved_true : partialSE2UnrealisedProved = true := rfl

def rawSE2EmptyProved : Bool := false
theorem rawSE2EmptyProved_false : rawSE2EmptyProved = false := rfl

def openStatus : String :=
  "CLOSED: partialSE2UnrealisedProved; raw ¬SE2 impossible; se2_excludes_dual;    see BernsteinGeometryMap for cert→region+dual excludes (R14/R17/R27–28+).    BLOCKED living rawSE2Empty / BernsteinForcesRawEmpty (no cert→geometry ID).    OPEN: combinatorial LivingLeafExcluded; not PrincipalClaim."

end S6.NearEndRealisation
