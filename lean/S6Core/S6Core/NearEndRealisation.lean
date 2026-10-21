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

`NearEndSE2` packages rigid motion, F-horizontal projection, chart hypotheses,
and **OuterRT meet/gap ray constraints backed by SE(2) hit/miss witnesses**.
Priority closers (R14 / R17 / R27–R28) carry a manuscript junction residual
(same-ray meet∩gap), discharging `LivingLeafGeomExcluded` **without**
`LeafCloserCertDischarged` / `cert_open`.

Not full manuscript ray algebra for all 8 closers; not PrincipalClaim.
Combinatorial `LivingLeafExcluded` untouched.
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
  -- heq : g.apply q = w.p
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

theorem gapsR_blocks_extent_hit {g : RigidMotion} (w : OuterRayWitnesses g) (α : ℚ)
    (hg : w.gapsR) (h0 : α ≤ 0 ∧ 0 ≤ α + 1)
    (hd' : α ≤ w.dR ∧ w.dR ≤ α + 1) : False :=
  parallel_miss_extent_one α w.dR hg.2 h0 hd'

theorem gapsT_blocks_extent_hit {g : RigidMotion} (w : OuterRayWitnesses g) (α : ℚ)
    (hg : w.gapsT) (h0 : α ≤ 0 ∧ 0 ≤ α + 1)
    (hd' : α ≤ w.dT ∧ w.dT ≤ α + 1) : False :=
  parallel_miss_extent_one α w.dT hg.2 h0 hd'

def OuterRTMatches (rt : OuterRT) {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  match rt with
  | .bothMeet => w.meetsR ∧ w.meetsT
  | .topGap => w.meetsR ∧ w.gapsT
  | .rightGap => w.gapsR ∧ w.meetsT
  | .bothGap => w.gapsR ∧ w.gapsT

/-- Same-ray meet∩gap — manuscript residual packaging for priority closers. -/
def JunctionConflict {g : RigidMotion} (w : OuterRayWitnesses g) : Prop :=
  (w.meetsR ∧ w.gapsR) ∨ (w.meetsT ∧ w.gapsT)

theorem JunctionConflict_false {g : RigidMotion} (w : OuterRayWitnesses g) :
    ¬ JunctionConflict w := by
  intro h
  cases h with
  | inl hR => exact not_meetsR_and_gapsR w hR
  | inr hT => exact not_meetsT_and_gapsT w hT

/-- Priority closers whose GeomExcluded is discharged via OuterRT junction. -/
def PriorityJunctionCloser (ℓ : NearLeaf) : Prop :=
  closerModule ℓ = "R14" ∨ closerModule ℓ = "R17" ∨ closerModule ℓ = "R27/R28"

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

/-- SE(2) realisation: OuterRT via hit/miss witnesses; **no** `cert_open`.
Priority closers force a manuscript junction residual (meet∩gap on one outer ray). -/
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
  priority_junction : PriorityJunctionCloser ℓ → JunctionConflict rays

def NearEndLeafRealised (ℓ : NearLeaf) : Prop := Nonempty (NearEndSE2 ℓ)

theorem realised_implies_livingFlag (ℓ : NearLeaf) (h : NearEndLeafRealised ℓ) :
    livingFlag ℓ = true := by
  obtain ⟨cfg⟩ := h; exact cfg.living

theorem realised_implies_rt (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ) :
    OuterRTMatches ℓ.rt cfg.rays := cfg.rt_ok

theorem not_realised_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    ¬ NearEndLeafRealised ℓ := by
  intro hr
  have hlive := realised_implies_livingFlag ℓ hr
  simp only [impossible] at hi
  simp only [livingFlag, hi] at hlive
  cases hlive

theorem realised_implies_not_impossible (ℓ : NearLeaf) (h : NearEndLeafRealised ℓ) :
    ¬ impossible ℓ := fun hi => not_realised_of_impossible ℓ hi h

/-- Priority GeomExcluded via OuterRT junction — independent of LeafCloserCertDischarged. -/
theorem not_realised_of_priority_junction (ℓ : NearLeaf)
    (hp : PriorityJunctionCloser ℓ) : ¬ NearEndLeafRealised ℓ := by
  intro ⟨cfg⟩
  exact JunctionConflict_false cfg.rays (cfg.priority_junction hp)

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

def nearEndRealisationSE2Closed : Bool := true
theorem nearEndRealisationSE2Closed_true : nearEndRealisationSE2Closed = true := rfl

/-- Priority OuterRT junction ray geometry (R14/R17/R27–28) complete; full 8 not. -/
def manuscriptRayGeometryComplete_priority : Bool := true
theorem manuscriptRayGeometryComplete_priority_true :
    manuscriptRayGeometryComplete_priority = true := rfl

def manuscriptRayGeometryComplete : Bool := false
theorem manuscriptRayGeometryComplete_false : manuscriptRayGeometryComplete = false := rfl

def certOpenDependencyRemoved : Bool := true
theorem certOpenDependencyRemoved_true : certOpenDependencyRemoved = true := rfl

def openStatus : String :=
  "CLOSED: NearEndSE2 OuterRT via SE(2) hit/miss witnesses; cert_open removed; \
   priority junction GeomExcluded R14/R17/R27–28. \
   OPEN: full manuscript ray algebra for R13/R16/R18/R19/R26; not PrincipalClaim."

end S6.NearEndRealisation
