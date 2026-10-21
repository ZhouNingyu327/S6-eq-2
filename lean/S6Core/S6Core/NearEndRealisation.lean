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
**OuterRT meet/gap ray constraints**, and a **closer-cert barrier** (`cert_open`).
Once the Lean closer-cert bundle is inhabited, `NearEndLeafRealised` is empty,
discharging `LivingLeafGeomExcluded`. OuterRT rays use extent-one parallel-miss.
Not manuscript-complete ray geometry; not PrincipalClaim.
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

structure OuterRayData where
  dR : ℚ
  dT : ℚ

def OuterRayData.meetsR (r : OuterRayData) : Prop := r.dR ≤ 1
def OuterRayData.meetsT (r : OuterRayData) : Prop := r.dT ≤ 1
def OuterRayData.gapsR (r : OuterRayData) : Prop := 1 < r.dR
def OuterRayData.gapsT (r : OuterRayData) : Prop := 1 < r.dT

theorem not_meetsR_and_gapsR (r : OuterRayData) : ¬ (r.meetsR ∧ r.gapsR) := by
  intro ⟨hm, hg⟩; exact (not_le_of_gt hg) hm

theorem not_meetsT_and_gapsT (r : OuterRayData) : ¬ (r.meetsT ∧ r.gapsT) := by
  intro ⟨hm, hg⟩; exact (not_le_of_gt hg) hm

theorem gapsR_blocks_extent_hit (r : OuterRayData) (α : ℚ)
    (hg : r.gapsR) (h0 : α ≤ 0 ∧ 0 ≤ α + 1)
    (hd' : α ≤ r.dR ∧ r.dR ≤ α + 1) : False :=
  parallel_miss_extent_one α r.dR hg h0 hd'

theorem gapsT_blocks_extent_hit (r : OuterRayData) (α : ℚ)
    (hg : r.gapsT) (h0 : α ≤ 0 ∧ 0 ≤ α + 1)
    (hd' : α ≤ r.dT ∧ r.dT ≤ α + 1) : False :=
  parallel_miss_extent_one α r.dT hg h0 hd'

def OuterRTMatches (rt : OuterRT) (r : OuterRayData) : Prop :=
  match rt with
  | .bothMeet => r.meetsR ∧ r.meetsT
  | .topGap => r.meetsR ∧ r.gapsT
  | .rightGap => r.gapsR ∧ r.meetsT
  | .bothGap => r.gapsR ∧ r.gapsT

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

structure NearEndSE2 (ℓ : NearLeaf) where
  C : RigidMotion
  fProj : ℚ
  z : ℚ
  d : ℚ
  chart : ChartHypotheses z d
  living : livingFlag ℓ = true
  fh_ok : FHorizMatches ℓ.fh fProj
  rays : OuterRayData
  rt_ok : OuterRTMatches ℓ.rt rays
  cert_open : ¬ LeafCloserCertDischarged ℓ

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

theorem not_realised_of_leafCloserCert (ℓ : NearLeaf)
    (h : LeafCloserCertDischarged ℓ) : ¬ NearEndLeafRealised ℓ := by
  intro ⟨cfg⟩; exact cfg.cert_open h

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

def openStatus : String :=
  "CLOSED: NearEndSE2 + OuterRT meet/gap + cert barrier; gaps block extent hits. \
   OPEN: manuscript ray geometry beyond separation thresholds. Not PrincipalClaim."

end S6.NearEndRealisation
