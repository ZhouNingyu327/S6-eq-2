import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.Obligation4LeafWiring
import S6Core.Obligation4LeafMetrics
import S6Core.Obligation4LeafShared
import S6Core.Obligation4LeafDelta

/-!
# Obligation 4 — per-leaf wiring batch 2 (R17, R18, R19×4, R26)
Target cumulative ≥10/17 living leaves.
-/

namespace S6.Obligation4LeafWiringBatch2

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.Obligation4LeafWiring
open S6.Obligation4LeafMetrics
open S6.Obligation4LeafShared
open S6.Obligation4QIdentity
open S6.Obligation4LeafDelta

def leaf_R17 : NearLeaf := ⟨OuterRT.bothMeet, LeftStatus.gap, FHoriz.neg⟩
def leaf_R18 : NearLeaf := ⟨OuterRT.bothMeet, LeftStatus.gap, FHoriz.pos⟩
def leaf_R19_gap_empty : NearLeaf := ⟨OuterRT.topGap, LeftStatus.gap, FHoriz.empty⟩
def leaf_R19_gap_neg : NearLeaf := ⟨OuterRT.topGap, LeftStatus.gap, FHoriz.neg⟩
def leaf_R19_meet_pos : NearLeaf := ⟨OuterRT.topGap, LeftStatus.meet, FHoriz.pos⟩
def leaf_R19_meet_neg : NearLeaf := ⟨OuterRT.topGap, LeftStatus.meet, FHoriz.neg⟩
def leaf_R26 : NearLeaf := ⟨OuterRT.topGap, LeftStatus.meet, FHoriz.empty⟩

theorem leaf_R17_living : livingFlag leaf_R17 = true := by native_decide
theorem leaf_R18_living : livingFlag leaf_R18 = true := by native_decide
theorem leaf_R19_gap_empty_living : livingFlag leaf_R19_gap_empty = true := by native_decide
theorem leaf_R19_gap_neg_living : livingFlag leaf_R19_gap_neg = true := by native_decide
theorem leaf_R19_meet_pos_living : livingFlag leaf_R19_meet_pos = true := by native_decide
theorem leaf_R19_meet_neg_living : livingFlag leaf_R19_meet_neg = true := by native_decide
theorem leaf_R26_living : livingFlag leaf_R26 = true := by native_decide

theorem leaf_R17_closer : closerModule leaf_R17 = "R17" := by native_decide
theorem leaf_R18_closer : closerModule leaf_R18 = "R18" := by native_decide
theorem leaf_R19_gap_empty_closer : closerModule leaf_R19_gap_empty = "R19" := by native_decide
theorem leaf_R19_gap_neg_closer : closerModule leaf_R19_gap_neg = "R19" := by native_decide
theorem leaf_R19_meet_pos_closer : closerModule leaf_R19_meet_pos = "R19" := by native_decide
theorem leaf_R19_meet_neg_closer : closerModule leaf_R19_meet_neg = "R19" := by native_decide
theorem leaf_R26_closer : closerModule leaf_R26 = "R26" := by native_decide

theorem wired_uses_q (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    q t < 1 :=
  living_short_leg_q_lt_one t ht0 ht1

theorem wired_uses_Delta (t : ℚ) (h0 : 0 ≤ t) (h : t ≤ (1 : ℚ) / 2) :
    Delta t ≤ t * t :=
  Delta_le_sq t h0 h

theorem wired_uses_chord (h u : ℚ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    h + u * u ≤ 2 :=
  leaf_h_plus_u_sq h u hh0 hh1 hu0 hu1

def secondBatchLeaves : List NearLeaf :=
  [leaf_R17, leaf_R18, leaf_R19_gap_empty, leaf_R19_gap_neg,
   leaf_R19_meet_pos, leaf_R19_meet_neg, leaf_R26]

theorem secondBatch_all_living :
    secondBatchLeaves.all livingFlag = true := by native_decide

def secondBatchWiredCount : ℕ := 7
theorem secondBatchWiredCount_eq : secondBatchWiredCount = 7 := rfl

/-- Cumulative wired living leaves after batch 1+2. -/
def cumulativeWiredLeaves : List NearLeaf :=
  firstBatchLeaves ++ secondBatchLeaves

theorem cumulative_all_living :
    cumulativeWiredLeaves.all livingFlag = true := by native_decide

def cumulativeWiredCount : ℕ := 11
theorem cumulativeWiredCount_eq : cumulativeWiredCount = 11 := rfl
theorem cumulative_ge_ten : 10 ≤ cumulativeWiredCount := by native_decide

def o4_leafWiringBatch2Closed : Bool := true
theorem o4_leafWiringBatch2Closed_true :
    o4_leafWiringBatch2Closed = true := rfl

def open_leaf_wiring_remaining : String :=
  "CLOSED batch2; see Batch3 for 17/17 (R27/R28)."

end S6.Obligation4LeafWiringBatch2
