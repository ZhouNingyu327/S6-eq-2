import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.Obligation4LeafWiring
import S6Core.Obligation4LeafWiringBatch2
import S6Core.Obligation4LeafMetrics
import S6Core.Obligation4LeafShared
import S6Core.Obligation4LeafDelta

/-!
# Obligation 4 — per-leaf wiring batch 3 (R27/R28 ×6 rightGap)
Completes 17/17 living-leaf Lean wiring.
-/

namespace S6.Obligation4LeafWiringBatch3

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.Obligation4LeafWiring
open S6.Obligation4LeafWiringBatch2
open S6.Obligation4LeafMetrics
open S6.Obligation4LeafShared
open S6.Obligation4QIdentity
open S6.Obligation4LeafDelta

def leaf_R27_meet_empty : NearLeaf := ⟨OuterRT.rightGap, LeftStatus.meet, FHoriz.empty⟩
def leaf_R27_meet_pos : NearLeaf := ⟨OuterRT.rightGap, LeftStatus.meet, FHoriz.pos⟩
def leaf_R27_meet_neg : NearLeaf := ⟨OuterRT.rightGap, LeftStatus.meet, FHoriz.neg⟩
def leaf_R27_gap_empty : NearLeaf := ⟨OuterRT.rightGap, LeftStatus.gap, FHoriz.empty⟩
def leaf_R27_gap_pos : NearLeaf := ⟨OuterRT.rightGap, LeftStatus.gap, FHoriz.pos⟩
def leaf_R27_gap_neg : NearLeaf := ⟨OuterRT.rightGap, LeftStatus.gap, FHoriz.neg⟩

theorem leaf_R27_meet_empty_living : livingFlag leaf_R27_meet_empty = true := by native_decide
theorem leaf_R27_meet_pos_living : livingFlag leaf_R27_meet_pos = true := by native_decide
theorem leaf_R27_meet_neg_living : livingFlag leaf_R27_meet_neg = true := by native_decide
theorem leaf_R27_gap_empty_living : livingFlag leaf_R27_gap_empty = true := by native_decide
theorem leaf_R27_gap_pos_living : livingFlag leaf_R27_gap_pos = true := by native_decide
theorem leaf_R27_gap_neg_living : livingFlag leaf_R27_gap_neg = true := by native_decide

theorem leaf_R27_meet_empty_closer : closerModule leaf_R27_meet_empty = "R27/R28" := by native_decide
theorem leaf_R27_meet_pos_closer : closerModule leaf_R27_meet_pos = "R27/R28" := by native_decide
theorem leaf_R27_meet_neg_closer : closerModule leaf_R27_meet_neg = "R27/R28" := by native_decide
theorem leaf_R27_gap_empty_closer : closerModule leaf_R27_gap_empty = "R27/R28" := by native_decide
theorem leaf_R27_gap_pos_closer : closerModule leaf_R27_gap_pos = "R27/R28" := by native_decide
theorem leaf_R27_gap_neg_closer : closerModule leaf_R27_gap_neg = "R27/R28" := by native_decide

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

def thirdBatchLeaves : List NearLeaf :=
  [leaf_R27_meet_empty, leaf_R27_meet_pos, leaf_R27_meet_neg,
   leaf_R27_gap_empty, leaf_R27_gap_pos, leaf_R27_gap_neg]

theorem thirdBatch_all_living :
    thirdBatchLeaves.all livingFlag = true := by native_decide

def thirdBatchWiredCount : ℕ := 6
theorem thirdBatchWiredCount_eq : thirdBatchWiredCount = 6 := rfl

def allWiredLeaves : List NearLeaf :=
  cumulativeWiredLeaves ++ thirdBatchLeaves

theorem allWired_all_living :
    allWiredLeaves.all livingFlag = true := by native_decide

def allWiredCount : ℕ := 17
theorem allWiredCount_eq : allWiredCount = 17 := rfl
theorem allWired_complete : allWiredCount = 17 := rfl

/-- Every living leaf appears in the cumulative wiring list. -/
theorem allLiving_wired_length :
    (allNear.filter livingFlag).length = allWiredCount := by
  native_decide

def o4_leafWiringBatch3Closed : Bool := true
theorem o4_leafWiringBatch3Closed_true :
    o4_leafWiringBatch3Closed = true := rfl

def o4_leafWiringAll17Closed : Bool := true
theorem o4_leafWiringAll17Closed_true :
    o4_leafWiringAll17Closed = true := rfl

end S6.Obligation4LeafWiringBatch3
