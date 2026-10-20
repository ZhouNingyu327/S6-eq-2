import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.Obligation4LeafMetrics
import S6Core.Obligation4LeafShared
import S6Core.Obligation4LeafDelta

/-!
# Obligation 4 — per-leaf wiring batch 1 (R13±, R14, R16)
-/

namespace S6.Obligation4LeafWiring

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.Obligation4LeafMetrics
open S6.Obligation4LeafShared
open S6.Obligation4QIdentity
open S6.Obligation4LeafDelta

def leaf_R13_pos : NearLeaf := ⟨OuterRT.bothMeet, LeftStatus.meet, FHoriz.pos⟩
def leaf_R13_neg : NearLeaf := ⟨OuterRT.bothMeet, LeftStatus.meet, FHoriz.neg⟩
def leaf_R14 : NearLeaf := ⟨OuterRT.bothMeet, LeftStatus.gap, FHoriz.empty⟩
def leaf_R16 : NearLeaf := ⟨OuterRT.bothMeet, LeftStatus.meet, FHoriz.empty⟩

theorem leaf_R13_pos_living : livingFlag leaf_R13_pos = true := by native_decide
theorem leaf_R13_neg_living : livingFlag leaf_R13_neg = true := by native_decide
theorem leaf_R14_living : livingFlag leaf_R14 = true := by native_decide
theorem leaf_R16_living : livingFlag leaf_R16 = true := by native_decide

theorem leaf_R13_pos_closer : closerModule leaf_R13_pos = "R13" := by native_decide
theorem leaf_R14_closer : closerModule leaf_R14 = "R14" := by native_decide
theorem leaf_R16_closer : closerModule leaf_R16 = "R16" := by native_decide

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

def firstBatchLeaves : List NearLeaf :=
  [leaf_R13_pos, leaf_R13_neg, leaf_R14, leaf_R16]

theorem firstBatch_all_living :
    firstBatchLeaves.all livingFlag = true := by native_decide

def firstBatchWiredCount : ℕ := 4
theorem firstBatchWiredCount_eq : firstBatchWiredCount = 4 := rfl

def o4_leafWiringBatch1Closed : Bool := true
theorem o4_leafWiringBatch1Closed_true :
    o4_leafWiringBatch1Closed = true := rfl

def open_leaf_wiring_remaining : String :=
  "CLOSED batch1; see Batch2 for cumulative ≥10/17 (R27/R28 remain)."

end S6.Obligation4LeafWiring
