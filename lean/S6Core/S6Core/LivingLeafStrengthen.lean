import Mathlib.Tactic
import S6Core.NearEndGeometry
import S6Core.Exhaustiveness
import S6Core.LeafCertificates

/-!
# LivingLeaf strengthenings (table + closer inventory)

Strengthens LivingLeaf / near-end inventory facts without touching
MainTheorem / G5ExclusionFrag / AxisG5k0FromCover.

Honest: table + closer map strengthenings ≠ geometric exclusion of the 17 living leaves
≠ PrincipalClaim unconditional.
-/

namespace S6.LivingLeafStrengthen

open S6.NearEndGeometry
open S6.Exhaustiveness
open S6.LeafCertificates

/-- Exact list of the 17 living near-end leaves. -/
theorem seventeen_living_list :
    (allNear.filter livingFlag) =
      [ ⟨.bothMeet, .meet, .empty⟩, ⟨.bothMeet, .meet, .pos⟩, ⟨.bothMeet, .meet, .neg⟩
      , ⟨.bothMeet, .gap,  .empty⟩, ⟨.bothMeet, .gap,  .pos⟩, ⟨.bothMeet, .gap,  .neg⟩
      , ⟨.topGap,   .meet, .empty⟩, ⟨.topGap,   .meet, .pos⟩, ⟨.topGap,   .meet, .neg⟩
      , ⟨.topGap,   .gap,  .empty⟩, ⟨.topGap,   .gap,  .neg⟩
      , ⟨.rightGap, .meet, .empty⟩, ⟨.rightGap, .meet, .pos⟩, ⟨.rightGap, .meet, .neg⟩
      , ⟨.rightGap, .gap,  .empty⟩, ⟨.rightGap, .gap,  .pos⟩, ⟨.rightGap, .gap,  .neg⟩ ] := by
  native_decide

/-- bothGap contributes 6 of the 7 table-impossible leaves. -/
theorem bothGap_impossible_count :
    (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.bothGap) && isImpossibleFlag ℓ)).length = 6 := by
  native_decide

/-- The unique non-bothGap impossible leaf is topGap/gap/pos. -/
theorem unique_topGap_impossible :
    (allNear.filter (fun ℓ => isImpossibleFlag ℓ && decide (ℓ.rt ≠ OuterRT.bothGap))) =
      [⟨OuterRT.topGap, LeftStatus.gap, FHoriz.pos⟩] := by
  native_decide

/-- Every rightGap leaf is living and closes under R27/R28. -/
theorem rightGap_all_living_closer_R27_28 :
    (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.rightGap))).all
      (fun ℓ => livingFlag ℓ && decide (closerModule ℓ = "R27/R28")) = true := by
  native_decide

/-- R13 closers: bothMeet/meet/{pos,neg}. -/
theorem r13_closer_leaves :
    closerModule ⟨.bothMeet, .meet, .pos⟩ = "R13" ∧
      closerModule ⟨.bothMeet, .meet, .neg⟩ = "R13" := by
  native_decide

/-- R26 closer: topGap/meet/empty. -/
theorem r26_closer_leaf :
    closerModule ⟨.topGap, .meet, .empty⟩ = "R26" := by
  native_decide

/-- Living leaves partition by closer-module label (inventory). -/
def livingCloserLabels : List String :=
  (allNear.filter livingFlag).map closerModule

theorem livingCloserLabels_length : livingCloserLabels.length = 17 := by
  native_decide

theorem livingCloserLabels_no_impossible :
    livingCloserLabels.all (fun s => decide (s ≠ "IMPOSSIBLE")) = true := by
  native_decide

/-- All 7 impossible leaves are LivingLeafExcluded (re-export). -/
theorem seven_impossible_LivingLeafExcluded :
    ∀ ℓ : NearLeaf, impossible ℓ → LivingLeafExcluded ℓ :=
  all_impossible_leaves_excluded

/-- Conditional packaging: cert-bridge ⇒ all living excluded (already in G1G2;
kept here without importing MainTheorem). -/
def LivingLeafCertBridge : Prop :=
  ∀ ℓ : NearLeaf, living ℓ → LivingLeafExcluded ℓ

theorem AllLivingLeavesExcluded_of_certBridge (h : LivingLeafCertBridge) :
    AllLivingLeavesExcluded :=
  fun ℓ hl => h ℓ hl hl

/-- Inventory: external exact family for near-end dual-solver steps is complete;
this Bool is status metadata, not geometry. -/
def nearEndExactInventoryComplete : Bool := true
theorem nearEndExactInventoryComplete_true :
    nearEndExactInventoryComplete = true := rfl

def livingLeafGeometryProvedInLean : Bool := false
theorem livingLeafGeometryProvedInLean_false :
    livingLeafGeometryProvedInLean = false := rfl

def livingLeafStrengthenClosed : Bool := true
theorem livingLeafStrengthenClosed_true : livingLeafStrengthenClosed = true := rfl

/-- Closer-module multiplicity on the 17 living leaves. -/
theorem closer_R13_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R13"))).length = 2 := by
  native_decide

theorem closer_R14_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R14"))).length = 1 := by
  native_decide

theorem closer_R16_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R16"))).length = 1 := by
  native_decide

theorem closer_R17_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R17"))).length = 1 := by
  native_decide

theorem closer_R18_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R18"))).length = 1 := by
  native_decide

theorem closer_R19_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R19"))).length = 4 := by
  native_decide

theorem closer_R26_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R26"))).length = 1 := by
  native_decide

theorem closer_R27_28_count :
    (allNear.filter livingFlag |>.filter (fun ℓ => decide (closerModule ℓ = "R27/R28"))).length = 6 := by
  native_decide

/-- Living closer counts sum to 17. -/
theorem closer_counts_sum_to_seventeen :
    2 + 1 + 1 + 1 + 1 + 4 + 1 + 6 = 17 := by native_decide

/-- bothMeet living leaves: 6. -/
theorem bothMeet_living_count :
    (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.bothMeet) && livingFlag ℓ)).length = 6 := by
  native_decide

/-- topGap living leaves: 5 (6 total topGap minus 1 impossible). -/
theorem topGap_living_count :
    (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.topGap) && livingFlag ℓ)).length = 5 := by
  native_decide

/-- rightGap living leaves: 6. -/
theorem rightGap_living_count :
    (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.rightGap) && livingFlag ℓ)).length = 6 := by
  native_decide

/-- No bothGap leaf is living. -/
theorem bothGap_none_living :
    (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.bothGap) && livingFlag ℓ)).length = 0 := by
  native_decide

/-- Explicit livingClosers membership for R13 pair leaves. -/
theorem livingClosers_R13_pair :
    (⟨.bothMeet, .meet, .pos⟩, "R13") ∈ livingClosers ∧
      (⟨.bothMeet, .meet, .neg⟩, "R13") ∈ livingClosers := by
  native_decide

theorem livingClosers_R26 :
    (⟨.topGap, .meet, .empty⟩, "R26") ∈ livingClosers := by
  native_decide

theorem livingClosers_R14 :
    (⟨.bothMeet, .gap, .empty⟩, "R14") ∈ livingClosers := by
  native_decide

/-- Living leaves partition by outer RT: 6+5+6. -/
theorem living_rt_partition :
    (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.bothMeet) && livingFlag ℓ)).length +
      (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.topGap) && livingFlag ℓ)).length +
        (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.rightGap) && livingFlag ℓ)).length = 17 := by
  native_decide

/-- Impossible leaves are exactly bothGap×6 + topGap/gap/pos. -/
theorem impossible_partition_shape :
    (allNear.filter isImpossibleFlag).length = 7 ∧
      (allNear.filter (fun ℓ => decide (ℓ.rt = OuterRT.bothGap))).length = 6 ∧
        isImpossibleFlag ⟨.topGap, .gap, .pos⟩ = true := by
  native_decide

def openStatus : String :=
  "CLOSED: living/impossible lists, closer labels, bothGap counts, R13–R28 closer multiplicities. \
   OPEN: geometric LivingLeafExcluded for each of the 17 living leaves. \
   Not PrincipalClaim."

end S6.LivingLeafStrengthen
