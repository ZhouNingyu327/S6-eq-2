import Mathlib.Tactic
import S6Core.NearEndGeometry
import S6Core.Exhaustiveness
import S6Core.LeafCertificates

/-!
# Living-leaf closer discharge bridge

Packages the 8 named living closer modules into a single conditional
`AllNamedClosersDischarged` hypothesis that implies
`AllLivingLeavesExcluded` / `AllLivingClosersDischarged`.

Does **not** import MainTheorem / G5ExclusionFrag / AxisG5k0FromCover.
Does **not** claim any closer is unconditionally discharged.
≠ PrincipalClaim.
-/

namespace S6.LivingLeafCloserBridge

open S6.NearEndGeometry
open S6.Exhaustiveness
open S6.LeafCertificates

/-- Geometric discharge of every living leaf labelled by a closer module. -/
def CloserDischarged (label : String) : Prop :=
  ∀ ℓ : NearLeaf, living ℓ → closerModule ℓ = label → LivingLeafExcluded ℓ

/-- The eight living closer labels (inventory). -/
def livingCloserLabelSet : List String :=
  ["R13", "R14", "R16", "R17", "R18", "R19", "R26", "R27/R28"]

theorem livingCloserLabelSet_length : livingCloserLabelSet.length = 8 := by
  native_decide

/-- Every living leaf's closer is one of the eight named labels. -/
theorem living_closer_in_labelSet (ℓ : NearLeaf) (h : livingFlag ℓ = true) :
    closerModule ℓ ∈ livingCloserLabelSet := by
  revert h
  rcases ℓ with ⟨rt, left, fh⟩
  cases rt <;> cases left <;> cases fh <;> native_decide

/-- Conjunction of all eight closer discharges. -/
def AllNamedClosersDischarged : Prop :=
  CloserDischarged "R13" ∧
    CloserDischarged "R14" ∧
      CloserDischarged "R16" ∧
        CloserDischarged "R17" ∧
          CloserDischarged "R18" ∧
            CloserDischarged "R19" ∧
              CloserDischarged "R26" ∧
                CloserDischarged "R27/R28"

/-- Same shape as G1G2 `AllLivingClosersDischarged` (kept local to avoid MainTheorem). -/
def AllLivingClosersDischarged : Prop :=
  ∀ ℓ : NearLeaf, living ℓ → LivingLeafExcluded ℓ

/-- Case-split: named closer discharges ⇒ every living leaf excluded. -/
theorem AllLivingClosersDischarged_of_named (h : AllNamedClosersDischarged) :
    AllLivingClosersDischarged := by
  intro ℓ hl
  have hflag : livingFlag ℓ = true := hl
  have mem : closerModule ℓ ∈ livingCloserLabelSet := living_closer_in_labelSet ℓ hflag
  simp only [livingCloserLabelSet, List.mem_cons, List.mem_nil_iff, or_false] at mem
  rcases h with ⟨h13, h14, h16, h17, h18, h19, h26, h2728⟩
  rcases mem with hm | hm | hm | hm | hm | hm | hm | hm
  · exact h13 ℓ hl hm
  · exact h14 ℓ hl hm
  · exact h16 ℓ hl hm
  · exact h17 ℓ hl hm
  · exact h18 ℓ hl hm
  · exact h19 ℓ hl hm
  · exact h26 ℓ hl hm
  · exact h2728 ℓ hl hm

theorem AllLivingLeavesExcluded_of_namedClosers (h : AllNamedClosersDischarged) :
    AllLivingLeavesExcluded :=
  fun ℓ hl => AllLivingClosersDischarged_of_named h ℓ hl hl

/-- Per-leaf conditionals (R13 pair). -/
theorem LivingLeafExcluded_bothMeet_meet_pos_of_R13
    (h : CloserDischarged "R13") :
    LivingLeafExcluded ⟨.bothMeet, .meet, .pos⟩ := by
  intro hl
  have hc : closerModule ⟨.bothMeet, .meet, .pos⟩ = "R13" := by native_decide
  exact h _ hl hc hl

theorem LivingLeafExcluded_bothMeet_meet_neg_of_R13
    (h : CloserDischarged "R13") :
    LivingLeafExcluded ⟨.bothMeet, .meet, .neg⟩ := by
  intro hl
  have hc : closerModule ⟨.bothMeet, .meet, .neg⟩ = "R13" := by native_decide
  exact h _ hl hc hl

theorem LivingLeafExcluded_bothMeet_gap_empty_of_R14
    (h : CloserDischarged "R14") :
    LivingLeafExcluded ⟨.bothMeet, .gap, .empty⟩ := by
  intro hl
  have hc : closerModule ⟨.bothMeet, .gap, .empty⟩ = "R14" := by native_decide
  exact h _ hl hc hl

theorem LivingLeafExcluded_bothMeet_meet_empty_of_R16
    (h : CloserDischarged "R16") :
    LivingLeafExcluded ⟨.bothMeet, .meet, .empty⟩ := by
  intro hl
  have hc : closerModule ⟨.bothMeet, .meet, .empty⟩ = "R16" := by native_decide
  exact h _ hl hc hl

theorem LivingLeafExcluded_bothMeet_gap_neg_of_R17
    (h : CloserDischarged "R17") :
    LivingLeafExcluded ⟨.bothMeet, .gap, .neg⟩ := by
  intro hl
  have hc : closerModule ⟨.bothMeet, .gap, .neg⟩ = "R17" := by native_decide
  exact h _ hl hc hl

theorem LivingLeafExcluded_bothMeet_gap_pos_of_R18
    (h : CloserDischarged "R18") :
    LivingLeafExcluded ⟨.bothMeet, .gap, .pos⟩ := by
  intro hl
  have hc : closerModule ⟨.bothMeet, .gap, .pos⟩ = "R18" := by native_decide
  exact h _ hl hc hl

theorem LivingLeafExcluded_topGap_meet_empty_of_R26
    (h : CloserDischarged "R26") :
    LivingLeafExcluded ⟨.topGap, .meet, .empty⟩ := by
  intro hl
  have hc : closerModule ⟨.topGap, .meet, .empty⟩ = "R26" := by native_decide
  exact h _ hl hc hl

/-- All four R19 living leaves from one closer discharge. -/
theorem LivingLeafExcluded_R19_family_of_R19
    (h : CloserDischarged "R19") :
    LivingLeafExcluded ⟨.topGap, .gap, .empty⟩ ∧
      LivingLeafExcluded ⟨.topGap, .gap, .neg⟩ ∧
        LivingLeafExcluded ⟨.topGap, .meet, .pos⟩ ∧
          LivingLeafExcluded ⟨.topGap, .meet, .neg⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl

/-- All six rightGap living leaves from R27/R28 discharge. -/
theorem LivingLeafExcluded_rightGap_family_of_R27_28
    (h : CloserDischarged "R27/R28") :
    LivingLeafExcluded ⟨.rightGap, .meet, .empty⟩ ∧
      LivingLeafExcluded ⟨.rightGap, .meet, .pos⟩ ∧
        LivingLeafExcluded ⟨.rightGap, .meet, .neg⟩ ∧
          LivingLeafExcluded ⟨.rightGap, .gap, .empty⟩ ∧
            LivingLeafExcluded ⟨.rightGap, .gap, .pos⟩ ∧
              LivingLeafExcluded ⟨.rightGap, .gap, .neg⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl
  · intro hl; exact h _ hl (by native_decide) hl

theorem LivingLeafExcluded_rightGap_of_R27_28
    (h : CloserDischarged "R27/R28") (left : LeftStatus) (fh : FHoriz) :
    LivingLeafExcluded ⟨.rightGap, left, fh⟩ := by
  intro hl
  have hc : closerModule ⟨.rightGap, left, fh⟩ = "R27/R28" := by
    cases left <;> cases fh <;> native_decide
  exact h _ hl hc hl

/-- Residual closer count still open in Lean (geometry). -/
def openCloserDischargeCount : ℕ := 8
theorem openCloserDischargeCount_eq : openCloserDischargeCount = 8 := rfl

def namedClosersDischargedProved : Bool := false
theorem namedClosersDischargedProved_false :
    namedClosersDischargedProved = false := rfl

def allLivingClosersDischargedProved : Bool := false
theorem allLivingClosersDischargedProved_false :
    allLivingClosersDischargedProved = false := rfl

def openStatus : String :=
  "CLOSED: CloserDischarged packaging; named⇒AllLivingClosersDischarged; \
   per-leaf conditionals for R13–R19/R26/R27–28. \
   OPEN: inhabit CloserDischarged for each of 8 labels (geometry/certs). \
   Not PrincipalClaim."

end S6.LivingLeafCloserBridge
