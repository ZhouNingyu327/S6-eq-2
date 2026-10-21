import Mathlib.Tactic
import S6Core.AxisClassConstraints
import S6Core.CoveringGeometry
import S6Core.M7_1Geometry
import S6Core.MainTheorem
import S6Core.ParallelBudget
import S6Core.G5Budget
import S6Core.OwnershipBridge
open S6.TopClassExhaustiveness
open S6.Exhaustiveness

/-!
# G3/G4 fragments — mid-split + M7.1 interface

* Axis `k=2` forces C/F mid split (`AxisClassConstraints`).
* M7.1 far-end / topGap checker equivalences already in `M7_1Geometry`.
* Conditional `G3Exclusion` / `G4Exclusion` from named bridges.
-/

namespace S6.G3G4Fragments

open S6.AxisClassConstraints
open S6.CoveringGeometry
open S6.M7_1Geometry
open S6.MainTheorem
open S6.OwnershipBridge

/-- k=2 + bottom/right owned ⇒ cannot both sit in C (axis). -/
theorem k2_bottom_right_not_both_C (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.C.contains T.midBottom) (hr : cov.C.contains T.midRight) : False :=
  not_both_in_C_bottom_right T cov hμ hb hr

theorem k2_bottom_right_not_both_F (T : TargetMids) (cov : Covering) (hμ : 1 < T.μ)
    (hb : cov.F.contains T.midBottom) (hr : cov.F.contains T.midRight) : False :=
  not_both_in_F_bottom_right T cov hμ hb hr

/-- G3 = k=2, not adjacent; G4 = k=2, adjacent (classifier). -/
theorem classify_G3_of_k2_not_adj (o : Ownership)
    (hf : o.fHasO = false) (hk : o.k = ⟨2, by decide⟩) (ha : o.midsAdjacent = false) :
    classify o = TopClass.G3 :=
  classify_G3_of o hf hk ha

theorem classify_G4_of_k2_adj (o : Ownership)
    (hf : o.fHasO = false) (hk : o.k = ⟨2, by decide⟩) (ha : o.midsAdjacent = true) :
    classify o = TopClass.G4 :=
  classify_G4_of o hf hk ha

/-- M7.1 topGap narrative ↔ checker (already proved; re-export). -/
theorem m71_topGap_equiv (n : NarrativeTopGap) (hw : NarrativeTopGap.wellFormed n) :
    CheckerTopGapPre.valid n.remaining.toChecker ∧
      CheckerTopGapPre.toOuter n.remaining.toChecker = n.remaining :=
  topGap_narrative_iff_checker n hw

/-- Open bridges: G3/G4 covers realise a discharged M7.1 / budget leaf. -/
def G3Bridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 → False

def G4Bridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G4 → False

/-- If the G3/G4 bridges are the exclusions themselves (identity packaging). -/
theorem G3Exclusion_of_bridge (h : G3Bridge) : G3Exclusion := h
theorem G4Exclusion_of_bridge (h : G4Bridge) : G4Exclusion := h

/-- Far-end host validity (M7.1 entry). -/
theorem farEnd_default_valid : FarEndHosts.valid {} := FarEndHosts.default_valid

def g3g4MidSplitClosed : Bool := true
theorem g3g4MidSplitClosed_true : g3g4MidSplitClosed = true := rfl

def g3g4BridgesProvedInLean : Bool := false
theorem g3g4BridgesProvedInLean_false : g3g4BridgesProvedInLean = false := rfl


open S6.ParallelBudget
open S6.G5Budget

/-- Finer G3 bridge: a G3 cover realises a side-gap `BudgetHyp` covering ineq. -/
def G3SideGapBudgetBridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      ∃ hyp : BudgetHyp, (12 : ℚ) * hyp.μ ≤ 8 + 3 * hyp.B + hyp.vF

/-- Finer G4 bridge: a G4 cover realises no-side-gap or opposite-mid budget. -/
def G4BudgetBridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G4 →
      (∃ (B : ℚ), B < 1 ∧ (12 : ℚ) * T.μ ≤ 8 + 2 * B + 2 * T.μ) ∨
        Nonempty G5OppositeMidHyp

theorem G3Exclusion_of_sideGapBudget (h : G3SideGapBudgetBridge) : G3Exclusion := by
  intro T cov hcls
  rcases h T cov hcls with ⟨hyp, hp⟩
  exact sideGap_impossible hyp hp

theorem G4Exclusion_of_budget (h : G4BudgetBridge) : G4Exclusion := by
  intro T cov hcls
  rcases h T cov hcls with hB | hOpp
  · rcases hB with ⟨B, hBlt, hp⟩
    exact noSideGap_impossible T.μ B T.hμ hBlt hp
  · exact hOpp.elim fun H => H.impossible

/-- M7.1 right-gap narrative + BudgetHyp covering ⇒ False (algebraic step). -/
theorem m71_sideGap_budget_impossible (hyp : BudgetHyp)
    (hp : (12 : ℚ) * hyp.μ ≤ 8 + 3 * hyp.B + hyp.vF) : False :=
  sideGap_impossible hyp hp

/-- M7.1 no-side-gap algebraic discharge. -/
theorem m71_noSideGap_budget_impossible (μ B : ℚ) (hμ : 1 < μ) (hB : B < 1)
    (hp : (12 : ℚ) * μ ≤ 8 + 2 * B + 2 * μ) : False :=
  noSideGap_impossible μ B hμ hB hp

def g3g4BudgetReductionClosed : Bool := true
theorem g3g4BudgetReductionClosed_true : g3g4BudgetReductionClosed = true := rfl

def openG3G4BudgetBridges : List String :=
  ["G3SideGapBudgetBridge", "G4BudgetBridge"]


/-- G3 exclusion from side-gap OR no-side-gap budget export. -/
def G3EitherBudgetBridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      (∃ hyp : BudgetHyp, (12 : ℚ) * hyp.μ ≤ 8 + 3 * hyp.B + hyp.vF) ∨
        (∃ (B : ℚ), B < 1 ∧ (12 : ℚ) * T.μ ≤ 8 + 2 * B + 2 * T.μ)

theorem G3Exclusion_of_either_budget (h : G3EitherBudgetBridge) : G3Exclusion := by
  intro T cov hcls
  rcases h T cov hcls with h1 | h2
  · rcases h1 with ⟨hyp, hp⟩; exact sideGap_impossible hyp hp
  · rcases h2 with ⟨B, hB, hp⟩; exact noSideGap_impossible T.μ B T.hμ hB hp

def g3EitherBudgetReductionClosed : Bool := true
theorem g3EitherBudgetReductionClosed_true : g3EitherBudgetReductionClosed = true := rfl


/-- Package: G3 cover realises either side-gap BudgetHyp or opposite-mid hyp. -/
def G3SideOrOppBridge : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      (∃ hyp : BudgetHyp, (12 : ℚ) * hyp.μ ≤ 8 + 3 * hyp.B + hyp.vF) ∨
        Nonempty G5OppositeMidHyp

theorem G3Exclusion_of_sideOrOpp (h : G3SideOrOppBridge) : G3Exclusion := by
  intro T cov hcls
  rcases h T cov hcls with h1 | h2
  · rcases h1 with ⟨hyp, hp⟩; exact sideGap_impossible hyp hp
  · exact h2.elim fun H => H.impossible

def g3SideOrOppReductionClosed : Bool := true
theorem g3SideOrOppReductionClosed_true : g3SideOrOppReductionClosed = true := rfl


/-- On the finite Ownership grid, G3 ⇒ k=2 ∧ ¬fHasO ∧ ¬adjacent (machine-checked). -/
theorem G3_implies_k2_on_grid :
    allOwnership.all
      (fun o => decide (classify o = TopClass.G3 →
        o.fHasO = false ∧ o.k = ⟨2, by decide⟩ ∧ o.midsAdjacent = false)) = true := by
  native_decide

theorem G4_implies_k2_adj_on_grid :
    allOwnership.all
      (fun o => decide (classify o = TopClass.G4 →
        o.fHasO = false ∧ o.k = ⟨2, by decide⟩ ∧ o.midsAdjacent = true)) = true := by
  native_decide

/-- Named open: a G3 PointwiseCover realises a side-gap BudgetHyp at T.μ. -/
def G3CoverBudgetRealisation : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      ∃ (B vF : ℚ), ∃ hyp : BudgetHyp,
        hyp.μ = T.μ ∧ hyp.B = B ∧ hyp.vF = vF ∧
          (12 : ℚ) * hyp.μ ≤ 8 + 3 * hyp.B + hyp.vF

theorem G3Exclusion_of_coverBudgetRealisation (h : G3CoverBudgetRealisation) :
    G3Exclusion := by
  intro T cov hcls
  rcases h T cov hcls with ⟨B, vF, hyp, _, _, _, hp⟩
  exact sideGap_impossible hyp hp

def g3CoverBudgetRealisationProved : Bool := false
theorem g3CoverBudgetRealisationProved_false :
    g3CoverBudgetRealisationProved = false := rfl


/-! ## G3/G4 flag characterisation (Ownership grid → Prop) -/

theorem classify_eq_G3_iff (o : Ownership) :
    classify o = TopClass.G3 ↔
      o.fHasO = false ∧ o.k = ⟨2, by decide⟩ ∧ o.midsAdjacent = false := by
  constructor
  · intro h
    cases hf : o.fHasO
    · simp [classify, hf] at h
      match o.k, h with
      | ⟨0, _⟩, h => cases h
      | ⟨1, _⟩, h => revert h; cases o.midInC <;> intro h <;> cases h
      | ⟨2, _⟩, h =>
        cases ha : o.midsAdjacent
        · refine ⟨rfl, rfl, rfl⟩
        · simp [ha] at h
    · simp [classify, hf] at h
  · intro ⟨hf, hk, ha⟩
    exact classify_G3_of o hf hk ha

theorem classify_eq_G4_iff (o : Ownership) :
    classify o = TopClass.G4 ↔
      o.fHasO = false ∧ o.k = ⟨2, by decide⟩ ∧ o.midsAdjacent = true := by
  constructor
  · intro h
    cases hf : o.fHasO
    · simp [classify, hf] at h
      match o.k, h with
      | ⟨0, _⟩, h => cases h
      | ⟨1, _⟩, h => revert h; cases o.midInC <;> intro h <;> cases h
      | ⟨2, _⟩, h =>
        cases ha : o.midsAdjacent
        · simp [ha] at h
        · exact ⟨rfl, rfl, rfl⟩
    · simp [classify, hf] at h
  · intro ⟨hf, hk, ha⟩
    exact classify_G4_of o hf hk ha

theorem isG3Class_flags {T : S6.Obligation2.Target}
    (cov : S6.Obligation2Opens.PointwiseCover T)
    (h : classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
      TopClass.G3) :
    let o := (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership
    o.fHasO = false ∧ o.k = ⟨2, by decide⟩ ∧ o.midsAdjacent = false :=
  (classify_eq_G3_iff _).1 h

theorem isG4Class_flags {T : S6.Obligation2.Target}
    (cov : S6.Obligation2Opens.PointwiseCover T)
    (h : classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
      TopClass.G4) :
    let o := (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership
    o.fHasO = false ∧ o.k = ⟨2, by decide⟩ ∧ o.midsAdjacent = true :=
  (classify_eq_G4_iff _).1 h

def g3g4FlagIffClosed : Bool := true
theorem g3g4FlagIffClosed_true : g3g4FlagIffClosed = true := rfl

end S6.G3G4Fragments
