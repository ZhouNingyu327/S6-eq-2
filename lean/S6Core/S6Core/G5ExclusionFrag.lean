import Mathlib.Tactic
import S6Core.G5Budget
import S6Core.ParallelBudget
import S6Core.G5Fragments
import S6Core.CoveringGeometry
import S6Core.MainTheorem
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.TopClassExhaustiveness
import S6Core.Exhaustiveness
import S6Core.OwnershipBridge

/-!
# G5 exclusion fragments (R2–R8 algebraic spine)

* If a G5 cover realises R2 grid-budget hypotheses, it is impossible (proved).
* Conditional: `G5Exclusion` follows from three geometric bridge Props.
* Full unconditional `G5Exclusion` remains open.
-/

namespace S6.G5ExclusionFrag

open S6.G5Budget
open S6.ParallelBudget
open S6.G5Fragments
open S6.CoveringGeometry
open S6.MainTheorem
open S6.Obligation2
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.TopClassExhaustiveness
open S6.Exhaustiveness
open S6.OwnershipBridge

def isG5Class {T : Target} (cov : PointwiseCover T) : Prop :=
  classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership = TopClass.G5

theorem isG5_of_fHasO_axis (T : TargetMids) (cov : Covering)
    (h : (flagsOfTarget T cov).fHasO = true) :
    classify (flagsOfTarget T cov).toOwnership = TopClass.G5 :=
  covering_G5_of_fHasO T cov h

/-! ## Open geometric bridges -/

def G5k2Bridge : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨2, by decide⟩ →
        Nonempty G5OppositeMidHyp ∨
          Nonempty G5AdjacentMidHyp ∨
            Nonempty G5GridHyp

def G5k0Bridge : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        Nonempty G5GridHyp

def G5k1Bridge : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨1, by decide⟩ →
        (∃ h : S6.ParallelBudget.BudgetHyp, (12 : ℚ) * h.μ ≤ 8 + 3 * h.B + h.vF) ∨
          (∃ (B : ℚ), B < 1 ∧
            (12 : ℚ) * T.μ ≤ 8 + 2 * B + 2 * T.μ) ∨
            Nonempty G5OppositeMidHyp

/-! ## Algebraic discharge -/

theorem discharge_k2
    (h : Nonempty G5OppositeMidHyp ∨ Nonempty G5AdjacentMidHyp ∨ Nonempty G5GridHyp) :
    False := by
  rcases h with h | h | h
  · exact h.elim fun H => H.impossible
  · exact h.elim fun H => H.impossible
  · exact h.elim fun H => H.impossible

theorem discharge_k0 (h : Nonempty G5GridHyp) : False :=
  h.elim fun H => H.impossible

theorem discharge_k1 {T : Target}
    (h : (∃ hyp : S6.ParallelBudget.BudgetHyp,
            (12 : ℚ) * hyp.μ ≤ 8 + 3 * hyp.B + hyp.vF) ∨
      (∃ (B : ℚ), B < 1 ∧ (12 : ℚ) * T.μ ≤ 8 + 2 * B + 2 * T.μ) ∨
        Nonempty G5OppositeMidHyp) : False := by
  rcases h with h | h | h
  · rcases h with ⟨hyp, hp⟩; exact sideGap_impossible hyp hp
  · rcases h with ⟨B, hB, hp⟩; exact noSideGap_impossible T.μ B T.hμ hB hp
  · exact h.elim fun H => H.impossible

/-- Fin 3 is only 0,1,2. -/
theorem k_trichotomy (k : Fin 3) :
    k = ⟨0, by decide⟩ ∨ k = ⟨1, by decide⟩ ∨ k = ⟨2, by decide⟩ := by
  match k with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)

/-- Conditional G5Exclusion from the three bridges. -/
theorem G5Exclusion_of_bridges
    (hk2 : G5k2Bridge) (hk0 : G5k0Bridge) (hk1 : G5k1Bridge) :
    G5Exclusion := by
  intro T cov hcls
  have hG5 : isG5Class cov := hcls
  set fl := (RoleSelection.ofCover cov).toManuscript.flags
  rcases k_trichotomy fl.k with hk | hk | hk
  · exact discharge_k0 (hk0 T cov hG5 hk)
  · exact discharge_k1 (hk1 T cov hG5 hk)
  · exact discharge_k2 (hk2 T cov hG5 hk)

theorem g5_centre_misses_mids_large_mu {T : Target} (g : RotatedSquare)
    (hμ2 : (2 : ℚ) < T.μ * T.μ)
    (hc : RotatedSquare.contains g (Target.centre T)) :
    ¬ RotatedSquare.contains g (midBottom T) ∧
      ¬ RotatedSquare.contains g (midRight T) ∧
        ¬ RotatedSquare.contains g (midTop T) ∧
          ¬ RotatedSquare.contains g (midLeft T) :=
  centre_owner_misses_all_outer_mids_of_mu_sq T g hμ2 hc

def g5AlgebraicSpineClosed : Bool := true
theorem g5AlgebraicSpineClosed_true : g5AlgebraicSpineClosed = true := rfl

def g5BridgesProvedInLean : Bool := false
theorem g5BridgesProvedInLean_false : g5BridgesProvedInLean = false := rfl

def openG5Bridges : List String :=
  ["G5k2Bridge", "G5k0Bridge", "G5k1Bridge"]

end S6.G5ExclusionFrag
