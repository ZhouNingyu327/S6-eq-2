import Mathlib.Tactic
import S6Core.AxisClassConstraints
import S6Core.CoveringGeometry
import S6Core.M7_1Geometry
import S6Core.MainTheorem
import S6Core.ParallelBudget
import S6Core.ParallelBudgetGeometry
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


/-! ## G3/G4 cover → flag extracts + BudgetHyp packaging -/

theorem G3_cover_k_eq_two {T : S6.Obligation2.Target}
    (cov : S6.Obligation2Opens.PointwiseCover T)
    (h : classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
      TopClass.G3) :
    (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.k = ⟨2, by decide⟩ :=
  (isG3Class_flags cov h).2.1

theorem G4_cover_k_eq_two {T : S6.Obligation2.Target}
    (cov : S6.Obligation2Opens.PointwiseCover T)
    (h : classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
      TopClass.G4) :
    (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.k = ⟨2, by decide⟩ :=
  (isG4Class_flags cov h).2.1

/-- Build `BudgetHyp` from rational witnesses (geometry supplies `B`,`vF`). -/
def BudgetHyp.of (μ B vF : ℚ) (hμ : 1 < μ) (hB : B < 1) (hv : vF < μ) : BudgetHyp :=
  ⟨μ, B, vF, hμ, hB, hv⟩

/-- Side-gap exclusion from exported `(B,vF)` + covering inequality at `T.μ`. -/
theorem G3Exclusion_of_exported_sideGap {T : S6.Obligation2.Target}
    (cov : S6.Obligation2Opens.PointwiseCover T)
    (_hcls :
      classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3)
    (B vF : ℚ) (hB : B < 1) (hv : vF < T.μ)
    (hp : (12 : ℚ) * T.μ ≤ 8 + 3 * B + vF) : False :=
  sideGap_impossible (BudgetHyp.of T.μ B vF T.hμ hB hv) hp

/-- Named residual: export `B<1`, `vF<μ`, and covering ineq from a G3 cover. -/
def G3SideGapDataExport : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      ∃ (B vF : ℚ), B < 1 ∧ vF < T.μ ∧ (12 : ℚ) * T.μ ≤ 8 + 3 * B + vF

theorem G3SideGapBudgetBridge_of_dataExport (h : G3SideGapDataExport) :
    G3SideGapBudgetBridge := by
  intro T cov hcls
  rcases h T cov hcls with ⟨B, vF, hB, hv, hp⟩
  exact ⟨BudgetHyp.of T.μ B vF T.hμ hB hv, hp⟩

theorem G3Exclusion_of_dataExport (h : G3SideGapDataExport) : G3Exclusion :=
  G3Exclusion_of_sideGapBudget (G3SideGapBudgetBridge_of_dataExport h)

def g3SideGapDataExportProved : Bool := false
theorem g3SideGapDataExportProved_false : g3SideGapDataExportProved = false := rfl

def g3BudgetHypBuilderClosed : Bool := true
theorem g3BudgetHypBuilderClosed_true : g3BudgetHypBuilderClosed = true := rfl


open S6.ParallelBudgetGeometry

/-- Export `ParallelBudgetData` + `vF` + cover ineq ⇒ `G3SideGapDataExport`. -/
def G3ParallelBudgetExport : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      ∃ (D : ParallelBudgetData) (vF : ℚ),
        vF < T.μ ∧ (12 : ℚ) * T.μ ≤ 8 + 3 * D.B + vF

theorem G3SideGapDataExport_of_parallelBudget (h : G3ParallelBudgetExport) :
    G3SideGapDataExport := by
  intro T cov hcls
  rcases h T cov hcls with ⟨D, vF, hv, hp⟩
  exact ⟨D.B, vF, D.B_lt_one, hv, hp⟩

theorem G3Exclusion_of_parallelBudgetExport (h : G3ParallelBudgetExport) : G3Exclusion :=
  G3Exclusion_of_dataExport (G3SideGapDataExport_of_parallelBudget h)

theorem sideGap_impossible_of_parallelBudget (μ : ℚ) (D : ParallelBudgetData) (vF : ℚ)
    (hμ : 1 < μ) (hv : vF < μ)
    (hp : (12 : ℚ) * μ ≤ 8 + 3 * D.B + vF) : False :=
  sideGap_impossible (BudgetHyp.of μ D.B vF hμ D.B_lt_one hv) hp

def g3ParallelBudgetExportProved : Bool := false
theorem g3ParallelBudgetExportProved_false : g3ParallelBudgetExportProved = false := rfl

def g3ParallelBudgetReductionClosed : Bool := true
theorem g3ParallelBudgetReductionClosed_true :
    g3ParallelBudgetReductionClosed = true := rfl


/-- Build `ParallelBudgetData` from separation witnesses. -/
def ParallelBudgetData.mk' (d y s : ℚ)
    (hd : 1 < d) (hy : 0 < y) (hy2 : y * y = d * d - 1)
    (hs : 0 < s) (hs2 : s * s = 2) (hd_le_s : d ≤ s) : ParallelBudgetData :=
  ⟨d, y, s, hd, hy, hy2, hs, hs2, hd_le_s⟩

/-- Separation witnesses `(d,y,s,vF)` from a G3 cover. -/
def G3SepWitnessExport : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      ∃ (d y s vF : ℚ) (hd : 1 < d) (hy : 0 < y) (hy2 : y * y = d * d - 1)
        (hs : 0 < s) (hs2 : s * s = 2) (hd_le : d ≤ s),
          vF < T.μ ∧
            (12 : ℚ) * T.μ ≤
              8 + 3 * (ParallelBudgetData.mk' d y s hd hy hy2 hs hs2 hd_le).B + vF

theorem G3ParallelBudgetExport_of_sepWitness (h : G3SepWitnessExport) :
    G3ParallelBudgetExport := by
  intro T cov hcls
  rcases h T cov hcls with ⟨d, y, s, vF, hd, hy, hy2, hs, hs2, hd_le, hv, hp⟩
  exact ⟨ParallelBudgetData.mk' d y s hd hy hy2 hs hs2 hd_le, vF, hv, hp⟩

theorem G3Exclusion_of_sepWitness (h : G3SepWitnessExport) :
    S6.MainTheorem.G3Exclusion :=
  G3Exclusion_of_parallelBudgetExport (G3ParallelBudgetExport_of_sepWitness h)

def g3SepWitnessExportProved : Bool := false
theorem g3SepWitnessExportProved_false : g3SepWitnessExportProved = false := rfl

def g3SepWitnessReductionClosed : Bool := true
theorem g3SepWitnessReductionClosed_true : g3SepWitnessReductionClosed = true := rfl


/-- Cap geometry: oriented square + triangular-cap cuts + budget data from a G3 cover. -/
def G3CapGeometryExport : Prop :=
  ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
    classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
        TopClass.G3 →
      ∃ (Q : OrientedUnitSquare) (H : TriangularCapCuts Q) (D : ParallelBudgetData) (vF : ℚ),
        D.d = H.d ∧ vF < T.μ ∧ (12 : ℚ) * T.μ ≤ 8 + 3 * D.B + vF

theorem G3ParallelBudgetExport_of_capGeometry (h : G3CapGeometryExport) :
    G3ParallelBudgetExport := by
  intro T cov hcls
  rcases h T cov hcls with ⟨_, _, D, vF, _, hv, hp⟩
  exact ⟨D, vF, hv, hp⟩

theorem G3Exclusion_of_capGeometry (h : G3CapGeometryExport) :
    S6.MainTheorem.G3Exclusion :=
  G3Exclusion_of_parallelBudgetExport (G3ParallelBudgetExport_of_capGeometry h)

/-- Build `ParallelBudgetData` from a triangular-cap cut + `(y,s)` witnesses. -/
def ParallelBudgetData_of_cap (Q : OrientedUnitSquare) (H : TriangularCapCuts Q)
    (y s : ℚ) (hy : 0 < y) (hy2 : y * y = H.d * H.d - 1)
    (hs : 0 < s) (hs2 : s * s = 2) (hd_le : H.d ≤ s) : ParallelBudgetData :=
  ParallelBudgetData.mk' H.d y s H.hd hy hy2 hs hs2 hd_le

theorem ParallelBudgetData_of_cap_B_lt_one (Q : OrientedUnitSquare) (H : TriangularCapCuts Q)
    (y s : ℚ) (hy : 0 < y) (hy2 : y * y = H.d * H.d - 1)
    (hs : 0 < s) (hs2 : s * s = 2) (hd_le : H.d ≤ s) :
    (ParallelBudgetData_of_cap Q H y s hy hy2 hs hs2 hd_le).B < 1 :=
  (ParallelBudgetData_of_cap Q H y s hy hy2 hs hs2 hd_le).B_lt_one

/-- Cap + separation witnesses ⇒ `G3SepWitnessExport`. -/
theorem G3SepWitnessExport_of_capSep
    (H : ∀ (T : S6.Obligation2.Target) (cov : S6.Obligation2Opens.PointwiseCover T),
      classify (S6.Obligation2Roles.RoleSelection.ofCover cov).toManuscript.flags.toOwnership =
          TopClass.G3 →
        ∃ (Q : OrientedUnitSquare) (Hc : TriangularCapCuts Q) (y s vF : ℚ)
          (hy : 0 < y) (hy2 : y * y = Hc.d * Hc.d - 1)
          (hs : 0 < s) (hs2 : s * s = 2) (hd_le : Hc.d ≤ s),
            vF < T.μ ∧
              (12 : ℚ) * T.μ ≤
                8 + 3 * (ParallelBudgetData_of_cap Q Hc y s hy hy2 hs hs2 hd_le).B + vF) :
    G3SepWitnessExport := by
  intro T cov hcls
  rcases H T cov hcls with ⟨Q, Hc, y, s, vF, hy, hy2, hs, hs2, hd_le, hv, hp⟩
  refine ⟨Hc.d, y, s, vF, Hc.hd, hy, hy2, hs, hs2, hd_le, hv, ?_⟩
  simpa [ParallelBudgetData.mk', ParallelBudgetData_of_cap] using hp

def g3CapGeometryExportProved : Bool := false
theorem g3CapGeometryExportProved_false : g3CapGeometryExportProved = false := rfl

def g3CapGeometryReductionClosed : Bool := true
theorem g3CapGeometryReductionClosed_true : g3CapGeometryReductionClosed = true := rfl

end S6.G3G4Fragments
