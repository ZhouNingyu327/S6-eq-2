import Mathlib.Tactic

/-!
# Prop-level exhaustiveness skeleton matching tables M3.0–M3.3

Finite near-end G2 table is machine-checked (`native_decide`).

Former Lean `axiom`s of type `True` / `→ True` are **discharged as theorems**
(they were vacuous placeholders). Real PDF-module obligations are recorded
as data in `residualObligations` — **not** as `axiom`s.
-/

namespace S6.Exhaustiveness

inductive TopClass
  | G1 | G2_centerMid | G2_farF | G3 | G4 | G5
  deriving DecidableEq, Repr

inductive OuterRT
  | bothMeet | topGap | rightGap | bothGap
  deriving DecidableEq, Repr

inductive LeftStatus
  | meet | gap
  deriving DecidableEq, Repr

inductive FHoriz
  | empty | pos | neg
  deriving DecidableEq, Repr

structure NearLeaf where
  rt : OuterRT
  left : LeftStatus
  fh : FHoriz
  deriving DecidableEq, Repr

def isImpossibleFlag : NearLeaf → Bool
  | ⟨OuterRT.bothGap, _, _⟩ => true
  | ⟨OuterRT.topGap, LeftStatus.gap, FHoriz.pos⟩ => true
  | _ => false

def livingFlag (ℓ : NearLeaf) : Bool := !(isImpossibleFlag ℓ)

def allNear : List NearLeaf :=
  [ ⟨.bothMeet, .meet, .empty⟩, ⟨.bothMeet, .meet, .pos⟩, ⟨.bothMeet, .meet, .neg⟩
  , ⟨.bothMeet, .gap,  .empty⟩, ⟨.bothMeet, .gap,  .pos⟩, ⟨.bothMeet, .gap,  .neg⟩
  , ⟨.topGap,   .meet, .empty⟩, ⟨.topGap,   .meet, .pos⟩, ⟨.topGap,   .meet, .neg⟩
  , ⟨.topGap,   .gap,  .empty⟩, ⟨.topGap,   .gap,  .pos⟩, ⟨.topGap,   .gap,  .neg⟩
  , ⟨.rightGap, .meet, .empty⟩, ⟨.rightGap, .meet, .pos⟩, ⟨.rightGap, .meet, .neg⟩
  , ⟨.rightGap, .gap,  .empty⟩, ⟨.rightGap, .gap,  .pos⟩, ⟨.rightGap, .gap,  .neg⟩
  , ⟨.bothGap,  .meet, .empty⟩, ⟨.bothGap,  .meet, .pos⟩, ⟨.bothGap,  .meet, .neg⟩
  , ⟨.bothGap,  .gap,  .empty⟩, ⟨.bothGap,  .gap,  .pos⟩, ⟨.bothGap,  .gap,  .neg⟩
  ]

theorem allNear_length : allNear.length = 24 := by native_decide
theorem count_impossible :
    (allNear.filter isImpossibleFlag).length = 7 := by native_decide
theorem count_living :
    (allNear.filter livingFlag).length = 17 := by native_decide
theorem filter_partition :
    (allNear.filter isImpossibleFlag).length +
      (allNear.filter livingFlag).length = allNear.length := by
  native_decide

def impossible (ℓ : NearLeaf) : Prop := isImpossibleFlag ℓ = true
def living (ℓ : NearLeaf) : Prop := livingFlag ℓ = true

theorem near_exhaustive (ℓ : NearLeaf) : living ℓ ∨ impossible ℓ := by
  simp only [living, impossible, livingFlag]
  cases isImpossibleFlag ℓ
  · left; rfl
  · right; rfl

/-! ## NON-PROOF placeholders (`→ True` / `True`)

These compile without `sorry` because the *goal* is propositional `True`,
not a covering exclusion. They must **not** be cited as geometric closure.
-/

/-- NON-PROOF: concludes `True`, not that a living leaf is geometrically excluded. -/
theorem near_end_leaves_closed : ∀ ℓ : NearLeaf, living ℓ → True :=
  fun _ _ => trivial

/-- NON-PROOF stubs. Boolean Ownership→TopClass tables live elsewhere; geometric
realisation / manuscript faithfulness remain open (see OwnershipBridge FIXMEs). -/
theorem top_class_exhaustive : True := trivial
theorem far_end_reduction_closed : True := trivial
theorem final_form_closed : True := trivial

structure S6Skeleton where
  near : ∀ ℓ : NearLeaf, living ℓ → True
  top : True
  far : True
  final : True

theorem skeleton : S6Skeleton :=
  ⟨near_end_leaves_closed, top_class_exhaustive, far_end_reduction_closed,
    final_form_closed⟩

/-- Residual **human-geometry / PDF** obligations (not Lean axioms). -/
structure ResidualObligation where
  name : String
  modules : String
  note : String

def residualObligations : List ResidualObligation :=
  [ ⟨"near_end_leaf_closures", "R13–R19,R26–R28 + LeafCertificates",
      "17/17 full cert registry; Lean closerModule map; PDF geometry not re-proved"⟩
  , ⟨"top_class_G1_G5", "TopClassExhaustiveness + OwnershipBridge + PdfNormalisation",
      "Axis+rotated+ManuscriptNormalisedCovering→flagsOfTargetRotated (manuscript k/F∋O); G2_overallClosed=true metadata"⟩
  , ⟨"far_end_reduction_M7", "R29–R39 / M7.1 + M7_1Geometry + g3 checklist",
      "SMT=0; G3_checklistClosed=true; G3_overallClosed=true (branch-logic/StandardForm fragment)"⟩
  , ⟨"final_form_M8_M11", "R40–R64 + m8 registry + dual-wrapper",
      "M8 registry wired; M9–M11 dual-wrapper PASS on main checkers after miss_certs; blocked: PDF geometry / Lean"⟩
  , ⟨"general_rotated_f_formula", "ChordLength + RigidMotionChart + ObliqueChart + EuclideanChord",
      "Width+z+algebra+incidence chord=f closed (G1_overallClosed=true)"⟩
  ]

theorem residualObligations_length :
    residualObligations.length = 5 := by native_decide

/-- Lean axiom count in this module: **0**. -/
def leanAxiomCount : ℕ := 0

end S6.Exhaustiveness
