import Mathlib.Tactic
import S6Core.Obligation2
import S6Core.Normalization
import S6Core.CoverageNondecrease
import S6Core.PdfNormalisation
import S6Core.OwnershipBridge
import S6Core.RigidMotionChart

/-!
# Obligation 2 — normalisation core (R2 Lemma 2 + SE(2) packaging + pipeline)

## 已证
* All six pairwise inequalities among corner owners
* Extra far-corner `distSq` facts (v2–v3, v2–v4, v3–v4)
* R2 Lemma 2 **1D projection domination**: `L≤0≤L+1`, `u≥0`, `u∈[L,L+1]` ⇒ `u∈[0,1]`
* Orthogonal interval ⇒ β-parameter with `0≤β≤1`
* `DominatedCornerForm` covers the origin; membership matches manuscript inequalities
* `pushLeft2` idempotent; normalised form is a fixed point of `pushLeft2`
* SE(2): rigid images preserve far-pair distances (transport of diameter obstruction)
* Conditional pipeline: `NormalisationWitness` ⇒ `ManuscriptNormalisedCovering`

## Opens 1–3: **已证** in `Obligation2Opens.lean`
* Residual blocking full flag: `open_roleSelection_and_mids_from_geometry`
* `obligation2_fullNormalisationClosed` remains `false`
-/

namespace S6.Obligation2Norm

open S6.Obligation2
open S6.Normalization
open S6.CoverageNondecrease
open S6.OwnershipBridge
open S6.RigidMotionChart
open S6.PdfNormalisation

/-! ## Far distances among the remaining corner pairs -/

theorem vert23_far (T : Target) :
    (2 : ℚ) < distSq (Target.v2 T) (Target.v3 T) := by
  simp only [distSq, Target.v2, Target.v3]; nlinarith [T.hμ]

theorem diag24_far (T : Target) :
    (2 : ℚ) < distSq (Target.v2 T) (Target.v4 T) := by
  simp only [distSq, Target.v2, Target.v4]; nlinarith [T.hμ]

theorem edge34_far (T : Target) :
    (2 : ℚ) < distSq (Target.v3 T) (Target.v4 T) := by
  simp only [distSq, Target.v3, Target.v4]; nlinarith [T.hμ]

theorem owners_i2_ne_i3 (T : Target) (C : CornerOwners T) : C.i2 ≠ C.i3 := by
  intro h
  exact cannot_cover_far (C.squares C.i2) _ _ (vert23_far T) C.h2
    (by simpa [congrArg C.squares h] using C.h3)

theorem owners_i2_ne_i4 (T : Target) (C : CornerOwners T) : C.i2 ≠ C.i4 := by
  intro h
  exact cannot_cover_far (C.squares C.i2) _ _ (diag24_far T) C.h2
    (by simpa [congrArg C.squares h] using C.h4)

theorem owners_i3_ne_i4 (T : Target) (C : CornerOwners T) : C.i3 ≠ C.i4 := by
  intro h
  exact cannot_cover_far (C.squares C.i3) _ _ (edge34_far T) C.h3
    (by simpa [congrArg C.squares h] using C.h4)

/-- All six pairwise inequalities among the four corner owners. -/
theorem owners_pairwise_distinct (T : Target) (C : CornerOwners T) :
    C.i1 ≠ C.i2 ∧ C.i1 ≠ C.i3 ∧ C.i1 ≠ C.i4 ∧
      C.i2 ≠ C.i3 ∧ C.i2 ≠ C.i4 ∧ C.i3 ≠ C.i4 :=
  ⟨owners_i1_ne_i2 T C, owners_i1_ne_i3 T C, owners_i1_ne_i4 T C,
    owners_i2_ne_i3 T C, owners_i2_ne_i4 T C, owners_i3_ne_i4 T C⟩

/-! ## R2 Lemma 2 — 1D projection domination -/

/-- Core of manuscript Lemma 2: replace strip `[L,L+1]` by `[0,1]` when the
strip contains the origin and the point lies in the closed half-line `u≥0`. -/
theorem dominate_projection (L u : ℚ)
    (hL : L ≤ (0 : ℚ)) (_hL1 : (0 : ℚ) ≤ L + 1)
    (hu : (0 : ℚ) ≤ u)
    (hcov : L ≤ u ∧ u ≤ L + 1) :
    (0 : ℚ) ≤ u ∧ u ≤ (1 : ℚ) := by
  refine ⟨hu, ?_⟩
  -- u ≤ L+1 ≤ 1 because L ≤ 0 ⇒ L+1 ≤ 1
  have hL1_le : L + 1 ≤ (1 : ℚ) := by linarith
  exact le_trans hcov.2 hL1_le

/-- Same statement in `covers1D` language; coincides with
`pushLeft_preserves_nonneg_coverage` when `L ≤ 0` (then `pushLeft L = 0`). -/
theorem dominate_projection_covers1D (L u : ℚ)
    (hL : L ≤ (0 : ℚ)) (hL1 : (0 : ℚ) ≤ L + 1)
    (hu : (0 : ℚ) ≤ u) (hcov : covers1D L u) :
    covers1D (0 : ℚ) u := by
  have h := dominate_projection L u hL hL1 hu hcov
  exact ⟨h.1, by simpa using h.2⟩

theorem dominate_eq_pushLeft_when_L_le_zero (L : ℚ) (hL : L ≤ 0) :
    pushLeft L = 0 := by
  simp only [pushLeft, max_eq_right hL]

/-- Orthogonal projection interval containing 0 is parameterized by β ∈ [0,1]. -/
theorem orthogonal_to_beta (M : ℚ)
    (hM0 : M ≤ (0 : ℚ)) (hM1 : (0 : ℚ) ≤ M + 1) :
    ∃ β : ℚ, 0 ≤ β ∧ β ≤ 1 ∧ M = -β ∧ M + 1 = 1 - β := by
  refine ⟨-M, ?_, ?_, by ring, by ring⟩
  · -- 0 ≤ -M  from M ≤ 0
    linarith
  · -- -M ≤ 1  from 0 ≤ M+1
    linarith

/-! ## Dominated corner form (manuscript inequalities) -/

/-- Manuscript form after Lemma 2: inward first-quadrant direction `(c,s)` and
orthogonal offset `β`. -/
structure DominatedCornerForm where
  c : ℚ
  s : ℚ
  β : ℚ
  hc0 : 0 ≤ c
  hs0 : 0 ≤ s
  hunit : c * c + s * s = 1
  hβ0 : 0 ≤ β
  hβ1 : β ≤ 1

def DominatedCornerForm.uCoord (D : DominatedCornerForm) (p : ℚ × ℚ) : ℚ :=
  D.c * p.1 + D.s * p.2

def DominatedCornerForm.vCoord (D : DominatedCornerForm) (p : ℚ × ℚ) : ℚ :=
  -D.s * p.1 + D.c * p.2

def DominatedCornerForm.covers (D : DominatedCornerForm) (p : ℚ × ℚ) : Prop :=
  let u := D.uCoord p
  let v := D.vCoord p
  0 ≤ u ∧ u ≤ 1 ∧ -D.β ≤ v ∧ v ≤ 1 - D.β

theorem DominatedCornerForm.covers_origin (D : DominatedCornerForm) :
    D.covers (0, 0) := by
  simp only [DominatedCornerForm.covers, DominatedCornerForm.uCoord,
    DominatedCornerForm.vCoord]
  refine ⟨by linarith, by norm_num, ?_, ?_⟩
  · -- -β ≤ 0
    linarith [D.hβ0]
  · -- 0 ≤ 1 - β
    linarith [D.hβ1]

/-- Building a dominated form from a first-quadrant unit direction and an
orthogonal strip containing the origin (Lemma 2 construction).
Assumes the radial strip has already been dominated to `[0,1]` (`L = 0`). -/
def dominatedOfStrip (c s M : ℚ)
    (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (hunit : c * c + s * s = 1)
    (hM : M ≤ 0) (hM1 : 0 ≤ M + 1) :
    DominatedCornerForm :=
  { c := c, s := s, β := -M
    hc0 := hc0, hs0 := hs0, hunit := hunit
    hβ0 := by linarith
    hβ1 := by linarith }

/-! ## pushLeft2 idempotence / no-cycle (M1 algebraic) -/

theorem pushLeft2_idempotent (s : AxisSquare2) :
    pushLeft2 (pushLeft2 s) = pushLeft2 s := by
  cases s with
  | mk x y =>
    simp only [pushLeft2]
    refine congrArg₂ AxisSquare2.mk ?_ ?_
    · exact pushLeft_idempotent x
    · exact pushLeft_idempotent y

/-- Already non-negative offsets are fixed points of `pushLeft2`. -/
theorem pushLeft2_fixed_of_nonneg (s : AxisSquare2)
    (hx : 0 ≤ s.x) (hy : 0 ≤ s.y) :
    pushLeft2 s = s := by
  cases s with
  | mk x y =>
    simp only [pushLeft2, pushLeft]
    refine congrArg₂ AxisSquare2.mk ?_ ?_
    · exact max_eq_left hx
    · exact max_eq_left hy

/-- Relating dominated axis-aligned form `(0, β')` style: after `pushLeft2`,
further normalisation is the identity (no reclassify cycle on the algebraic map). -/
theorem normalisation_map_no_cycle (s : AxisSquare2) :
    pushLeft2 (pushLeft2 s) = pushLeft2 s :=
  pushLeft2_idempotent s

/-! ## SE(2) packaging — rigid transport of diameter obstruction -/

theorem rigid_preserves_edge_far (T : Target) (m : RigidMotion) :
    (2 : ℚ) < distSq (m.apply (Target.v1 T)) (m.apply (Target.v2 T)) := by
  simpa [rigid_preserves_distSq] using edge_far T

theorem rigid_preserves_vert_far (T : Target) (m : RigidMotion) :
    (2 : ℚ) < distSq (m.apply (Target.v1 T)) (m.apply (Target.v4 T)) := by
  simpa [rigid_preserves_distSq] using vert_far T

theorem rigid_preserves_diag_far (T : Target) (m : RigidMotion) :
    (2 : ℚ) < distSq (m.apply (Target.v1 T)) (m.apply (Target.v3 T)) := by
  simpa [rigid_preserves_distSq] using diag_far T

/-- Conjugating a rotated square by a pure translation of its shift. -/
def translateSquare (t : ℚ × ℚ) (g : RotatedSquare) : RotatedSquare :=
  ⟨g.dir, translate t g.shift⟩

theorem translateSquare_apply (t : ℚ × ℚ) (g : RotatedSquare) (q : ℚ × ℚ) :
    (translateSquare t g).apply q = translate t (g.apply q) := by
  simp only [translateSquare, RigidMotion.apply, translate]
  apply Prod.ext <;> ring

/-- Translation conjugation preserves body membership of correspondingly
translated points. -/
theorem translateSquare_contains_iff (t : ℚ × ℚ) (g : RotatedSquare) (p : ℚ × ℚ) :
    RotatedSquare.contains (translateSquare t g) (translate t p) ↔
      RotatedSquare.contains g p := by
  simp only [RotatedSquare.contains, RotatedSquare.toBody, translateSquare,
    translate, rotateInv]
  -- toBody of translated square at translated point:
  -- rotateInv ( (p+t) - (shift+t) ) = rotateInv (p - shift)
  have h :
      ((p.1 + t.1) - (g.shift.1 + t.1), (p.2 + t.2) - (g.shift.2 + t.2)) =
        (p.1 - g.shift.1, p.2 - g.shift.2) := by
    apply Prod.ext <;> ring
  -- rewrite both toBody expressions
  change inAxisSquare (rotateInv g.dir
      ((p.1 + t.1) - (g.shift.1 + t.1), (p.2 + t.2) - (g.shift.2 + t.2))) ↔
    inAxisSquare (rotateInv g.dir (p.1 - g.shift.1, p.2 - g.shift.2))
  simp

/-! ## Six-square covering skeleton -/

/-- Six rotated unit squares over a target (area-cover hypothesis left open). -/
structure SixCovering (T : Target) where
  squares : Fin 6 → RotatedSquare

/-- Corner-owner existence from an explicit per-corner witness (no area measure). -/
def SixCovering.toCornerOwners (T : Target) (cov : SixCovering T)
    (i1 i2 i3 i4 : Fin 6)
    (h1 : RotatedSquare.contains (cov.squares i1) (Target.v1 T))
    (h2 : RotatedSquare.contains (cov.squares i2) (Target.v2 T))
    (h3 : RotatedSquare.contains (cov.squares i3) (Target.v3 T))
    (h4 : RotatedSquare.contains (cov.squares i4) (Target.v4 T)) :
    CornerOwners T :=
  ⟨cov.squares, i1, i2, i3, i4, h1, h2, h3, h4⟩

/-! ## Conditional pipeline → ManuscriptNormalisedCovering -/

/-- Witness that packages everything Lean can check once geometric placement
hypotheses are supplied (centre as `identityPose`, F/A the remaining free squares,
mids chosen). -/
structure NormalisationWitness (T : Target) where
  cov : SixCovering T
  owners : CornerOwners T
  hsq : owners.squares = cov.squares
  -- After SE(2)+relabel, some index is the centre block at identityPose
  iC : Fin 6
  hCentre : cov.squares iC = identityPose
  -- The two free blocks in the manuscript normal form
  F : RotatedSquare
  A : RotatedSquare
  mids : MidCandidates

/-- **Proved conditional:** a `NormalisationWitness` yields
`ManuscriptNormalisedCovering` (G2 Ownership fragment entry). -/
def NormalisationWitness.toManuscript {T : Target} (W : NormalisationWitness T) :
    ManuscriptNormalisedCovering :=
  ⟨T.μ, W.F, W.A, W.mids⟩

theorem NormalisationWitness_reaches_topClass (T : Target)
    (W : NormalisationWitness T) :
    ∃ tc : S6.Exhaustiveness.TopClass,
      S6.TopClassExhaustiveness.classify W.toManuscript.flags.toOwnership = tc :=
  manuscript_normalised_induces_topClass W.toManuscript

/-! ## Named open obligations (documentation strings; not axioms) -/

def open_firstQuadrantEdgeExists : String :=
  "Any rotated unit square containing a corner admits, in the inward local \
   frame, a first-quadrant edge direction (c,s ≥ 0, c²+s²=1). Euclidean \
   discrete choice among four edge normals; not yet a Lean existence proof."

def open_areaCover_yields_CornerOwners : String :=
  "A full area cover of T=[0,2μ]² by six unit squares yields CornerOwners \
   (each corner belongs to at least one square). Requires a Lean model of \
   closed-set covering, not only pointwise Fin 6 witnesses."

def open_centrePlacement_to_identityPose : String :=
  "After corner domination, some remaining square can be moved by SE(2) to \
   identityPose covering the centre O, leaving F and A as the other two. \
   Manuscript G2 normalisation step; packaging unfinished in Lean."

def open_full_existence_to_ManuscriptNormalisedCovering : String :=
  "Compose the three open steps above with proved dominate_projection / \
   owners_pairwise_distinct / NormalisationWitness.toManuscript to obtain \
   ∀ cover, ∃ ManuscriptNormalisedCovering. This is exactly \
   obligation2_fullNormalisationClosed."

/-- Sub-flags for this file (full normalisation still open). -/
def o2_pairwiseOwnersClosed : Bool := true
def o2_dominateProjectionClosed : Bool := true
def o2_pushLeftIdempotentClosed : Bool := true
def o2_se2DiameterTransportClosed : Bool := true
def o2_conditionalPipelineClosed : Bool := true
def o2_fullNormalisationClosed : Bool := false

theorem o2_pairwiseOwnersClosed_true : o2_pairwiseOwnersClosed = true := rfl
theorem o2_dominateProjectionClosed_true : o2_dominateProjectionClosed = true := rfl
theorem o2_pushLeftIdempotentClosed_true : o2_pushLeftIdempotentClosed = true := rfl
theorem o2_se2DiameterTransportClosed_true : o2_se2DiameterTransportClosed = true := rfl
theorem o2_conditionalPipelineClosed_true : o2_conditionalPipelineClosed = true := rfl
theorem o2_fullNormalisationClosed_false : o2_fullNormalisationClosed = false := rfl

end S6.Obligation2Norm
