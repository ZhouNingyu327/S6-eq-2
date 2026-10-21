import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.Obligation2Roles
import S6Core.Obligation2Norm
import S6Core.PdfNormalisation
import S6Core.ClassificationExample
import S6Core.TopClassExhaustiveness
import S6Core.RigidMotionChart

/-!
# Manuscript ↔ Lean faithfulness (partial)

Machine-checked fragments of the Major-3 ownership / role API, plus an explicit
inventory of what remains open.

## Proved here / via imports
* Primary flags: four target outer mids; `fHasO` ⇔ `F` contains centre `O`.
* G5 classification from `fHasO` (axis + rotated).
* `RoleSelection` packaging inequalities `iC≠iF≠iA`; centre ≠ corner owners;
  `toManuscript` uses one `pullback` (`g⁻¹ ∘ f`).
* `ManuscriptNormalisedCovering.flags` ignores optional `mids` transport field.
* Classification regressions in `ClassificationExample` (rereview + G5/G1 below).

## Still open (stated; **not** proved in Lean)
* Every informal M3.0 covering in the long proof reduces, after the paper's
  coordinate choice, to data whose `flagsOfTargetRotated` /
  `RoleSelection.ofCover` Ownership record matches the manuscript.
* End-to-end geometric theorem \(S(6)=2\) in Lean.
* Metric leaf certificates inside Lean.

Boolean status flags elsewhere are human-maintained metadata — not proofs.
-/

namespace S6.Faithfulness

open S6.OwnershipBridge
open S6.Obligation2
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.Obligation2Norm
open S6.PdfNormalisation
open S6.TopClassExhaustiveness
open S6.Exhaustiveness
open S6.RigidMotionChart

/-! ## Flag API contracts -/

theorem flags_fHasO_iff_F_contains_O (T : TargetMids) (cov : Covering) :
    (flagsOfTarget T cov).fHasO = true ↔ cov.F.containsB T.O = true := by
  simp [flagsOfTarget, fContainsO]

theorem flags_rot_fHasO_iff_F_contains_O (T : TargetMids) (cov : RotatedCovering) :
    (flagsOfTargetRotated T cov).fHasO = true ↔ cov.F.containsB T.O = true := by
  simp [flagsOfTargetRotated, fContainsO_rot]

theorem manuscript_flags_ignore_mids_field
    (μ : ℚ) (F A : RotatedSquare) (m₁ m₂ : MidCandidates) :
    (⟨μ, F, A, m₁⟩ : ManuscriptNormalisedCovering).flags =
      (⟨μ, F, A, m₂⟩ : ManuscriptNormalisedCovering).flags :=
  rfl

theorem pullback_eq_comp_inverse (g f : RotatedSquare) :
    RotatedSquare.pullback g f = RigidMotion.comp (RigidMotion.inverse g) f :=
  rfl

/-! ## RoleSelection packaging -/

theorem roleSelection_distinct_roles {T : Target} (R : RoleSelection T) :
    R.iC ≠ R.iF ∧ R.iC ≠ R.iA ∧ R.iF ≠ R.iA :=
  ⟨R.hCF, R.hCA, R.hFA⟩

theorem roleSelection_centre_misses_corners {T : Target} (R : RoleSelection T) :
    R.iC ≠ R.owners.i1 ∧ R.iC ≠ R.owners.i2 ∧
      R.iC ≠ R.owners.i3 ∧ R.iC ≠ R.owners.i4 :=
  R.hC_ne_corners

/-- Sixth-tile existence among five excluded labels (used by `ofCover`). -/
theorem sixth_tile_exists (a b c d e : Fin 6) :
    ∃ i : Fin 6, i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ d ∧ i ≠ e :=
  exists_index_outside_five a b c d e

theorem ofCover_reaches_topClass {T : Target} (cov : PointwiseCover T) :
    ∃ tc : TopClass,
      classify (RoleSelection.ofCover cov).toManuscript.flags.toOwnership = tc :=
  RoleSelection_reaches_topClass (RoleSelection.ofCover cov)

/-! ## Extra classification regressions (axis-aligned) -/

/-- G5 sketch: `C = F = [0,1]²`, target μ = 11/10 so O = (11/10,11/10) ∉ C∪F —
wait: need F∋O. Use larger tiles covering the centre. -/
def μ₁ : ℚ := 11 / 10
def T₁ : TargetMids := ⟨μ₁⟩

/-- Axis squares covering O=(1.1,1.1): C = F = [0.6, 1.6]². -/
def C_g5 : AxisSquare := ⟨3 / 5, 3 / 5⟩
def F_g5 : AxisSquare := ⟨3 / 5, 3 / 5⟩
def A_g5 : AxisSquare := ⟨0, 0⟩
def cov_g5 : Covering := ⟨C_g5, F_g5, A_g5⟩
def flags_g5 : CoveringFlags := flagsOfTarget T₁ cov_g5

theorem g5_fHasO_true : flags_g5.fHasO = true := by native_decide

theorem g5_class : classify flags_g5.toOwnership = TopClass.G5 := by native_decide

/-- G1 sketch: C near centre but F far; no outer mid in C∪F.
C = [0.6,1.6]² contains O but no outer mid of [0,2.2]²;
F = [10,11]×[10,11] misses everything. -/
def C_g1 : AxisSquare := ⟨3 / 5, 3 / 5⟩
def F_g1 : AxisSquare := ⟨10, 10⟩
def cov_g1 : Covering := ⟨C_g1, F_g1, A_g5⟩
def flags_g1 : CoveringFlags := flagsOfTarget T₁ cov_g1

theorem g1_fHasO_false : flags_g1.fHasO = false := by native_decide

theorem g1_k_zero : flags_g1.k = ⟨0, by decide⟩ := by native_decide

theorem g1_class : classify flags_g1.toOwnership = TopClass.G1 := by native_decide

/-- Centre-G2 sketch: unique bottom mid in C, F misses O.
C = [0.6,1.6]×[-0.1,0.9] owns bottom mid (1.1,0); F far. -/
def C_g2c : AxisSquare := ⟨3 / 5, -1 / 10⟩
def F_g2c : AxisSquare := ⟨10, 10⟩
def cov_g2c : Covering := ⟨C_g2c, F_g2c, A_g5⟩
def flags_g2c : CoveringFlags := flagsOfTarget T₁ cov_g2c

theorem g2c_k_one : flags_g2c.k = ⟨1, by decide⟩ := by native_decide

theorem g2c_fHasO_false : flags_g2c.fHasO = false := by native_decide

theorem g2c_midInC_true : flags_g2c.midInC = true := by native_decide

theorem g2c_class : classify flags_g2c.toOwnership = TopClass.G2_centerMid := by
  native_decide

/-! ## Open end-to-end statement (documentation only) -/

/-- Informal Prop describing the missing faithfulness theorem.
Not proved; listed so status docs can cite a single anchor. -/
def endToEndFaithfulnessStatement : String :=
  "∀ informal M3.0 covering in long_proof, after paper coordinate choice, \
   ∃ (T : TargetMids) (cov : RotatedCovering), \
   manuscript Ownership flags = flagsOfTargetRotated T cov \
   (equivalently RoleSelection.ofCover on a PointwiseCover), with iF the \
   sixth tile and free blocks pulled by one pullback into the centre body chart."

def endToEndFaithfulnessProvedInLean : Bool := false

theorem endToEndFaithfulnessProvedInLean_false :
    endToEndFaithfulnessProvedInLean = false := rfl

/-- Partial Major-3 API fragments closed; full geometric faithfulness open. -/
def major3_apiFragmentsClosed : Bool := true
theorem major3_apiFragmentsClosed_true : major3_apiFragmentsClosed = true := rfl


/-! ## Additional role contracts (openai/math push) -/

theorem ofCover_owners_pairwise {T : Target} (cov : PointwiseCover T) :
    (RoleSelection.ofCover cov).owners.i1 ≠ (RoleSelection.ofCover cov).owners.i2 ∧
      (RoleSelection.ofCover cov).owners.i1 ≠ (RoleSelection.ofCover cov).owners.i3 ∧
        (RoleSelection.ofCover cov).owners.i1 ≠ (RoleSelection.ofCover cov).owners.i4 ∧
          (RoleSelection.ofCover cov).owners.i2 ≠ (RoleSelection.ofCover cov).owners.i3 ∧
            (RoleSelection.ofCover cov).owners.i2 ≠ (RoleSelection.ofCover cov).owners.i4 ∧
              (RoleSelection.ofCover cov).owners.i3 ≠ (RoleSelection.ofCover cov).owners.i4 :=
  owners_pairwise_distinct T (RoleSelection.ofCover cov).owners

theorem ofCover_iF_outside_five {T : Target} (cov : PointwiseCover T) :
    (RoleSelection.ofCover cov).iF ≠ (RoleSelection.ofCover cov).owners.i1 ∧
      (RoleSelection.ofCover cov).iF ≠ (RoleSelection.ofCover cov).owners.i2 ∧
        (RoleSelection.ofCover cov).iF ≠ (RoleSelection.ofCover cov).owners.i3 ∧
          (RoleSelection.ofCover cov).iF ≠ (RoleSelection.ofCover cov).owners.i4 ∧
            (RoleSelection.ofCover cov).iF ≠ (RoleSelection.ofCover cov).iC := by
  have hF := RoleSelection_F_ne_corners (RoleSelection.ofCover cov)
  exact ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2, Ne.symm (RoleSelection.ofCover cov).hCF⟩

theorem ofCover_roles_all_distinct {T : Target} (cov : PointwiseCover T) :
    (RoleSelection.ofCover cov).iC ≠ (RoleSelection.ofCover cov).iF ∧
      (RoleSelection.ofCover cov).iC ≠ (RoleSelection.ofCover cov).iA ∧
        (RoleSelection.ofCover cov).iF ≠ (RoleSelection.ofCover cov).iA :=
  roleSelection_distinct_roles (RoleSelection.ofCover cov)

end S6.Faithfulness
