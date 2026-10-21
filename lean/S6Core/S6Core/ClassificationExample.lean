import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.TopClassExhaustiveness
import S6Core.RigidMotionChart

/-!
# Rereview counterexample — manuscript vs legacy classifiers

Target `[0,11/5]²` (so `μ = 11/10`),
`C = [3/5,8/5]²`, `F = [3/5,8/5] × [-1/2,1/2]`.

Manuscript: only the bottom outer mid lies in `C ∪ F`, and `F` does not contain
the centre `O`, so `k = 1` and `fHasO = false`.

Legacy MidCandidates wiring (three standard mids, `fHasO` ← any mid in `F`)
gave `k = 0` and `fHasO = true`. The primary API must match the manuscript.
-/

namespace S6.ClassificationExample

open S6.OwnershipBridge
open S6.TopClassExhaustiveness
open S6.Exhaustiveness
open S6.RigidMotionChart

def μ₀ : ℚ := 11 / 10
def T₀ : TargetMids := ⟨μ₀⟩

def C₀ : AxisSquare := ⟨3 / 5, 3 / 5⟩
def F₀ : AxisSquare := ⟨3 / 5, -1 / 2⟩
def A₀ : AxisSquare := ⟨0, 0⟩  -- unused for flags

def cov₀ : Covering := ⟨C₀, F₀, A₀⟩

def flags₀ : CoveringFlags := flagsOfTarget T₀ cov₀

/-- Manuscript: unique owned outer mid is bottom; F does not contain O. -/
theorem rereview_k_eq_one : flags₀.k = ⟨1, by decide⟩ := by native_decide

theorem rereview_fHasO_false : flags₀.fHasO = false := by native_decide

theorem rereview_midInC_false : flags₀.midInC = false := by native_decide

theorem rereview_class_G2_farF :
    classify flags₀.toOwnership = TopClass.G2_farF := by native_decide

/-- Legacy wiring still exhibits the rereview mismatch (regression witness). -/
def legacyMids₀ : MidCandidates :=
  ⟨(μ₀, 0), (2 * μ₀, μ₀), (μ₀, 2 * μ₀)⟩

def legacyFlags₀ : CoveringFlags := legacyFlagsOf cov₀ legacyMids₀

theorem legacy_k_eq_zero : legacyFlags₀.k = ⟨0, by decide⟩ := by native_decide

theorem legacy_fHasO_true : legacyFlags₀.fHasO = true := by native_decide

/-- Same example via pure translations as rotated squares. -/
def cov₀_rot : RotatedCovering :=
  ⟨pureTranslation (C₀.x, C₀.y), pureTranslation (F₀.x, F₀.y),
    pureTranslation (A₀.x, A₀.y)⟩

def flags₀_rot : CoveringFlags := flagsOfTargetRotated T₀ cov₀_rot

theorem rereview_rot_k_eq_one : flags₀_rot.k = ⟨1, by decide⟩ := by native_decide

theorem rereview_rot_fHasO_false : flags₀_rot.fHasO = false := by native_decide

/-- Further G5 / G1 / centre-G2 regressions: `S6Core.Faithfulness`. -/
theorem rereview_legacy_mismatch :
    flags₀.k ≠ legacyFlags₀.k ∧ flags₀.fHasO ≠ legacyFlags₀.fHasO := by
  native_decide

end S6.ClassificationExample

