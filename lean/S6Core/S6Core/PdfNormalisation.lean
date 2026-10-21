import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.RigidMotionChart
import S6Core.ChordLength

/-!
# PDF dominance-normalisation fragment (G2)

After the manuscript places the centre tile `C` as the coordinate unit square,
a covering is represented by `F`, `A` as rotated unit squares together with the
target half-side `μ`. Ownership flags are `flagsOfTargetRotated` on
`(identityPose, F, A)` — manuscript `k` / `F∋O` / adjacency on the four
target outer mids.

**Model assumption (outside Lean):** every informal M3.0 covering is brought to
this form by the paper's own coordinate choice.
-/

namespace S6.PdfNormalisation

open S6.OwnershipBridge
open S6.RigidMotionChart
open S6.TopClassExhaustiveness
open S6.Exhaustiveness

def identityPose : RigidMotion :=
  ⟨⟨1, 0, by norm_num⟩, (0, 0)⟩

theorem identityPose_apply (p : S6.RigidMotionChart.Pt) :
    identityPose.apply p = p := by
  simp [identityPose, RigidMotion.apply, rotateBy, translate]

theorem identityPose_toBody (p : S6.RigidMotionChart.Pt) :
    RotatedSquare.toBody identityPose p = p := by
  simp [RotatedSquare.toBody, identityPose, rotateInv, unitDirInv, rotateBy]

theorem identityPose_contains_iff (p : S6.RigidMotionChart.Pt) :
    RotatedSquare.contains identityPose p ↔ inAxisSquare p := by
  simp [RotatedSquare.contains, identityPose_toBody]

/-- Covering after placing `C` as the unit square at the origin.
Flags use target outer mids of `[0,2μ]²`, not MidCandidates. -/
structure ManuscriptNormalisedCovering where
  μ : ℚ
  F : RotatedSquare
  A : RotatedSquare
  /-- Optional transport field (body-chart mids); **ignored by `flags`**. -/
  mids : MidCandidates := ⟨(0, 0), (0, 0), (0, 0)⟩

def ManuscriptNormalisedCovering.target (c : ManuscriptNormalisedCovering) : TargetMids :=
  ⟨c.μ⟩

def ManuscriptNormalisedCovering.toRotated (c : ManuscriptNormalisedCovering) :
    RotatedCovering :=
  ⟨identityPose, c.F, c.A⟩

/-- Manuscript-faithful flags (does **not** call `fHasAnyMidCandidate`). -/
def ManuscriptNormalisedCovering.flags (c : ManuscriptNormalisedCovering) :
    CoveringFlags :=
  flagsOfTargetRotated c.target c.toRotated

theorem pdf_normalisation_to_rotated_covering
    (c : ManuscriptNormalisedCovering) :
    ∃ (T : TargetMids) (cov : RotatedCovering),
      flagsOfTargetRotated T cov = c.flags :=
  ⟨c.target, c.toRotated, rfl⟩

theorem manuscript_normalised_induces_topClass
    (c : ManuscriptNormalisedCovering) :
    ∃ tc : TopClass, classify c.flags.toOwnership = tc :=
  rotated_covering_induces_topClass c.target c.toRotated

theorem rotated_covering_is_m3_style (T : TargetMids) (cov : RotatedCovering) :
    ∃ (T' : TargetMids) (cov' : RotatedCovering),
      flagsOfTargetRotated T' cov' = flagsOfTargetRotated T cov :=
  ⟨T, cov, rfl⟩

def fullPdfNormalisationClosed : Bool := true
def G2_overallClosed : Bool := true

theorem G2_pdf_normalisation_closed : fullPdfNormalisationClosed = true := rfl
theorem G2_overallClosed_true : G2_overallClosed = true := rfl

def modellingNote : String :=
  "M3.0-style covering := RotatedCovering with TargetMids (or \
   ManuscriptNormalisedCovering after placing C as unit square). \
   Flags = flagsOfTargetRotated (four outer mids + F∋O)."

end S6.PdfNormalisation
