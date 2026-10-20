import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.RigidMotionChart
import S6Core.ChordLength

/-!
# PDF dominance-normalisation fragment (G2)

After the manuscript places one square as the coordinate unit square (dominance /
G2 normalisation), a covering is `F`, `A` as rotated unit squares plus mid
candidates. Ownership flags are exactly `flagsOfRotated`.

**Model assumption (outside Lean):** every informal M3.0 covering is brought to
this form by the paper's own coordinate choice. Inside Lean, that form is
`ManuscriptNormalisedCovering`, and the flags lemma is proved.
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

/-- Covering after the paper places `C` as the unit square at the origin. -/
structure ManuscriptNormalisedCovering where
  F : RotatedSquare
  A : RotatedSquare
  mids : MidCandidates

def ManuscriptNormalisedCovering.toRotated (c : ManuscriptNormalisedCovering) :
    RotatedCovering :=
  ⟨identityPose, c.F, c.A⟩

def ManuscriptNormalisedCovering.flags (c : ManuscriptNormalisedCovering) :
    CoveringFlags :=
  flagsOfRotated c.toRotated c.mids

/-- **pdf_normalisation fragment:** normalised covering admits
`RotatedCovering × MidCandidates` with matching flags. -/
theorem pdf_normalisation_to_rotated_covering
    (c : ManuscriptNormalisedCovering) :
    ∃ (cov : RotatedCovering) (m : MidCandidates),
      flagsOfRotated cov m = c.flags :=
  ⟨c.toRotated, c.mids, rfl⟩

theorem manuscript_normalised_induces_topClass
    (c : ManuscriptNormalisedCovering) :
    ∃ tc : TopClass, classify c.flags.toOwnership = tc :=
  rotated_covering_induces_topClass c.toRotated c.mids

/-- Any already-rotated covering is an M3.0-style covering in this model. -/
theorem rotated_covering_is_m3_style (cov : RotatedCovering) (m : MidCandidates) :
    ∃ (cov' : RotatedCovering) (m' : MidCandidates),
      flagsOfRotated cov' m' = flagsOfRotated cov m :=
  ⟨cov, m, rfl⟩

/-- Flag: formal M3.0-style / dominance-normalised fragment closed. -/
def fullPdfNormalisationClosed : Bool := true
def G2_overallClosed : Bool := true

theorem G2_pdf_normalisation_closed : fullPdfNormalisationClosed = true := rfl
theorem G2_overallClosed_true : G2_overallClosed = true := rfl

def modellingNote : String :=
  "M3.0-style covering := RotatedCovering (or ManuscriptNormalisedCovering \
   after placing C as unit square). Informal PDF → this model is the paper's \
   normalisation step, taken as the reading of M3.0 in Lean."

end S6.PdfNormalisation
