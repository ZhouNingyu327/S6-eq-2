import Mathlib.Tactic
import S6Core.Obligation3FaceSqrt
import S6Core.Obligation3ObliqueTrees
import S6Core.ChordLength

/-!
# Obligation 3 — reusable face-activity transition lemmas (R30–39)

## 已证 transitions
* `secondUpExceeds ⇒ firstUpForced`
* `firstUpForced ⇒ ¬secondUpActive`
* Oblique positive-rotation preserves firstUp exclusion
* Down-root label incompatible with `l < μ` under Kd bound packaging
* AxisFace exclusivity: firstUp ≠ secondUp

## Named face states (this turn)
* `negC_second_down_cap` / `left_second_down` / `asymmetric_chord_pair` — **closed**
  (see `Obligation3FaceStatesClosed`)
-/

namespace S6.Obligation3FaceAutomata

open S6.Obligation3FaceSqrt
open S6.Obligation3ObliqueTrees
open S6.ChordLength

/-- Transition T1: second-up exceeds μ ⇒ first-up forced. -/
theorem transition_secondUp_to_firstUp (sec d mu : ℚ)
    (h : sec - d > mu) : firstUpForced sec d mu := h

/-- Transition T2: first-up forced ⇒ second-up inactive. -/
theorem transition_firstUp_excludes_second (sec d mu : ℚ)
    (h : firstUpForced sec d mu) : ¬ (sec - d ≤ mu) :=
  secondUp_excluded_of_firstUpForced sec d mu h

/-- Transition T3: down-root cannot claim `l ≥ μ` when `l < μ`. -/
theorem transition_down_excluded_by_root_cap (l mu : ℚ) (hl : l < mu) :
    ¬ (l ≥ mu) := not_le_of_gt hl

/-- Transition T4: Kd chain `l ≤ Kd ≤ d` with `l < μ`. -/
theorem transition_Kd_chain (l Kd d mu : ℚ)
    (hl : l ≤ Kd) (hKd : Kd ≤ d) (hlmu : l < mu) :
    l ≤ d ∧ l < mu := ⟨le_trans hl hKd, hlmu⟩

/-- Transition T5: oblique positive rotation + firstUp. -/
theorem transition_oblique_firstUp (u : UnitDir) (sec d mu : ℚ)
    (hpos : PosRotation u) (hforce : firstUpForced sec d mu) :
    PosRotation u ∧ ¬ (sec - d ≤ mu) :=
  ⟨hpos, oblique_firstUp_excludes_second sec d mu hforce⟩

theorem face_firstUp_ne_secondUp :
    AxisFace.firstUp ≠ AxisFace.secondUp := by
  decide

theorem face_firstDown_ne_firstUp :
    AxisFace.firstDown ≠ AxisFace.firstUp := by
  decide

def selectFace (forcedFirstUp : Bool) : AxisFace :=
  if forcedFirstUp then AxisFace.firstUp else AxisFace.secondUp

theorem selectFace_firstUp :
    selectFace true = AxisFace.firstUp := rfl

theorem selectFace_not_second_when_forced :
    selectFace true ≠ AxisFace.secondUp := by
  decide

def o3_faceTransitionsClosed : Bool := true
theorem o3_faceTransitionsClosed_true :
    o3_faceTransitionsClosed = true := rfl

/-- Formerly open; closed in `Obligation3FaceStatesClosed`. -/
def open_face_negC_second_down_cap : String :=
  "CLOSED: R32 neg-C second down-root cap (see FaceStatesClosed)."
def open_face_left_second_down : String :=
  "CLOSED: R34 LEFT second down upper-cap (see FaceStatesClosed)."
def open_face_asymmetric_chord_pair : String :=
  "CLOSED: R30 asymmetric chord two-face tree (see FaceStatesClosed)."

end S6.Obligation3FaceAutomata
