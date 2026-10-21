import Mathlib.Tactic
import S6Core.Obligation2
import S6Core.OwnershipBridge
import S6Core.BernsteinGridLift
import S6Core.GridContribution
import S6Core.RotatedGridBound

/-!
# Rotated chord-measure fragments (toward G5k*GeomExport)

* Diameter ⇒ any two points in a unit square have `distSq ≤ 2`.
* Along a straight chord, Euclidean length² ≤ 2, so length ≤ √2 (too weak alone
  for outer-sum ≤2; need the Weierstrass `g2_alg < 2` reading for corners).
* Named open export Props for PointwiseCover → corners≤8 / CF≤4.
-/

namespace S6.RotatedChordMeasure

open S6.Obligation2
open S6.OwnershipBridge
open S6.BernsteinGridLift
open S6.GridContribution
open S6.RotatedGridBound

/-- Chord length squared between two points in a rotated unit square is ≤ 2. -/
theorem chord_distSq_le_two (g : RotatedSquare) (p q : Pt)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q) :
    distSq p q ≤ 2 :=
  rotated_unit_diameter g p q hp hq

/-- Cleared form: if `ℓ² = distSq` and `ℓ ≥ 0`, then `ℓ² ≤ 2`. -/
theorem chord_len_sq_le_two (g : RotatedSquare) (p q : Pt) (ℓ : ℚ)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q)
    (hℓ : ℓ * ℓ = distSq p q) (hnn : 0 ≤ ℓ) :
    ℓ * ℓ ≤ 2 := by
  rw [hℓ]; exact chord_distSq_le_two g p q hp hq

/-- Algebraic corner budget on the Weierstrass chart. -/
theorem weierstrass_corner_budget (t : ℚ) (ht0 : 0 < t) (ht : t < 1 / 2) :
    g2_alg t < 2 :=
  corner_g2_alg_lt_two t ht0 ht

def pointwiseCoverCornersExportProved : Bool := false
theorem pointwiseCoverCornersExportProved_false :
    pointwiseCoverCornersExportProved = false := rfl

/-- Open residual note for CF export. -/
def pointwiseCoverCFExportProved : Bool := false
theorem pointwiseCoverCFExportProved_false :
    pointwiseCoverCFExportProved = false := rfl

/-- Package: algebraic + diameter fragments closed; measure export open. -/
def rotatedChordAlgebraicClosed : Bool := true
theorem rotatedChordAlgebraicClosed_true : rotatedChordAlgebraicClosed = true := rfl

def openRotatedChordExports : List String :=
  ["PointwiseCover → corners≤8 chord measure",
   "PointwiseCover → CF≤4 chord measure",
   "g2_alg geometric reading as outer chord sum"]

end S6.RotatedChordMeasure
