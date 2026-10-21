import Mathlib.Tactic
import S6Core.Obligation2
import S6Core.OwnershipBridge
import S6Core.BernsteinGridLift
import S6Core.GridContribution

/-!
# Rotated corner / CF bound fragments

* Algebraic `g2_alg < 2` on `(0,1/2)` (Weierstrass chart).
* Unit-square diameter `distSq ≤ 2` (re-export).
* Chord-measure corner ≤2 / CF export from `PointwiseCover` remains open.
-/

namespace S6.RotatedGridBound

open S6.Obligation2
open S6.OwnershipBridge
open S6.BernsteinGridLift
open S6.GridContribution

theorem corner_g2_alg_lt_two (t : ℚ) (ht0 : 0 < t) (ht : t < 1 / 2) :
    g2_alg t < 2 :=
  g2_alg_lt_two t ht0 ht

theorem rotated_unit_diameter (g : RotatedSquare) (p q : Pt)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q) :
    distSq p q ≤ 2 :=
  rotated_diameter g p q hp hq

def rotatedCornerOuterExportProved : Bool := false
theorem rotatedCornerOuterExportProved_false :
    rotatedCornerOuterExportProved = false := rfl

def rotatedCornerAlgebraicSpineClosed : Bool := true
theorem rotatedCornerAlgebraicSpineClosed_true :
    rotatedCornerAlgebraicSpineClosed = true := rfl

def openRotatedGeomExports : List String :=
  ["RotatedCornerOuterContribLeTwo (chord measure)",
   "RotatedCFBoundExport",
   "GridCoveredByCornersAndCF from PointwiseCover"]

end S6.RotatedGridBound
