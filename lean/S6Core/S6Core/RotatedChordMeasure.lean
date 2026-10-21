import Mathlib.Tactic
import S6Core.Obligation2
import S6Core.Obligation2Opens
import S6Core.Obligation2Roles
import S6Core.OwnershipBridge
import S6Core.BernsteinGridLift
import S6Core.GridContribution
import S6Core.RotatedGridBound
import S6Core.G5Budget
import S6Core.G5ExclusionFrag
import S6Core.G5GeometryBridge

/-!
# Rotated chord-measure fragments (toward G5k*GeomExport)

Proved: diameter `distSq ≤ 2`; Weierstrass `g2_alg < 2`;
`RotatedG5k0ChordExport` ⇒ `G5k0GeomExport` / `G5k0Bridge`.
Open: inhabiting `RotatedG5k0ChordExport` from `PointwiseCover`.
-/

namespace S6.RotatedChordMeasure

open S6.Obligation2
open S6.Obligation2Opens
open S6.Obligation2Roles
open S6.OwnershipBridge
open S6.BernsteinGridLift
open S6.GridContribution
open S6.RotatedGridBound
open S6.G5Budget
open S6.G5ExclusionFrag
open S6.G5GeometryBridge

theorem chord_distSq_le_two (g : RotatedSquare) (p q : Pt)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q) :
    distSq p q ≤ 2 :=
  rotated_unit_diameter g p q hp hq

theorem chord_len_sq_le_two (g : RotatedSquare) (p q : Pt) (ℓ : ℚ)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q)
    (hℓ : ℓ * ℓ = distSq p q) :
    ℓ * ℓ ≤ 2 := by
  rw [hℓ]; exact chord_distSq_le_two g p q hp hq

theorem weierstrass_corner_budget (t : ℚ) (ht0 : 0 < t) (ht : t < 1 / 2) :
    g2_alg t < 2 :=
  corner_g2_alg_lt_two t ht0 ht

theorem four_corner_lengths_le_eight (c1 c2 c3 c4 : ℚ)
    (h1 : c1 ≤ 2) (h2 : c2 ≤ 2) (h3 : c3 ≤ 2) (h4 : c4 ≤ 2) :
    c1 + c2 + c3 + c4 ≤ 8 := by nlinarith

theorem chord_bounds_impossible (μ corners CF : ℚ) (hμ : 1 < μ)
    (hcorners : corners ≤ 8) (hCF : CF ≤ 4)
    (hcover : (12 : ℚ) * μ ≤ corners + CF) : False :=
  (G5GridHypLe.mk μ corners CF hμ hcorners hCF hcover).impossible

/-- Open: G5 k=0 cover exports chord corners≤8, CF≤4, cover ineq. -/
def RotatedG5k0ChordExport : Prop :=
  ∀ (T : Target) (cov : PointwiseCover T),
    isG5Class cov →
      (RoleSelection.ofCover cov).toManuscript.flags.k = ⟨0, by decide⟩ →
        ∃ corners CF : ℚ,
          corners ≤ 8 ∧ CF ≤ 4 ∧ (12 : ℚ) * T.μ ≤ corners + CF

/-- CF≤4 + cover + μ>1 ⇒ CF<4 (else 12μ ≤ corners+4 ≤ 12, contradiction). -/
theorem CF_strict_of_le_four (μ corners CF : ℚ) (hμ : 1 < μ)
    (hcorners : corners ≤ 8) (hCF : CF ≤ 4)
    (hcover : (12 : ℚ) * μ ≤ corners + CF) : CF < 4 := by
  by_contra hne
  have hge : (4 : ℚ) ≤ CF := le_of_not_gt hne
  have hEq : CF = 4 := le_antisymm hCF hge
  have : (12 : ℚ) * μ ≤ corners + 4 := by simpa [hEq] using hcover
  nlinarith [hμ, hcorners, this]

theorem G5k0Bridge_of_rotatedChordExport (h : RotatedG5k0ChordExport) :
    G5k0Bridge := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨corners, CF, hc, hCF, hcover⟩
  exact False.elim (chord_bounds_impossible T.μ corners CF T.hμ hc hCF hcover)

theorem G5k0GeomExport_of_rotatedChordExport (h : RotatedG5k0ChordExport) :
    G5k0GeomExport := by
  intro T cov hcls hk
  rcases h T cov hcls hk with ⟨corners, CF, hc, hCF, hcover⟩
  have hstrict := CF_strict_of_le_four T.μ corners CF T.hμ hc hCF hcover
  exact ⟨⟨corners, CF, T.hμ, hc, hstrict, hcover⟩⟩

def rotatedChordAlgebraicClosed : Bool := true
theorem rotatedChordAlgebraicClosed_true : rotatedChordAlgebraicClosed = true := rfl

def rotatedG5k0ChordExportProved : Bool := false
theorem rotatedG5k0ChordExportProved_false : rotatedG5k0ChordExportProved = false := rfl

def openRotatedChordExports : List String :=
  ["RotatedG5k0ChordExport from PointwiseCover",
   "g2_alg geometric reading as outer chord sum"]

end S6.RotatedChordMeasure
