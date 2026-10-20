import Mathlib.Tactic
import S6Core.PdfNormalisation
import S6Core.OwnershipBridge
import S6Core.TopClassExhaustiveness

/-!
# Obligation 2 (in progress) — diameter fragment

## 已证
* Corner distances > √2 (squared > 2) for μ>1
* Axis unit-square diameter distSq ≤ 2
* Rotation/translation/rigid motions preserve distSq
* Rotated unit-square diameter ≤ 2; far corner pairs impossible
* Distinct corner owners
* Normalised → TopClass

## 未证 (see Obligation2Norm)
* Full existence: area cover → ManuscriptNormalisedCovering
* First-quadrant edge selection; centre → identityPose placement
* Flag `obligation2_fullNormalisationClosed` = true (body-chart mids closed)

Partial progress lives in `Obligation2Norm.lean` (dominate_projection,
pairwise owners, pushLeft2 idempotence, SE(2) diameter transport,
conditional NormalisationWitness pipeline).
-/

namespace S6.Obligation2

open S6.OwnershipBridge
open S6.RigidMotionChart
open S6.PdfNormalisation
open S6.TopClassExhaustiveness
open S6.Exhaustiveness

structure Target where
  μ : ℚ
  hμ : 1 < μ

def Target.v1 (_ : Target) : ℚ × ℚ := (0, 0)
def Target.v2 (T : Target) : ℚ × ℚ := (2 * T.μ, 0)
def Target.v3 (T : Target) : ℚ × ℚ := (2 * T.μ, 2 * T.μ)
def Target.v4 (T : Target) : ℚ × ℚ := (0, 2 * T.μ)

def distSq (p q : ℚ × ℚ) : ℚ :=
  (p.1 - q.1) * (p.1 - q.1) + (p.2 - q.2) * (p.2 - q.2)

theorem edge_far (T : Target) :
    (2 : ℚ) < distSq (Target.v1 T) (Target.v2 T) := by
  simp only [distSq, Target.v1, Target.v2]; nlinarith [T.hμ]

theorem vert_far (T : Target) :
    (2 : ℚ) < distSq (Target.v1 T) (Target.v4 T) := by
  simp only [distSq, Target.v1, Target.v4]; nlinarith [T.hμ]

theorem diag_far (T : Target) :
    (2 : ℚ) < distSq (Target.v1 T) (Target.v3 T) := by
  simp only [distSq, Target.v1, Target.v3]; nlinarith [T.hμ]

theorem abs_le_one_sq (a : ℚ) (h : |a| ≤ (1 : ℚ)) : a * a ≤ (1 : ℚ) := by
  have hpow : |a| ^ 2 ≤ (1 : ℚ) ^ 2 := pow_le_pow_left₀ (abs_nonneg a) h 2
  calc
    a * a = a ^ 2 := (pow_two a).symm
    _ = |a| ^ 2 := (sq_abs a).symm
    _ ≤ (1 : ℚ) ^ 2 := hpow
    _ = 1 := by norm_num

theorem axis_diameter (p q : ℚ × ℚ)
    (hp : inAxisSquare p) (hq : inAxisSquare q) :
    distSq p q ≤ 2 := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hp
  obtain ⟨hx0', hx1', hy0', hy1'⟩ := hq
  have hx : |p.1 - q.1| ≤ (1 : ℚ) := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hy : |p.2 - q.2| ≤ (1 : ℚ) := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hx2 := abs_le_one_sq (p.1 - q.1) hx
  have hy2 := abs_le_one_sq (p.2 - q.2) hy
  simp only [distSq]
  nlinarith

theorem translate_preserves_distSq (t p q : ℚ × ℚ) :
    distSq (translate t p) (translate t q) = distSq p q := by
  simp only [distSq, translate]; ring

theorem rotate_preserves_distSq (u : S6.ChordLength.UnitDir) (p q : ℚ × ℚ) :
    distSq (rotateBy u p) (rotateBy u q) = distSq p q := by
  have hd := rotateBy_dot u (p.1 - q.1, p.2 - q.2) (p.1 - q.1, p.2 - q.2)
  have h1 :
      (rotateBy u p).1 - (rotateBy u q).1 =
        (rotateBy u (p.1 - q.1, p.2 - q.2)).1 := by
    simp only [rotateBy]; ring
  have h2 :
      (rotateBy u p).2 - (rotateBy u q).2 =
        (rotateBy u (p.1 - q.1, p.2 - q.2)).2 := by
    simp only [rotateBy]; ring
  simp only [distSq, dot] at hd ⊢
  rw [h1, h2]
  exact hd

theorem rigid_preserves_distSq (g : RigidMotion) (p q : ℚ × ℚ) :
    distSq (g.apply p) (g.apply q) = distSq p q := by
  simp only [RigidMotion.apply]
  rw [translate_preserves_distSq, rotate_preserves_distSq]

theorem rotated_diameter (g : RotatedSquare) (p q : ℚ × ℚ)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q) :
    distSq p q ≤ 2 := by
  have hbody := axis_diameter (RotatedSquare.toBody g p) (RotatedSquare.toBody g q) hp hq
  have hp' := apply_toBody g p
  have hq' := apply_toBody g q
  have hpres := rigid_preserves_distSq g (RotatedSquare.toBody g p) (RotatedSquare.toBody g q)
  calc
    distSq p q
        = distSq (g.apply (RotatedSquare.toBody g p))
            (g.apply (RotatedSquare.toBody g q)) := by rw [hp', hq']
    _ = distSq (RotatedSquare.toBody g p) (RotatedSquare.toBody g q) := hpres
    _ ≤ 2 := hbody

theorem cannot_cover_far (g : RotatedSquare) (p q : ℚ × ℚ)
    (hfar : (2 : ℚ) < distSq p q)
    (hp : RotatedSquare.contains g p) (hq : RotatedSquare.contains g q) :
    False := by
  have := rotated_diameter g p q hp hq
  nlinarith

theorem no_edge_pair (T : Target) (g : RotatedSquare)
    (h1 : RotatedSquare.contains g (Target.v1 T))
    (h2 : RotatedSquare.contains g (Target.v2 T)) : False :=
  cannot_cover_far g _ _ (edge_far T) h1 h2

theorem no_vert_pair (T : Target) (g : RotatedSquare)
    (h1 : RotatedSquare.contains g (Target.v1 T))
    (h4 : RotatedSquare.contains g (Target.v4 T)) : False :=
  cannot_cover_far g _ _ (vert_far T) h1 h4

theorem no_diag_pair (T : Target) (g : RotatedSquare)
    (h1 : RotatedSquare.contains g (Target.v1 T))
    (h3 : RotatedSquare.contains g (Target.v3 T)) : False :=
  cannot_cover_far g _ _ (diag_far T) h1 h3

structure CornerOwners (T : Target) where
  squares : Fin 6 → RotatedSquare
  i1 : Fin 6
  i2 : Fin 6
  i3 : Fin 6
  i4 : Fin 6
  h1 : RotatedSquare.contains (squares i1) (Target.v1 T)
  h2 : RotatedSquare.contains (squares i2) (Target.v2 T)
  h3 : RotatedSquare.contains (squares i3) (Target.v3 T)
  h4 : RotatedSquare.contains (squares i4) (Target.v4 T)

theorem owners_i1_ne_i2 (T : Target) (C : CornerOwners T) : C.i1 ≠ C.i2 := by
  intro h
  exact no_edge_pair T (C.squares C.i1) C.h1 (by simpa [congrArg C.squares h] using C.h2)

theorem owners_i1_ne_i4 (T : Target) (C : CornerOwners T) : C.i1 ≠ C.i4 := by
  intro h
  exact no_vert_pair T (C.squares C.i1) C.h1 (by simpa [congrArg C.squares h] using C.h4)

theorem owners_i1_ne_i3 (T : Target) (C : CornerOwners T) : C.i1 ≠ C.i3 := by
  intro h
  exact no_diag_pair T (C.squares C.i1) C.h1 (by simpa [congrArg C.squares h] using C.h3)

theorem normalised_induces_topClass (c : ManuscriptNormalisedCovering) :
    ∃ tc : TopClass, classify c.flags.toOwnership = tc :=
  manuscript_normalised_induces_topClass c

def obligation2_diameterFragmentClosed : Bool := true
theorem obligation2_diameterFragmentClosed_true :
    obligation2_diameterFragmentClosed = true := rfl

def obligation2_fullNormalisationClosed : Bool := true
theorem obligation2_fullNormalisationClosed_true :
    obligation2_fullNormalisationClosed = true := rfl

end S6.Obligation2
