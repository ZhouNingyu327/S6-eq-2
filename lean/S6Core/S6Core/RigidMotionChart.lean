import Mathlib.Tactic
import S6Core.ChordLength

/-!
# Rigid motions → intercept chart (G1 attack)

SE(2) on `ℚ × ℚ`: rotate by `UnitDir`, then translate.

## Proved
* `rotateBy` preserves dots
* translation shifts projections
* axis square extent 1 on axis normals
* rigid image extent 1 on image side-normals
* parallel `d>1` miss on extent-1 slabs
* ray intercept Thales ratios
* `ChartHypotheses` ⇒ `f`

## Oblique continuation
See `S6Core.ObliqueChart` for projected width `|c|+|s|`, manuscript `z`,
and algebra under `ChartHypotheses`. Euclidean chord↔product remains open.
-/

namespace S6.RigidMotionChart

open S6.ChordLength

abbrev Pt := ℚ × ℚ

def dot (u v : Pt) : ℚ := u.1 * v.1 + u.2 * v.2

def inAxisSquare (p : Pt) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

theorem inAxisSquare.bounds_x (p : Pt) (hp : inAxisSquare p) :
    0 ≤ p.1 ∧ p.1 ≤ 1 := ⟨hp.1, hp.2.1⟩

theorem inAxisSquare.bounds_y (p : Pt) (hp : inAxisSquare p) :
    0 ≤ p.2 ∧ p.2 ≤ 1 := ⟨hp.2.2.1, hp.2.2.2⟩

def rotateBy (u : UnitDir) (p : Pt) : Pt :=
  (u.c * p.1 - u.s * p.2, u.s * p.1 + u.c * p.2)

theorem rotateBy_dot (u : UnitDir) (p q : Pt) :
    dot (rotateBy u p) (rotateBy u q) = dot p q := by
  have hc : u.c * u.c + u.s * u.s = 1 := u.hc
  simp only [dot, rotateBy]
  have h :
      (u.c * p.1 - u.s * p.2) * (u.c * q.1 - u.s * q.2) +
        (u.s * p.1 + u.c * p.2) * (u.s * q.1 + u.c * q.2) =
      (u.c * u.c + u.s * u.s) * (p.1 * q.1 + p.2 * q.2) := by ring
  calc
    _ = (u.c * u.c + u.s * u.s) * (p.1 * q.1 + p.2 * q.2) := h
    _ = 1 * (p.1 * q.1 + p.2 * q.2) := by rw [hc]
    _ = p.1 * q.1 + p.2 * q.2 := by ring

def translate (t p : Pt) : Pt := (p.1 + t.1, p.2 + t.2)

theorem dot_translate (n t p : Pt) :
    dot n (translate t p) = dot n p + dot n t := by
  simp [dot, translate]; ring

structure RigidMotion where
  dir : UnitDir
  shift : Pt

def RigidMotion.apply (g : RigidMotion) (p : Pt) : Pt :=
  translate g.shift (rotateBy g.dir p)

def inRigidSquare (g : RigidMotion) (p : Pt) : Prop :=
  ∃ q, inAxisSquare q ∧ g.apply q = p

def RigidMotion.imageNormal (g : RigidMotion) (nBody : Pt) : Pt :=
  rotateBy g.dir nBody

theorem RigidMotion.proj_imageNormal (g : RigidMotion) (nBody q : Pt) :
    dot (g.imageNormal nBody) (g.apply q) =
      dot nBody q + dot (g.imageNormal nBody) g.shift := by
  have hrot := rotateBy_dot g.dir nBody q
  simp only [RigidMotion.apply, RigidMotion.imageNormal, dot_translate, hrot]

theorem rigid_e2_proj_bounds (g : RigidMotion) (p : Pt)
    (hp : inRigidSquare g p) :
    let n := g.imageNormal (0, 1)
    let c := dot n g.shift
    c ≤ dot n p ∧ dot n p ≤ c + 1 := by
  obtain ⟨q, hq, rfl⟩ := hp
  have ⟨hy0, hy1⟩ := inAxisSquare.bounds_y q hq
  have h := RigidMotion.proj_imageNormal g (0, 1) q
  simp only [dot, RigidMotion.imageNormal] at h ⊢
  constructor <;> linarith

theorem rigid_e1_proj_bounds (g : RigidMotion) (p : Pt)
    (hp : inRigidSquare g p) :
    let n := g.imageNormal (1, 0)
    let c := dot n g.shift
    c ≤ dot n p ∧ dot n p ≤ c + 1 := by
  obtain ⟨q, hq, rfl⟩ := hp
  have ⟨hx0, hx1⟩ := inAxisSquare.bounds_x q hq
  have h := RigidMotion.proj_imageNormal g (1, 0) q
  simp only [dot, RigidMotion.imageNormal] at h ⊢
  constructor <;> linarith

theorem parallel_miss_extent_one (α d : ℚ) (hd : 1 < d)
    (h0 : α ≤ 0 ∧ 0 ≤ α + 1) (hd' : α ≤ d ∧ d ≤ α + 1) : False :=
  extent_one_blocks_gap α d hd h0 hd'

theorem rigid_sideNormal_parallel_sum_le_one (d : ℚ) (hd : 1 < d) (α : ℚ) :
    (if α ≤ 0 ∧ 0 ≤ α + 1 then (1 : ℚ) else 0) +
      (if α ≤ d ∧ d ≤ α + 1 then (1 : ℚ) else 0) ≤ 1 :=
  rotated_side_normal_parallel_sum_le_one d hd α

theorem rigid_sideNormal_extent_one_e2 (g : RigidMotion) (p : Pt)
    (hp : inRigidSquare g p) :
    ∃ c : ℚ, c ≤ dot (g.imageNormal (0, 1)) p ∧
      dot (g.imageNormal (0, 1)) p ≤ c + 1 :=
  ⟨dot (g.imageNormal (0, 1)) g.shift, rigid_e2_proj_bounds g p hp⟩

theorem rigid_sideNormal_extent_one_e1 (g : RigidMotion) (p : Pt)
    (hp : inRigidSquare g p) :
    ∃ c : ℚ, c ≤ dot (g.imageNormal (1, 0)) p ∧
      dot (g.imageNormal (1, 0)) p ≤ c + 1 :=
  ⟨dot (g.imageNormal (1, 0)) g.shift, rigid_e1_proj_bounds g p hp⟩

def rayHit (o u n : Pt) (α : ℚ) : ℚ :=
  (α - dot n o) / dot n u

theorem ray_intercept_ratio (o u n : Pt) (α0 α1 α2 : ℚ)
    (hden : dot n u ≠ 0) (h01 : α1 ≠ α0) :
    let t := rayHit o u n
    (t α2 - t α0) / (t α1 - t α0) = (α2 - α0) / (α1 - α0) := by
  intro t
  simp only [rayHit, t]
  field_simp [hden, sub_ne_zero.mpr h01]
  ring

theorem thales_chart_gives_f (z d : ℚ) (h : ChartHypotheses z d) :
    h.leftRatio * h.rightFactor = f z d :=
  chord_eq_f_of_chartHypotheses z d h

def pureTranslation (t : Pt) : RigidMotion :=
  ⟨⟨1, 0, by norm_num⟩, t⟩

theorem pureTranslation_apply (t p : Pt) :
    (pureTranslation t).apply p = translate t p := by
  simp [RigidMotion.apply, pureTranslation, rotateBy, translate]

def pureRotation (u : UnitDir) : RigidMotion := ⟨u, (0, 0)⟩

theorem pureRotation_apply (u : UnitDir) (p : Pt) :
    (pureRotation u).apply p = rotateBy u p := by
  simp [RigidMotion.apply, pureRotation, translate]

theorem every_rigid_is_rotate_then_translate (g : RigidMotion) (p : Pt) :
    g.apply p = translate g.shift (rotateBy g.dir p) := rfl

def sideNormalSE2Closed : Bool := true
theorem G1_sideNormal_closed : sideNormalSE2Closed = true := rfl
-- Oblique flags live in `S6.ObliqueChart`.

end S6.RigidMotionChart
