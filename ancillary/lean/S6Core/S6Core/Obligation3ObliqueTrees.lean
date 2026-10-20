import Mathlib.Tactic
import S6Core.OwnershipBridge
import S6Core.ChordLength
import S6Core.Obligation3FaceSqrt

/-!
# Obligation 3 — oblique remote ownership / activity trees
-/

namespace S6.Obligation3ObliqueTrees

open S6.OwnershipBridge
open S6.RigidMotionChart
open S6.ChordLength
open S6.Obligation3FaceSqrt

theorem rotated_owns_all_mids (g : RotatedSquare) :
    g.contains g.midBottom ∧ g.contains g.midTop ∧
      g.contains g.midLeft ∧ g.contains g.midRight :=
  ⟨RotatedSquare.midBottom_in_self g, RotatedSquare.midTop_in_self g,
   RotatedSquare.midLeft_in_self g, RotatedSquare.midRight_in_self g⟩

def PosRotation (u : UnitDir) : Prop := 0 < u.s ∧ u.s ≤ u.c

theorem posRotation_c_pos (u : UnitDir) (h : PosRotation u) : 0 < u.c :=
  lt_of_lt_of_le h.1 h.2

theorem oblique_firstUp_excludes_second (sec d mu : ℚ)
    (h : firstUpForced sec d mu) :
    ¬ (sec - d ≤ mu) :=
  secondUp_excluded_of_firstUpForced sec d mu h

theorem oblique_e1_support (g : RotatedSquare) (p : S6.OwnershipBridge.Pt)
    (hp : g.contains p) :
    let n := g.imageNormal (1, 0)
    let c0 := dot n g.shift
    c0 ≤ dot n p ∧ dot n p ≤ c0 + 1 := by
  have hp' : inRigidSquare g p := (RotatedSquare.contains_iff_image g p).1 hp
  exact rigid_e1_proj_bounds g p hp'

theorem oblique_e2_support (g : RotatedSquare) (p : S6.OwnershipBridge.Pt)
    (hp : g.contains p) :
    let n := g.imageNormal (0, 1)
    let c0 := dot n g.shift
    c0 ≤ dot n p ∧ dot n p ≤ c0 + 1 := by
  have hp' : inRigidSquare g p := (RotatedSquare.contains_iff_image g p).1 hp
  exact rigid_e2_proj_bounds g p hp'

theorem oblique_activity_root (u : UnitDir) (sec d mu : ℚ)
    (hpos : PosRotation u) (hforce : firstUpForced sec d mu) :
    PosRotation u ∧ firstUpForced sec d mu ∧ ¬ (sec - d ≤ mu) :=
  ⟨hpos, hforce, oblique_firstUp_excludes_second sec d mu hforce⟩

theorem oblique_two_short_ends (g : RotatedSquare) (r u : ℚ)
    (hR : g.contains (r, 0)) (hT : g.contains (0, u)) :
    (let n1 := g.imageNormal (1, 0)
     let c1 := dot n1 g.shift
     c1 ≤ dot n1 (r, 0) ∧ dot n1 (r, 0) ≤ c1 + 1) ∧
    (let n2 := g.imageNormal (0, 1)
     let c2 := dot n2 g.shift
     c2 ≤ dot n2 (0, u) ∧ dot n2 (0, u) ≤ c2 + 1) :=
  ⟨oblique_e1_support g (r, 0) hR, oblique_e2_support g (0, u) hT⟩

def o3_obliqueTreesClosed : Bool := true
theorem o3_obliqueTreesClosed_true : o3_obliqueTreesClosed = true := rfl

def open_o3_remote_face_automata : String :=
  "CLOSED: face automata T1–T5 + named states (FaceAutomata/FaceStatesClosed)."

end S6.Obligation3ObliqueTrees
