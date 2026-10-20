import Mathlib.Tactic
import S6Core.Exhaustiveness

/-!
# Near-end leaf closure — external certificate inventory

Lean does **not** re-prove R13–R28 geometry. We record a finite closer-module
map for each living leaf and point to
`formalization/certs/near_end_leaf_certificate_registry.json` for script /
harness UNSAT audit paths.
-/

namespace S6.LeafCertificates

open S6.Exhaustiveness

def closerModule : NearLeaf → String
  | ⟨.bothMeet, .meet, .pos⟩ => "R13"
  | ⟨.bothMeet, .meet, .neg⟩ => "R13"
  | ⟨.bothMeet, .meet, .empty⟩ => "R16"
  | ⟨.bothMeet, .gap, .empty⟩ => "R14"
  | ⟨.bothMeet, .gap, .neg⟩ => "R17"
  | ⟨.bothMeet, .gap, .pos⟩ => "R18"
  | ⟨.topGap, .gap, .empty⟩ => "R19"
  | ⟨.topGap, .gap, .neg⟩ => "R19"
  | ⟨.topGap, .meet, .pos⟩ => "R19"
  | ⟨.topGap, .meet, .neg⟩ => "R19"
  | ⟨.topGap, .meet, .empty⟩ => "R26"
  | ⟨.topGap, .gap, .pos⟩ => "IMPOSSIBLE"
  | ⟨.rightGap, _, _⟩ => "R27/R28"
  | ⟨.bothGap, _, _⟩ => "IMPOSSIBLE"

/-- On the Bool flag, living leaves get a real closer. -/
theorem livingFlag_has_closer (ℓ : NearLeaf) (h : livingFlag ℓ = true) :
    closerModule ℓ ≠ "IMPOSSIBLE" := by
  revert h
  rcases ℓ with ⟨rt, left, fh⟩
  cases rt <;> cases left <;> cases fh <;> native_decide

def livingClosers : List (NearLeaf × String) :=
  (allNear.filter livingFlag).map fun ℓ => (ℓ, closerModule ℓ)

theorem livingClosers_length : livingClosers.length = 17 := by native_decide

theorem livingClosers_all_real :
    livingClosers.all (fun p => decide (p.2 ≠ "IMPOSSIBLE")) = true := by
  native_decide

def registryPath : String :=
  "certs/near_end_leaf_certificate_registry.json"

end S6.LeafCertificates
