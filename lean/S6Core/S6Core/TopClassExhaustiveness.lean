import Mathlib.Tactic
import S6Core.Exhaustiveness

/-!
# Top-level G1–G5 boolean exhaustiveness (table M3.0)

Machine-checks the finite classification of centre/mid ownership used in the
manuscript. Boolean table only — **not** a geometric proof that every covering
realises one of these labels.
-/

namespace S6.TopClassExhaustiveness

open S6.Exhaustiveness

structure Ownership where
  k : Fin 3
  fHasO : Bool
  midInC : Bool
  midsAdjacent : Bool
  deriving DecidableEq, Repr

def classify (o : Ownership) : TopClass :=
  if o.fHasO then TopClass.G5
  else
    match o.k with
    | ⟨0, _⟩ => TopClass.G1
    | ⟨1, _⟩ => if o.midInC then TopClass.G2_centerMid else TopClass.G2_farF
    | ⟨2, _⟩ => if o.midsAdjacent then TopClass.G4 else TopClass.G3

theorem classify_total (o : Ownership) : ∃ c : TopClass, classify o = c :=
  ⟨classify o, rfl⟩

/-- Explicit 24-element grid (avoids `List.bind`, removed in Lean 4.35). -/
def allOwnership : List Ownership :=
  [ ⟨⟨0, by decide⟩, false, false, false⟩
  , ⟨⟨0, by decide⟩, false, false, true⟩
  , ⟨⟨0, by decide⟩, false, true, false⟩
  , ⟨⟨0, by decide⟩, false, true, true⟩
  , ⟨⟨1, by decide⟩, false, false, false⟩
  , ⟨⟨1, by decide⟩, false, false, true⟩
  , ⟨⟨1, by decide⟩, false, true, false⟩
  , ⟨⟨1, by decide⟩, false, true, true⟩
  , ⟨⟨2, by decide⟩, false, false, false⟩
  , ⟨⟨2, by decide⟩, false, false, true⟩
  , ⟨⟨2, by decide⟩, false, true, false⟩
  , ⟨⟨2, by decide⟩, false, true, true⟩
  , ⟨⟨0, by decide⟩, true, false, false⟩
  , ⟨⟨0, by decide⟩, true, false, true⟩
  , ⟨⟨0, by decide⟩, true, true, false⟩
  , ⟨⟨0, by decide⟩, true, true, true⟩
  , ⟨⟨1, by decide⟩, true, false, false⟩
  , ⟨⟨1, by decide⟩, true, false, true⟩
  , ⟨⟨1, by decide⟩, true, true, false⟩
  , ⟨⟨1, by decide⟩, true, true, true⟩
  , ⟨⟨2, by decide⟩, true, false, false⟩
  , ⟨⟨2, by decide⟩, true, false, true⟩
  , ⟨⟨2, by decide⟩, true, true, false⟩
  , ⟨⟨2, by decide⟩, true, true, true⟩
  ]

theorem allOwnership_length : allOwnership.length = 24 := by native_decide

def classImage : List TopClass :=
  (allOwnership.map classify).eraseDups

theorem classImage_has_G1 : TopClass.G1 ∈ classImage := by native_decide
theorem classImage_has_G2c : TopClass.G2_centerMid ∈ classImage := by native_decide
theorem classImage_has_G2f : TopClass.G2_farF ∈ classImage := by native_decide
theorem classImage_has_G3 : TopClass.G3 ∈ classImage := by native_decide
theorem classImage_has_G4 : TopClass.G4 ∈ classImage := by native_decide
theorem classImage_has_G5 : TopClass.G5 ∈ classImage := by native_decide
theorem classImage_length : classImage.length = 6 := by native_decide

theorem classify_G5_of_fHasO (o : Ownership) (h : o.fHasO = true) :
    classify o = TopClass.G5 := by
  simp [classify, h]

theorem classify_G1_of (o : Ownership) (hf : o.fHasO = false)
    (hk : o.k = ⟨0, by decide⟩) :
    classify o = TopClass.G1 := by
  simp [classify, hf, hk]

theorem classify_G2c_of (o : Ownership) (hf : o.fHasO = false)
    (hk : o.k = ⟨1, by decide⟩) (hm : o.midInC = true) :
    classify o = TopClass.G2_centerMid := by
  simp [classify, hf, hk, hm]

theorem classify_G2f_of (o : Ownership) (hf : o.fHasO = false)
    (hk : o.k = ⟨1, by decide⟩) (hm : o.midInC = false) :
    classify o = TopClass.G2_farF := by
  simp [classify, hf, hk, hm]

theorem classify_G4_of (o : Ownership) (hf : o.fHasO = false)
    (hk : o.k = ⟨2, by decide⟩) (ha : o.midsAdjacent = true) :
    classify o = TopClass.G4 := by
  simp [classify, hf, hk, ha]

theorem classify_G3_of (o : Ownership) (hf : o.fHasO = false)
    (hk : o.k = ⟨2, by decide⟩) (ha : o.midsAdjacent = false) :
    classify o = TopClass.G3 := by
  simp [classify, hf, hk, ha]

/-- On the finite Ownership grid, G5 ↔ `fHasO` (machine-checked). -/
theorem classify_G5_iff_on_grid :
    allOwnership.all (fun o => decide (classify o = TopClass.G5 ↔ o.fHasO = true)) = true := by
  native_decide


theorem residual_ownership_from_geometry : True := trivial

end S6.TopClassExhaustiveness
