import Mathlib.Tactic
import S6Core.Exhaustiveness
import S6Core.LeafCertificates
import S6Core.ChordLength
import S6Core.RigidMotionChart

/-!
# Near-end SE(2) / chart realisation (≠ livingFlag)

Concrete realisation: rigid motion for C, F-horizontal projection, and
free-endpoint `ChartHypotheses`. Exclusion targets `¬ NearEndLeafRealised`,
not `livingFlag → False`.
-/

namespace S6.NearEndRealisation

open S6.Exhaustiveness
open S6.LeafCertificates
open S6.ChordLength
open S6.RigidMotionChart

/-- F-horizontal sign constraint matching `FHoriz`. -/
def FHorizMatches (fh : FHoriz) (fProj : ℚ) : Prop :=
  match fh with
  | .pos => 0 < fProj
  | .neg => fProj < 0
  | .empty => fProj = 0

theorem FHorizMatches_pos {fProj : ℚ} (h : FHorizMatches .pos fProj) :
    0 < fProj := h
theorem FHorizMatches_neg {fProj : ℚ} (h : FHorizMatches .neg fProj) :
    fProj < 0 := h
theorem FHorizMatches_empty {fProj : ℚ} (h : FHorizMatches .empty fProj) :
    fProj = 0 := h

/-- SE(2) + chart data witnessing a near-end configuration of leaf `ℓ`. -/
structure NearEndSE2 (ℓ : NearLeaf) where
  C : RigidMotion
  fProj : ℚ
  z : ℚ
  d : ℚ
  chart : ChartHypotheses z d
  living : livingFlag ℓ = true
  fh_ok : FHorizMatches ℓ.fh fProj

/-- Geometric realisation Prop (∃ SE(2)/chart witness). -/
def NearEndLeafRealised (ℓ : NearLeaf) : Prop :=
  Nonempty (NearEndSE2 ℓ)

theorem realised_implies_livingFlag (ℓ : NearLeaf)
    (h : NearEndLeafRealised ℓ) : livingFlag ℓ = true := by
  obtain ⟨cfg⟩ := h
  exact cfg.living

/-- Impossible table leaves admit no SE(2) realisation. -/
theorem not_realised_of_impossible (ℓ : NearLeaf) (hi : impossible ℓ) :
    ¬ NearEndLeafRealised ℓ := by
  intro hr
  have hlive : livingFlag ℓ = true := realised_implies_livingFlag ℓ hr
  simp only [impossible] at hi
  simp only [livingFlag, hi] at hlive
  -- hlive : (!true) = true
  cases hlive

theorem realised_implies_not_impossible (ℓ : NearLeaf)
    (h : NearEndLeafRealised ℓ) : ¬ impossible ℓ := by
  intro hi
  exact not_realised_of_impossible ℓ hi h

def NearEndSE2.originWorld {ℓ : NearLeaf} (cfg : NearEndSE2 ℓ) : Pt :=
  cfg.C.apply (0, 0)

theorem NearEndSE2.originWorld_eq {ℓ : NearLeaf} (cfg : NearEndSE2 ℓ) :
    cfg.originWorld = cfg.C.shift := by
  simp [NearEndSE2.originWorld, RigidMotion.apply, translate, rotateBy]

/-- Chart product identity on every realisation. -/
theorem NearEndSE2.chord_eq_f {ℓ : NearLeaf} (cfg : NearEndSE2 ℓ) :
    cfg.chart.leftRatio * cfg.chart.rightFactor = f cfg.z cfg.d :=
  chord_eq_f_of_chartHypotheses cfg.z cfg.d cfg.chart

/-- Pos-F realisation forces positive horizontal projection. -/
theorem realised_pos_fProj (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ)
    (hfh : ℓ.fh = .pos) : 0 < cfg.fProj := by
  have h := cfg.fh_ok
  simp only [hfh, FHorizMatches] at h
  exact h

theorem realised_neg_fProj (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ)
    (hfh : ℓ.fh = .neg) : cfg.fProj < 0 := by
  have h := cfg.fh_ok
  simp only [hfh, FHorizMatches] at h
  exact h

theorem realised_empty_fProj (ℓ : NearLeaf) (cfg : NearEndSE2 ℓ)
    (hfh : ℓ.fh = .empty) : cfg.fProj = 0 := by
  have h := cfg.fh_ok
  simp only [hfh, FHorizMatches] at h
  exact h

def nearEndRealisationSE2Closed : Bool := true
theorem nearEndRealisationSE2Closed_true : nearEndRealisationSE2Closed = true := rfl

def openStatus : String :=
  "CLOSED: NearEndSE2 structure; realised⇒livingFlag; impossible⇒¬realised; chart f-id. \
   OPEN: leaf-specific OuterRT meet/gap ray constraints; closer geom discharge."

end S6.NearEndRealisation
