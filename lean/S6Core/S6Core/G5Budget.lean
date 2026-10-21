import Mathlib.Tactic
import S6Core.ParallelBudget
import S6Core.ParallelBudgetGeometry

/-!
# G5 budget algebra — R2-style grid contradictions

Proves the **rational budget lemmas** used in the early G5 chain (INTERNAL_G5 R2–R3):

* `d + B(d) < 2` for every `ParallelBudgetData`
* Grid-length contradictions: `12μ ≤ corners + CF` impossible under the
  manuscript bounds `corners ≤ 8`, `CF < 4` or `CF ≤ 2μ + 2B` with `μ+B < 2`

These are not yet a full `G5Exclusion` (geometry→budget bridge still open),
but they are unconditional Lean theorems on the algebraic side of R2.
-/

namespace S6.G5Budget

open S6.ParallelBudget
open S6.ParallelBudgetGeometry

/-! ## `d + B < 2` -/

/-- Critical branch: `(d+y)² ≤ 2` forces `d < 5/3`, hence `d + Bcrit < 2`. -/
theorem d_add_Bcrit_lt_two (d y : ℚ) (hd : 1 < d) (hy : 0 < y)
    (hy2 : y * y = d * d - 1)
    (hcrit : (d + y) * (d + y) ≤ 2) :
    d + Bcrit d y < 2 := by
  -- Equivalent: y > 2d - 2
  have hgoal : 2 * d - 2 < y → d + (d - y) < 2 := by intro; nlinarith
  -- From (d+y)² ≤ 2 and y² = d²-1 derive d < 5/3, then y² > (2d-2)²
  have hy_gt : 2 * d - 2 < y := by
    -- First: 2d - 2 < d + y always? Better compare squares.
    -- Show (2d-2)² < y² using (d+y)² ≤ 2 ⇒ d is small enough.
    have hdy : 0 < d + y := add_pos (lt_trans (by norm_num : (0:ℚ) < 1) hd) hy
    -- From (d+y)² ≤ 2 and y² = d²-1: expand to bound d
    -- (d+y)² = d² + 2dy + y² = d² + 2dy + d² - 1 = 2d² + 2dy - 1 ≤ 2
    -- ⇒ 2d² + 2dy ≤ 3
    have hsum : 2 * d * d + 2 * d * y ≤ 3 := by
      have : (d + y) * (d + y) = 2 * d * d + 2 * d * y - 1 := by
        nlinarith [hy2]
      nlinarith [hcrit, this]
    -- Also need 2d-2 > 0 for squaring direction, i.e. d > 1 (given)
    have hpos : (0 : ℚ) < 2 * d - 2 := by nlinarith [hd]
    -- Prove (2d-2)² < y² = d²-1
    -- (2d-2)² - (d²-1) = 4(d-1)² - (d-1)(d+1) = (d-1)(4(d-1)-(d+1)) = (d-1)(3d-5)
    -- So need 3d-5 < 0 i.e. d < 5/3.
    have hd_lt : d < (5 : ℚ) / 3 := by
      -- From 2d² + 2dy ≤ 3 and y > 0: 2d² < 3 ⇒ d² < 3/2 ⇒ d < √(3/2) < 5/3
      -- √(3/2)² = 1.5, (5/3)² = 25/9 ≈ 2.77 > 1.5, so d² < 3/2 ⇒ d < 5/3
      have : 2 * d * d < 3 := by nlinarith [hsum, hy, hd]
      have hd2 : d * d < (3 : ℚ) / 2 := by nlinarith
      have h53 : (5 : ℚ) / 3 * ((5 : ℚ) / 3) = (25 : ℚ) / 9 := by norm_num
      have : (3 : ℚ) / 2 < (25 : ℚ) / 9 := by norm_num
      have hdpos : (0 : ℚ) < d := lt_trans (by norm_num) hd
      exact (sq_lt_sq₀ (le_of_lt hdpos) (by norm_num : (0:ℚ) ≤ (5:ℚ)/3)).1
        (by nlinarith [hd2, this, h53])
    have hdiff : (2 * d - 2) * (2 * d - 2) < y * y := by
      have : y * y - (2 * d - 2) * (2 * d - 2) =
          (d - 1) * (5 - 3 * d) := by nlinarith [hy2]
      have hfac : 0 < (d - 1) * (5 - 3 * d) := by
        have : 0 < d - 1 := sub_pos.mpr hd
        have : 0 < 5 - 3 * d := by nlinarith [hd_lt]
        exact mul_pos (by nlinarith [hd]) (by nlinarith [hd_lt])
      nlinarith [this, hfac]
    exact (sq_lt_sq₀ (le_of_lt hpos) (le_of_lt hy)).1 (by simpa [pow_two] using hdiff)
  simpa [Bcrit] using hgoal hy_gt

/-- Edge branch: `d + Bedge = 2s - d < 2` since `s² = 2` and `1 < d ≤ s`. -/
theorem d_add_Bedge_lt_two (d s : ℚ) (hd : 1 < d) (hs : 0 < s) (hs2 : s * s = 2)
    (hd_le_s : d ≤ s) :
    d + Bedge d s < 2 := by
  have h : d + Bedge d s = 2 * s - d := by simp only [Bedge]; ring
  rw [h]
  -- 2s - d ≤ 2s - 1 < 2 because (2s)² = 8 < 9 = 3²
  have h1 : 2 * s - d ≤ 2 * s - 1 := by nlinarith [hd]
  have hspos : (0 : ℚ) ≤ 2 * s := by nlinarith [hs]
  have h2s : 2 * s < 3 := by
    have hsq : (2 * s) * (2 * s) = 8 := by
      calc (2 * s) * (2 * s) = 4 * (s * s) := by ring
        _ = 4 * 2 := by rw [hs2]
        _ = 8 := by norm_num
    exact (sq_lt_sq₀ hspos (by norm_num : (0:ℚ) ≤ (3:ℚ))).1 (by
      simpa [pow_two] using (by nlinarith [hsq] : (2 * s) * (2 * s) < (3:ℚ) * 3))
  nlinarith [h1, h2s]

theorem d_add_B_lt_two_of (D : ParallelBudgetData) :
    D.d + D.B < 2 := by
  by_cases h : (D.d + D.y) * (D.d + D.y) ≤ 2
  · have hB : D.B = Bcrit D.d D.y := by simp [ParallelBudgetData.B, h]
    rw [hB]
    exact d_add_Bcrit_lt_two D.d D.y D.hd D.hy D.hy2 h
  · have hB : D.B = Bedge D.d D.s := by simp [ParallelBudgetData.B, h]
    rw [hB]
    exact d_add_Bedge_lt_two D.d D.s D.hd D.hs D.hs2 D.hd_le_s

/-- Specialisation: when the separation equals the half-side `μ`. -/
theorem mu_add_B_lt_two (D : ParallelBudgetData) (μ : ℚ) (hμ : μ = D.d) :
    μ + D.B < 2 := by
  have := d_add_B_lt_two_of D
  nlinarith

/-! ## Grid-length contradictions (R2 algebra) -/

/-- Abstract R2 opposite-mids / three-ray package. -/
structure G5GridHyp where
  μ : ℚ
  corners : ℚ
  CF : ℚ
  hμ : 1 < μ
  hcorners : corners ≤ 8
  hCF : CF < 4
  /-- Putative covering: grid length `12μ` covered by corners+CF. -/
  hcover : (12 : ℚ) * μ ≤ corners + CF

theorem G5GridHyp.impossible (H : G5GridHyp) : False := by
  have h12 : (12 : ℚ) < 12 * H.μ := by nlinarith [H.hμ]
  have htot : H.corners + H.CF < 12 := by nlinarith [H.hcorners, H.hCF]
  nlinarith [H.hcover, h12, htot]

/-- Opposite-mids variant: CF bound `2μ + 2B` with `μ+B < 2` ⇒ `CF < 4`. -/
structure G5OppositeMidHyp where
  μ : ℚ
  B : ℚ
  corners : ℚ
  hμ : 1 < μ
  hB : 0 ≤ B
  hμB : μ + B < 2
  hcorners : corners ≤ 8
  hcover : (12 : ℚ) * μ ≤ corners + (2 * μ + 2 * B)

theorem G5OppositeMidHyp.CF_lt_four (H : G5OppositeMidHyp) :
    2 * H.μ + 2 * H.B < 4 := by nlinarith [H.hμB]

theorem G5OppositeMidHyp.impossible (H : G5OppositeMidHyp) : False := by
  have hCF := H.CF_lt_four
  have h12 : (12 : ℚ) < 12 * H.μ := by nlinarith [H.hμ]
  have htot : H.corners + (2 * H.μ + 2 * H.B) < 12 := by nlinarith [H.hcorners, hCF]
  nlinarith [H.hcover, h12, htot]

/-- Adjacent-mids / three-ray package: CF bound strictly below 4. -/
structure G5AdjacentMidHyp where
  μ : ℚ
  corners : ℚ
  CF : ℚ
  hμ : 1 < μ
  hcorners : corners ≤ 8
  hCF : CF ≤ 3  -- stricter than <4; three-ray max estimates
  hcover : (12 : ℚ) * μ ≤ corners + CF

theorem G5AdjacentMidHyp.impossible (H : G5AdjacentMidHyp) : False := by
  have h12 : (12 : ℚ) < 12 * H.μ := by nlinarith [H.hμ]
  have htot : H.corners + H.CF < 12 := by nlinarith [H.hcorners, H.hCF]
  nlinarith [H.hcover, h12, htot]

/-- Wire `ParallelBudgetData` into opposite-mid hyp when corners≤8 and cover ineq. -/
theorem opposite_from_parallelBudget (D : ParallelBudgetData) (μ corners : ℚ)
    (hμeq : μ = D.d) (hμ : 1 < μ) (hcorners : corners ≤ 8)
    (hcover : (12 : ℚ) * μ ≤ corners + (2 * μ + 2 * D.B)) :
    False := by
  have hμB : μ + D.B < 2 := mu_add_B_lt_two D μ hμeq
  have hB0 : 0 ≤ D.B := by
    -- B = Bcrit or Bedge; both can be shown ≥ 0 on the feasible range, but
    -- opposite hyp only needs μ+B<2 + cover. Use 0≤B from Bedge/Bcrit:
    -- Bcrit = d-y: (d-y)(d+y) = d²-y² = 1 > 0 and d+y>0 ⇒ d-y>0
    -- Bedge = 2(s-d) ≥ 0 by d≤s
    by_cases h : (D.d + D.y) * (D.d + D.y) ≤ 2
    · have hB : D.B = Bcrit D.d D.y := by simp [ParallelBudgetData.B, h]
      rw [hB, Bcrit]
      have hdy : 0 < D.d + D.y :=
        add_pos (lt_trans (by norm_num : (0:ℚ) < 1) D.hd) D.hy
      have : (D.d - D.y) * (D.d + D.y) = 1 := by nlinarith [D.hy2]
      have hpos : 0 < D.d - D.y := by
        have := this
        nlinarith [hdy]
      exact le_of_lt hpos
    · have hB : D.B = Bedge D.d D.s := by simp [ParallelBudgetData.B, h]
      rw [hB, Bedge]
      nlinarith [D.hd_le_s]
  exact (G5OppositeMidHyp.mk μ D.B corners hμ hB0 hμB hcorners hcover).impossible

/-- Re-export side-gap / no-side-gap algebra already in `ParallelBudget`. -/
theorem sideGap_impossible (h : BudgetHyp)
    (hp : (12 : ℚ) * h.μ ≤ 8 + 3 * h.B + h.vF) : False :=
  sideGap_covering_impossible h hp

theorem noSideGap_impossible (μ B : ℚ) (hμ : 1 < μ) (hB : B < 1)
    (hp : (12 : ℚ) * μ ≤ 8 + 2 * B + 2 * μ) : False :=
  noSideGap_covering_impossible μ B hμ hB hp


/-- Same contradiction with non-strict `CF ≤ 4` (since `8+4=12 < 12μ`). -/
structure G5GridHypLe where
  μ : ℚ
  corners : ℚ
  CF : ℚ
  hμ : 1 < μ
  hcorners : corners ≤ 8
  hCF : CF ≤ 4
  hcover : (12 : ℚ) * μ ≤ corners + CF

theorem G5GridHypLe.impossible (H : G5GridHypLe) : False := by
  have h12 : (12 : ℚ) < 12 * H.μ := by nlinarith [H.hμ]
  have htot : H.corners + H.CF ≤ 12 := by nlinarith [H.hcorners, H.hCF]
  nlinarith [H.hcover, h12, htot]

end S6.G5Budget
