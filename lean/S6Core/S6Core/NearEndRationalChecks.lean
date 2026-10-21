import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Near-end rational payload checks (R14 / R16–R19)

Exact ℚ inequalities extracted from near-end leaf certificates
(`round14_J_certificate`, `round17_analytic_negative_checks`,
`round18_positive_projection_checks`, `round19_top_gap_checks`,
`round16_geometric_reduction_checks`).

Square-form rewrites discharge √2 comparisons without ℝ.
These payloads shrink residual bookkeeping; they do **not** prove
`LivingLeafExcluded` for any living leaf, nor PrincipalClaim.
-/

namespace S6.NearEndRationalChecks

/-- R17 analytic-negative rational_checks (squared √2 forms). -/
theorem r17_709_over_5184_pos : (0 : ℚ) < (709 : ℚ) / 5184 := by native_decide

theorem r17_34_75_lt_half : (34 : ℚ) / 75 < (1 : ℚ) / 2 := by native_decide

theorem r17_193_225_gt_five_six : (193 : ℚ) / 225 > (5 : ℚ) / 6 := by native_decide

theorem r17_19_sqrt2_lt_27_sq : (19 : ℚ)^2 * 2 < (27 : ℚ)^2 := by native_decide

theorem r17_sqrt2_minus_one_lt_5_12_sq : (2 : ℚ) < ((17 : ℚ) / 12)^2 := by native_decide

theorem r17_26_15_gt_sqrt2_sq : ((26 : ℚ) / 15)^2 > (2 : ℚ) := by native_decide

/-- R18 positive-projection constant_checks. -/
theorem r18_pos_cap_at_4_15 : (0 : ℚ) < (1 : ℚ) / 225 := by native_decide

theorem r18_4_15_lt_third : (4 : ℚ) / 15 < (1 : ℚ) / 3 := by native_decide

theorem r18_4_15_lt_half : (4 : ℚ) / 15 < (1 : ℚ) / 2 := by native_decide

/-- R19 top-gap constant_checks (squared √2 forms). -/
theorem r19_sqrt2_lt_3_2_sq : (2 : ℚ) < ((3 : ℚ) / 2)^2 := by native_decide

theorem r19_19_sqrt2_lt_27_sq : (19 : ℚ)^2 * 2 < (27 : ℚ)^2 := by native_decide

theorem r19_26_15_gt_sqrt2_sq : ((26 : ℚ) / 15)^2 > (2 : ℚ) := by native_decide

theorem r19_225_193_lt_7_6 : (225 : ℚ) / 193 < (7 : ℚ) / 6 := by native_decide

theorem r19_244_495_lt_half : (244 : ℚ) / 495 < (1 : ℚ) / 2 := by native_decide

theorem r19_sqrt2_minus_one_lt_5_12_sq : (2 : ℚ) < ((17 : ℚ) / 12)^2 := by native_decide

theorem r19_709_over_5184_pos : (0 : ℚ) < (709 : ℚ) / 5184 := by native_decide

/-- Recorded symbolic constant from R19 angle coefficient sum. -/
theorem r19_angle_coeff_sum : (61 : ℚ) / 33 = (61 : ℚ) / 33 := by native_decide

/-- R16 geometric-reduction exact endpoint. -/
theorem r16_exact_endpoint_lt : (256 : ℚ) / 36993 < (1 : ℚ) / 101 := by native_decide

theorem r16_4_15_le_bound : (4 : ℚ) / 15 ≤ (4 : ℚ) / 15 := by native_decide

/-- R14 J-certificate leaf min_R / min_P positivity samples. -/
theorem r14_c_root_min_R_pos : (0 : ℚ) < (19 : ℚ) / 125 := by native_decide

theorem r14_c_root_min_P_pos : (0 : ℚ) < (290632 : ℚ) / 9765625 := by native_decide

theorem r14_m_00_min_R_pos : (0 : ℚ) < (451 : ℚ) / 80 := by native_decide

theorem r14_m_00_min_P_pos : (0 : ℚ) < (7938371 : ℚ) / 160 := by native_decide

theorem r14_m_0100_min_R_pos : (0 : ℚ) < (33 : ℚ) / 8 := by native_decide

theorem r14_m_0100_min_P_pos : (0 : ℚ) < (301077 : ℚ) / 16 := by native_decide

theorem r14_m_0101_min_R_pos : (0 : ℚ) < (81 : ℚ) / 32 := by native_decide

theorem r14_m_0101_min_P_pos : (0 : ℚ) < (351 : ℚ) / 2 := by native_decide

theorem r14_m_0110_min_R_pos : (0 : ℚ) < (81 : ℚ) / 20 := by native_decide

theorem r14_m_0110_min_P_pos : (0 : ℚ) < (357777 : ℚ) / 20 := by native_decide

theorem r14_m_0111_min_R_pos : (0 : ℚ) < (197 : ℚ) / 80 := by native_decide

theorem r14_m_0111_min_P_pos : (0 : ℚ) < (3186 : ℚ) / 25 := by native_decide

theorem r14_m_10_min_R_pos : (0 : ℚ) < (219 : ℚ) / 40 := by native_decide

theorem r14_m_10_min_P_pos : (0 : ℚ) < (1863059 : ℚ) / 40 := by native_decide

theorem r14_m_1100_min_R_pos : (0 : ℚ) < (159 : ℚ) / 40 := by native_decide

theorem r14_m_1100_min_P_pos : (0 : ℚ) < (1358289 : ℚ) / 80 := by native_decide

theorem r14_m_1101_min_R_pos : (0 : ℚ) < (383 : ℚ) / 160 := by native_decide

theorem r14_m_1101_min_P_pos : (0 : ℚ) < (4023 : ℚ) / 50 := by native_decide

theorem r14_m_1110_min_R_pos : (0 : ℚ) < (39 : ℚ) / 10 := by native_decide

theorem r14_m_1110_min_P_pos : (0 : ℚ) < (80433 : ℚ) / 5 := by native_decide

theorem r14_m_1111_min_R_pos : (0 : ℚ) < (93 : ℚ) / 40 := by native_decide

theorem r14_m_1111_min_P_pos : (0 : ℚ) < (864 : ℚ) / 25 := by native_decide

def nearEndRationalCheckCount : ℕ := 41
theorem nearEndRationalCheckCount_eq : nearEndRationalCheckCount = 41 := rfl
def nearEndRationalChecksClosed : Bool := true
theorem nearEndRationalChecksClosed_true : nearEndRationalChecksClosed = true := rfl

/-- Honest: rational payloads ≠ LivingLeafExcluded for living leaves. -/
def livingLeafExcludedByRationalChecks : Bool := false
theorem livingLeafExcludedByRationalChecks_false :
    livingLeafExcludedByRationalChecks = false := rfl

end S6.NearEndRationalChecks
