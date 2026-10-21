import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Near-end exact certs R24–R28 (extra uniform-sign payloads)

Second wave of `native_decide` lifts from `exact_certs_batch24` rounds 24–28.
Does not touch MainTheorem / G5ExclusionFrag / AxisG5k0FromCover.
Payload nonneg/nonpos ≠ PrincipalClaim.
-/

namespace S6.NearEndExactR24_28Extra

def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

def nonposList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (c ≤ 0) && nonposList cs

/-- From `check_round24_g3_cside__n9__b12141227f.json` path `certificate_leading_pos_coeffs_on_[1,3]`. -/
def check_round24_g3_cside_n9_b12141227f_certificate_leading_pos_coeffs_on_1_3 : List ℚ :=
  [0, 16]
theorem check_round24_g3_cside_n9_b12141227f_certificate_leading_pos_coeffs_on_1_3_nonneg : nonnegList check_round24_g3_cside_n9_b12141227f_certificate_leading_pos_coeffs_on_1_3 = true := by native_decide

/-- From `check_round24_g3_fside__n4__a82de007c0.json` path `certificate_numer_coeffs`. -/
def check_round24_g3_fside_n4_a82de007c0_certificate_numer_coeffs : List ℚ :=
  [1, 1, 0]
theorem check_round24_g3_fside_n4_a82de007c0_certificate_numer_coeffs_nonneg : nonnegList check_round24_g3_fside_n4_a82de007c0_certificate_numer_coeffs = true := by native_decide

/-- From `check_round24_g3_fside__n4__a82de007c0.json` path `certificate_denom_coeffs`. -/
def check_round24_g3_fside_n4_a82de007c0_certificate_denom_coeffs : List ℚ :=
  [1, 1, (48 : ℚ) / 49]
theorem check_round24_g3_fside_n4_a82de007c0_certificate_denom_coeffs_nonneg : nonnegList check_round24_g3_fside_n4_a82de007c0_certificate_denom_coeffs = true := by native_decide

/-- From `check_round24_g3_fside__n5__cbecdd171f.json` path `certificate_f_coeffs`. -/
def check_round24_g3_fside_n5_cbecdd171f_certificate_f_coeffs : List ℚ :=
  [1, 1, (17 : ℚ) / 25]
theorem check_round24_g3_fside_n5_cbecdd171f_certificate_f_coeffs_nonneg : nonnegList check_round24_g3_fside_n5_cbecdd171f_certificate_f_coeffs = true := by native_decide

/-- From `check_round24_g3_fside__n5__cbecdd171f.json` path `certificate_witness_coeffs`. -/
def check_round24_g3_fside_n5_cbecdd171f_certificate_witness_coeffs : List ℚ :=
  [0, (4 : ℚ) / 45, (28 : ℚ) / 225, (8 : ℚ) / 375]
theorem check_round24_g3_fside_n5_cbecdd171f_certificate_witness_coeffs_nonneg : nonnegList check_round24_g3_fside_n5_cbecdd171f_certificate_witness_coeffs = true := by native_decide

/-- From `check_round24_g3_fside__n7__ce41334842.json` path `certificate_numer_coeffs`. -/
def check_round24_g3_fside_n7_ce41334842_certificate_numer_coeffs : List ℚ :=
  [0, 0, 4, 2, 12, 8]
theorem check_round24_g3_fside_n7_ce41334842_certificate_numer_coeffs_nonneg : nonnegList check_round24_g3_fside_n7_ce41334842_certificate_numer_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n12__35a3a52b42.json` path `certificate_bernstein_4_5h_h2`. -/
def check_round25_g3_complete_n12_35a3a52b42_certificate_bernstein_4_5h_h2 : List ℚ :=
  [4, (11 : ℚ) / 4, (5 : ℚ) / 4]
theorem check_round25_g3_complete_n12_35a3a52b42_certificate_bernstein_4_5h_h2_nonneg : nonnegList check_round25_g3_complete_n12_35a3a52b42_certificate_bernstein_4_5h_h2 = true := by native_decide

/-- From `check_round25_g3_complete__n5__d1f1497dfb.json` path `certificate_f_coeffs`. -/
def check_round25_g3_complete_n5_d1f1497dfb_certificate_f_coeffs : List ℚ :=
  [1, 1, (193 : ℚ) / 225]
theorem check_round25_g3_complete_n5_d1f1497dfb_certificate_f_coeffs_nonneg : nonnegList check_round25_g3_complete_n5_d1f1497dfb_certificate_f_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n5__d1f1497dfb.json` path `certificate_witness_coeffs`. -/
def check_round25_g3_complete_n5_d1f1497dfb_certificate_witness_coeffs : List ℚ :=
  [0, (4 : ℚ) / 135, (8 : ℚ) / 225, (52 : ℚ) / 10125]
theorem check_round25_g3_complete_n5_d1f1497dfb_certificate_witness_coeffs_nonneg : nonnegList check_round25_g3_complete_n5_d1f1497dfb_certificate_witness_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n5__e43d6cfe6c.json` path `certificate_f_coeffs`. -/
def check_round25_g3_complete_n5_e43d6cfe6c_certificate_f_coeffs : List ℚ :=
  [1, 1, (17 : ℚ) / 25]
theorem check_round25_g3_complete_n5_e43d6cfe6c_certificate_f_coeffs_nonneg : nonnegList check_round25_g3_complete_n5_e43d6cfe6c_certificate_f_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n5__e43d6cfe6c.json` path `certificate_witness_coeffs`. -/
def check_round25_g3_complete_n5_e43d6cfe6c_certificate_witness_coeffs : List ℚ :=
  [0, (4 : ℚ) / 45, (28 : ℚ) / 225, (8 : ℚ) / 375]
theorem check_round25_g3_complete_n5_e43d6cfe6c_certificate_witness_coeffs_nonneg : nonnegList check_round25_g3_complete_n5_e43d6cfe6c_certificate_witness_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n8__12ea6e3a3d.json` path `certificate_numer_coeffs`. -/
def check_round25_g3_complete_n8_12ea6e3a3d_certificate_numer_coeffs : List ℚ :=
  [0, 0, (16 : ℚ) / 75, (48 : ℚ) / 125, (224 : ℚ) / 625]
theorem check_round25_g3_complete_n8_12ea6e3a3d_certificate_numer_coeffs_nonneg : nonnegList check_round25_g3_complete_n8_12ea6e3a3d_certificate_numer_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n8__12ea6e3a3d.json` path `certificate_denom_coeffs`. -/
def check_round25_g3_complete_n8_12ea6e3a3d_certificate_denom_coeffs : List ℚ :=
  [1, 1, (79 : ℚ) / 75, (29 : ℚ) / 25, (841 : ℚ) / 625]
theorem check_round25_g3_complete_n8_12ea6e3a3d_certificate_denom_coeffs_nonneg : nonnegList check_round25_g3_complete_n8_12ea6e3a3d_certificate_denom_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n8__aa4c338fcf.json` path `certificate_numer_coeffs`. -/
def check_round25_g3_complete_n8_aa4c338fcf_certificate_numer_coeffs : List ℚ :=
  [0, (1 : ℚ) / 2, 0]
theorem check_round25_g3_complete_n8_aa4c338fcf_certificate_numer_coeffs_nonneg : nonnegList check_round25_g3_complete_n8_aa4c338fcf_certificate_numer_coeffs = true := by native_decide

/-- From `check_round25_g3_complete__n8__aa4c338fcf.json` path `certificate_denom_coeffs`. -/
def check_round25_g3_complete_n8_aa4c338fcf_certificate_denom_coeffs : List ℚ :=
  [1, 2]
theorem check_round25_g3_complete_n8_aa4c338fcf_certificate_denom_coeffs_nonneg : nonnegList check_round25_g3_complete_n8_aa4c338fcf_certificate_denom_coeffs = true := by native_decide

/-- From `check_round26_g2_top__n7__1cf912de97.json` path `certificate_leading_pos_coeffs_on_[1,3]`. -/
def check_round26_g2_top_n7_1cf912de97_certificate_leading_pos_coeffs_on_1_3 : List ℚ :=
  [0, 16]
theorem check_round26_g2_top_n7_1cf912de97_certificate_leading_pos_coeffs_on_1_3_nonneg : nonnegList check_round26_g2_top_n7_1cf912de97_certificate_leading_pos_coeffs_on_1_3 = true := by native_decide

/-- From `check_round26_g2_top__n7__44d9df748d.json` path `certificate_numer_coeffs`. -/
def check_round26_g2_top_n7_44d9df748d_certificate_numer_coeffs : List ℚ :=
  [0, 0, (5 : ℚ) / 18, (5 : ℚ) / 21, (95 : ℚ) / 216, (65 : ℚ) / 189, (85 : ℚ) / 432, (85 : ℚ) / 3024]
theorem check_round26_g2_top_n7_44d9df748d_certificate_numer_coeffs_nonneg : nonnegList check_round26_g2_top_n7_44d9df748d_certificate_numer_coeffs = true := by native_decide

/-- From `check_round26_g2_top__n7__44d9df748d.json` path `certificate_denom_coeffs`. -/
def check_round26_g2_top_n7_44d9df748d_certificate_denom_coeffs : List ℚ :=
  [1, (41 : ℚ) / 36, (527 : ℚ) / 432, (2023 : ℚ) / 1728]
theorem check_round26_g2_top_n7_44d9df748d_certificate_denom_coeffs_nonneg : nonnegList check_round26_g2_top_n7_44d9df748d_certificate_denom_coeffs = true := by native_decide

/-- From `check_round26_g2_top__n7__69e7323738.json` path `certificate_numer_coeffs`. -/
def check_round26_g2_top_n7_69e7323738_certificate_numer_coeffs : List ℚ :=
  [0, 0, 4, 2, 12, 8]
theorem check_round26_g2_top_n7_69e7323738_certificate_numer_coeffs_nonneg : nonnegList check_round26_g2_top_n7_69e7323738_certificate_numer_coeffs = true := by native_decide

/-- From `check_round26_g2_top__n7__7905cebf07.json` path `certificate_numer_coeffs`. -/
def check_round26_g2_top_n7_7905cebf07_certificate_numer_coeffs : List ℚ :=
  [0, 0, (5 : ℚ) / 18, (5 : ℚ) / 21, (95 : ℚ) / 216, (65 : ℚ) / 189, (85 : ℚ) / 432, (85 : ℚ) / 3024]
theorem check_round26_g2_top_n7_7905cebf07_certificate_numer_coeffs_nonneg : nonnegList check_round26_g2_top_n7_7905cebf07_certificate_numer_coeffs = true := by native_decide

/-- From `check_round26_g2_top__n7__7905cebf07.json` path `certificate_denom_coeffs`. -/
def check_round26_g2_top_n7_7905cebf07_certificate_denom_coeffs : List ℚ :=
  [1, (41 : ℚ) / 36, (527 : ℚ) / 432, (2023 : ℚ) / 1728]
theorem check_round26_g2_top_n7_7905cebf07_certificate_denom_coeffs_nonneg : nonnegList check_round26_g2_top_n7_7905cebf07_certificate_denom_coeffs = true := by native_decide

/-- From `check_round26_g2_top__n7__9b6f03fd30.json` path `certificate_numer_coeffs`. -/
def check_round26_g2_top_n7_9b6f03fd30_certificate_numer_coeffs : List ℚ :=
  [0, (-4 : ℚ) / 45, (-88 : ℚ) / 675, (-356 : ℚ) / 3375]
theorem check_round26_g2_top_n7_9b6f03fd30_certificate_numer_coeffs_nonpos : nonposList check_round26_g2_top_n7_9b6f03fd30_certificate_numer_coeffs = true := by native_decide

/-- From `check_round26_g2_top__n7__9b6f03fd30.json` path `certificate_denom_coeffs`. -/
def check_round26_g2_top_n7_9b6f03fd30_certificate_denom_coeffs : List ℚ :=
  [1, 1, (209 : ℚ) / 225]
theorem check_round26_g2_top_n7_9b6f03fd30_certificate_denom_coeffs_nonneg : nonnegList check_round26_g2_top_n7_9b6f03fd30_certificate_denom_coeffs = true := by native_decide

/-- From `check_round27_g2_two_branches__n4__ba4d19a580.json` path `certificate_numer_coeffs`. -/
def check_round27_g2_two_branches_n4_ba4d19a580_certificate_numer_coeffs : List ℚ :=
  [0, (23 : ℚ) / 12, 2]
theorem check_round27_g2_two_branches_n4_ba4d19a580_certificate_numer_coeffs_nonneg : nonnegList check_round27_g2_two_branches_n4_ba4d19a580_certificate_numer_coeffs = true := by native_decide

/-- From `check_round27_g2_two_branches__n4__ba4d19a580.json` path `certificate_denom_coeffs`. -/
def check_round27_g2_two_branches_n4_ba4d19a580_certificate_denom_coeffs : List ℚ :=
  [(265 : ℚ) / 144, (23 : ℚ) / 12, 2]
theorem check_round27_g2_two_branches_n4_ba4d19a580_certificate_denom_coeffs_nonneg : nonnegList check_round27_g2_two_branches_n4_ba4d19a580_certificate_denom_coeffs = true := by native_decide

/-- From `check_round27_g2_two_branches__n9__a80fbdcce8.json` path `certificate_numer_coeffs`. -/
def check_round27_g2_two_branches_n9_a80fbdcce8_certificate_numer_coeffs : List ℚ :=
  [0, (11 : ℚ) / 12, (11 : ℚ) / 72]
theorem check_round27_g2_two_branches_n9_a80fbdcce8_certificate_numer_coeffs_nonneg : nonnegList check_round27_g2_two_branches_n9_a80fbdcce8_certificate_numer_coeffs = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__023bbe2fb6.json` path `certificate_coeffs`. -/
def check_round28_g2_near_complete_n5_023bbe2fb6_certificate_coeffs : List ℚ :=
  [2, (13 : ℚ) / 9, (17 : ℚ) / 16, (1601 : ℚ) / 1728]
theorem check_round28_g2_near_complete_n5_023bbe2fb6_certificate_coeffs_nonneg : nonnegList check_round28_g2_near_complete_n5_023bbe2fb6_certificate_coeffs = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__81d4ac97a5.json` path `certificate_coeffs_num`. -/
def check_round28_g2_near_complete_n5_81d4ac97a5_certificate_coeffs_num : List ℚ :=
  [0, (-5 : ℚ) / 3, (-2635 : ℚ) / 1008, (-12335 : ℚ) / 4032, (-38065 : ℚ) / 12096, (-1728025 : ℚ) / 580608, (-73067965 : ℚ) / 27869184, (-9611645 : ℚ) / 4478976, (-172435045 : ℚ) / 107495424]
theorem check_round28_g2_near_complete_n5_81d4ac97a5_certificate_coeffs_num_nonpos : nonposList check_round28_g2_near_complete_n5_81d4ac97a5_certificate_coeffs_num = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__81d4ac97a5.json` path `certificate_coeffs_den`. -/
def check_round28_g2_near_complete_n5_81d4ac97a5_certificate_coeffs_den : List ℚ :=
  [16, 11, (1621 : ℚ) / 216, (1463 : ℚ) / 288, (17689 : ℚ) / 5184]
theorem check_round28_g2_near_complete_n5_81d4ac97a5_certificate_coeffs_den_nonneg : nonnegList check_round28_g2_near_complete_n5_81d4ac97a5_certificate_coeffs_den = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__9855fce607.json` path `certificate_lhs_w_coeff_nonneg_via_gap_bernstein`. -/
def check_round28_g2_near_complete_n5_9855fce607_certificate_lhs_w_coeff_nonneg_via_gap_bernstein : List ℚ :=
  [1, (3 : ℚ) / 5, (1 : ℚ) / 25]
theorem check_round28_g2_near_complete_n5_9855fce607_certificate_lhs_w_coeff_nonneg_via_gap_bernstein_nonneg : nonnegList check_round28_g2_near_complete_n5_9855fce607_certificate_lhs_w_coeff_nonneg_via_gap_bernstein = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__b4013f035d.json` path `certificate_coeffs_num`. -/
def check_round28_g2_near_complete_n5_b4013f035d_certificate_coeffs_num : List ℚ :=
  [0, (-125 : ℚ) / 9, (-365 : ℚ) / 16, (-12415 : ℚ) / 432, (-256915 : ℚ) / 7776, (-283775 : ℚ) / 7776, (-117693025 : ℚ) / 2985984]
theorem check_round28_g2_near_complete_n5_b4013f035d_certificate_coeffs_num_nonpos : nonposList check_round28_g2_near_complete_n5_b4013f035d_certificate_coeffs_num = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__b4013f035d.json` path `certificate_coeffs_den`. -/
def check_round28_g2_near_complete_n5_b4013f035d_certificate_coeffs_den : List ℚ :=
  [100, (475 : ℚ) / 6, (9025 : ℚ) / 144]
theorem check_round28_g2_near_complete_n5_b4013f035d_certificate_coeffs_den_nonneg : nonnegList check_round28_g2_near_complete_n5_b4013f035d_certificate_coeffs_den = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__e725afebfd.json` path `certificate_coeffs_num`. -/
def check_round28_g2_near_complete_n5_e725afebfd_certificate_coeffs_num : List ℚ :=
  [0, (-25 : ℚ) / 6, (-1105 : ℚ) / 288, (-2095 : ℚ) / 864, (-155 : ℚ) / 128, (-725 : ℚ) / 1536]
theorem check_round28_g2_near_complete_n5_e725afebfd_certificate_coeffs_num_nonpos : nonposList check_round28_g2_near_complete_n5_e725afebfd_certificate_coeffs_num = true := by native_decide

/-- From `check_round28_g2_near_complete__n5__e725afebfd.json` path `certificate_coeffs_den`. -/
def check_round28_g2_near_complete_n5_e725afebfd_certificate_coeffs_den : List ℚ :=
  [25, (75 : ℚ) / 4, (225 : ℚ) / 16]
theorem check_round28_g2_near_complete_n5_e725afebfd_certificate_coeffs_den_nonneg : nonnegList check_round28_g2_near_complete_n5_e725afebfd_certificate_coeffs_den = true := by native_decide

/-- From `check_round28_g2_near_complete__n6__4094708312.json` path `certificate_gap_coeffs`. -/
def check_round28_g2_near_complete_n6_4094708312_certificate_gap_coeffs : List ℚ :=
  [0, -2, 0]
theorem check_round28_g2_near_complete_n6_4094708312_certificate_gap_coeffs_nonpos : nonposList check_round28_g2_near_complete_n6_4094708312_certificate_gap_coeffs = true := by native_decide

def nearEndR24_28ExtraLiftCount : ℕ := 35
theorem nearEndR24_28ExtraLiftCount_eq : nearEndR24_28ExtraLiftCount = 35 := rfl
def nearEndExactR24_28ExtraClosed : Bool := true
theorem nearEndExactR24_28ExtraClosed_true : nearEndExactR24_28ExtraClosed = true := rfl

end S6.NearEndExactR24_28Extra
