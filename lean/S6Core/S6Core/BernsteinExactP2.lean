import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Exact-cert lifts — P2

Named Bernstein families (coeff vectors from JSON).
Supports componentwise ≥0 or ≤0 payloads (gaps often use ≤0 Bernstein forms).

Honest: payload-side `native_decide` only; **not** PrincipalClaim unconditional.
-/

namespace S6.BernsteinExactP2

def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

def nonposList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (c ≤ 0) && nonposList cs

def posList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 < c) && posList cs


/-- P2 `check_round24_g3_fside__n5__cbecdd171f.json` / check_round24_g3_fside n=5 / exact-Bernstein-minw / f_coeffs -/
def check_round24_g3_fside_n5_cbecdd171f_f_coeffs : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (17 : ℚ)/25]
theorem check_round24_g3_fside_n5_cbecdd171f_f_coeffs_pos : posList check_round24_g3_fside_n5_cbecdd171f_f_coeffs = true := by
  native_decide

/-- P2 `check_round24_g3_fside__n5__cbecdd171f.json` / check_round24_g3_fside n=5 / exact-Bernstein-minw / witness_coeffs -/
def check_round24_g3_fside_n5_cbecdd171f_witness_coeffs : List ℚ :=
  [(0 : ℚ), (4 : ℚ)/45, (28 : ℚ)/225, (8 : ℚ)/375]
theorem check_round24_g3_fside_n5_cbecdd171f_witness_coeffs_nonneg : nonnegList check_round24_g3_fside_n5_cbecdd171f_witness_coeffs = true := by
  native_decide

/-- P2 `check_round24_g3_fside__n7__ce41334842.json` / check_round24_g3_fside n=7 / exact-Bernstein-bvv / numer_coeffs -/
def check_round24_g3_fside_n7_ce41334842_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (4 : ℚ), (2 : ℚ), (12 : ℚ), (8 : ℚ)]
theorem check_round24_g3_fside_n7_ce41334842_numer_coeffs_nonneg : nonnegList check_round24_g3_fside_n7_ce41334842_numer_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n5__d1f1497dfb.json` / check_round25_g3_complete n=5 / exact-Bernstein-minw / f_coeffs -/
def check_round25_g3_complete_n5_d1f1497dfb_f_coeffs : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (193 : ℚ)/225]
theorem check_round25_g3_complete_n5_d1f1497dfb_f_coeffs_pos : posList check_round25_g3_complete_n5_d1f1497dfb_f_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n5__d1f1497dfb.json` / check_round25_g3_complete n=5 / exact-Bernstein-minw / witness_coeffs -/
def check_round25_g3_complete_n5_d1f1497dfb_witness_coeffs : List ℚ :=
  [(0 : ℚ), (4 : ℚ)/135, (8 : ℚ)/225, (52 : ℚ)/10125]
theorem check_round25_g3_complete_n5_d1f1497dfb_witness_coeffs_nonneg : nonnegList check_round25_g3_complete_n5_d1f1497dfb_witness_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n5__e43d6cfe6c.json` / check_round25_g3_complete n=5 / exact-Bernstein-minw / f_coeffs -/
def check_round25_g3_complete_n5_e43d6cfe6c_f_coeffs : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (17 : ℚ)/25]
theorem check_round25_g3_complete_n5_e43d6cfe6c_f_coeffs_pos : posList check_round25_g3_complete_n5_e43d6cfe6c_f_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n5__e43d6cfe6c.json` / check_round25_g3_complete n=5 / exact-Bernstein-minw / witness_coeffs -/
def check_round25_g3_complete_n5_e43d6cfe6c_witness_coeffs : List ℚ :=
  [(0 : ℚ), (4 : ℚ)/45, (28 : ℚ)/225, (8 : ℚ)/375]
theorem check_round25_g3_complete_n5_e43d6cfe6c_witness_coeffs_nonneg : nonnegList check_round25_g3_complete_n5_e43d6cfe6c_witness_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n8__12ea6e3a3d.json` / check_round25_g3_complete n=8 / exact-Bernstein-g25-chord / numer_coeffs -/
def check_round25_g3_complete_n8_12ea6e3a3d_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (16 : ℚ)/75, (48 : ℚ)/125, (224 : ℚ)/625]
theorem check_round25_g3_complete_n8_12ea6e3a3d_numer_coeffs_nonneg : nonnegList check_round25_g3_complete_n8_12ea6e3a3d_numer_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n8__12ea6e3a3d.json` / check_round25_g3_complete n=8 / exact-Bernstein-g25-chord / denom_coeffs -/
def check_round25_g3_complete_n8_12ea6e3a3d_denom_coeffs : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (79 : ℚ)/75, (29 : ℚ)/25, (841 : ℚ)/625]
theorem check_round25_g3_complete_n8_12ea6e3a3d_denom_coeffs_pos : posList check_round25_g3_complete_n8_12ea6e3a3d_denom_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n8__aa4c338fcf.json` / check_round25_g3_complete n=8 / exact-Bernstein-g25-S4U / numer_coeffs -/
def check_round25_g3_complete_n8_aa4c338fcf_numer_coeffs : List ℚ :=
  [(0 : ℚ), (1 : ℚ)/2, (0 : ℚ)]
theorem check_round25_g3_complete_n8_aa4c338fcf_numer_coeffs_nonneg : nonnegList check_round25_g3_complete_n8_aa4c338fcf_numer_coeffs = true := by
  native_decide

/-- P2 `check_round25_g3_complete__n8__aa4c338fcf.json` / check_round25_g3_complete n=8 / exact-Bernstein-g25-S4U / denom_coeffs -/
def check_round25_g3_complete_n8_aa4c338fcf_denom_coeffs : List ℚ :=
  [(1 : ℚ), (2 : ℚ)]
theorem check_round25_g3_complete_n8_aa4c338fcf_denom_coeffs_pos : posList check_round25_g3_complete_n8_aa4c338fcf_denom_coeffs = true := by
  native_decide

/-- P2 `check_round26_g2_top__n7__44d9df748d.json` / check_round26_g2_top n=7 / exact-Bernstein-r26-ld / numer_coeffs -/
def check_round26_g2_top_n7_44d9df748d_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (5 : ℚ)/18, (5 : ℚ)/21, (95 : ℚ)/216, (65 : ℚ)/189, (85 : ℚ)/432, (85 : ℚ)/3024]
theorem check_round26_g2_top_n7_44d9df748d_numer_coeffs_nonneg : nonnegList check_round26_g2_top_n7_44d9df748d_numer_coeffs = true := by
  native_decide

/-- P2 `check_round26_g2_top__n7__44d9df748d.json` / check_round26_g2_top n=7 / exact-Bernstein-r26-ld / denom_coeffs -/
def check_round26_g2_top_n7_44d9df748d_denom_coeffs : List ℚ :=
  [(1 : ℚ), (41 : ℚ)/36, (527 : ℚ)/432, (2023 : ℚ)/1728]
theorem check_round26_g2_top_n7_44d9df748d_denom_coeffs_pos : posList check_round26_g2_top_n7_44d9df748d_denom_coeffs = true := by
  native_decide

/-- P2 `check_round26_g2_top__n7__69e7323738.json` / check_round26_g2_top n=7 / exact-Bernstein-bvv / numer_coeffs -/
def check_round26_g2_top_n7_69e7323738_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (4 : ℚ), (2 : ℚ), (12 : ℚ), (8 : ℚ)]
theorem check_round26_g2_top_n7_69e7323738_numer_coeffs_nonneg : nonnegList check_round26_g2_top_n7_69e7323738_numer_coeffs = true := by
  native_decide

/-- P2 `check_round26_g2_top__n7__7905cebf07.json` / check_round26_g2_top n=7 / exact-Bernstein-r26-ld / numer_coeffs -/
def check_round26_g2_top_n7_7905cebf07_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (5 : ℚ)/18, (5 : ℚ)/21, (95 : ℚ)/216, (65 : ℚ)/189, (85 : ℚ)/432, (85 : ℚ)/3024]
theorem check_round26_g2_top_n7_7905cebf07_numer_coeffs_nonneg : nonnegList check_round26_g2_top_n7_7905cebf07_numer_coeffs = true := by
  native_decide

/-- P2 `check_round26_g2_top__n7__7905cebf07.json` / check_round26_g2_top n=7 / exact-Bernstein-r26-ld / denom_coeffs -/
def check_round26_g2_top_n7_7905cebf07_denom_coeffs : List ℚ :=
  [(1 : ℚ), (41 : ℚ)/36, (527 : ℚ)/432, (2023 : ℚ)/1728]
theorem check_round26_g2_top_n7_7905cebf07_denom_coeffs_pos : posList check_round26_g2_top_n7_7905cebf07_denom_coeffs = true := by
  native_decide

/-- P2 `check_round26_g2_top__n7__9b6f03fd30.json` / check_round26_g2_top n=7 / exact-Bernstein-r26-L3U2 / numer_coeffs -/
def check_round26_g2_top_n7_9b6f03fd30_numer_coeffs : List ℚ :=
  [(0 : ℚ), (-4 : ℚ)/45, (-88 : ℚ)/675, (-356 : ℚ)/3375]
theorem check_round26_g2_top_n7_9b6f03fd30_numer_coeffs_nonpos : nonposList check_round26_g2_top_n7_9b6f03fd30_numer_coeffs = true := by
  native_decide

/-- P2 `check_round26_g2_top__n7__9b6f03fd30.json` / check_round26_g2_top n=7 / exact-Bernstein-r26-L3U2 / denom_coeffs -/
def check_round26_g2_top_n7_9b6f03fd30_denom_coeffs : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (209 : ℚ)/225]
theorem check_round26_g2_top_n7_9b6f03fd30_denom_coeffs_pos : posList check_round26_g2_top_n7_9b6f03fd30_denom_coeffs = true := by
  native_decide

/-- P2 `check_round27_g2_two_branches__n9__a80fbdcce8.json` / check_round27_g2_two_branches n=9 / exact-Bernstein-hw11 / numer_coeffs -/
def check_round27_g2_two_branches_n9_a80fbdcce8_numer_coeffs : List ℚ :=
  [(0 : ℚ), (11 : ℚ)/12, (11 : ℚ)/72]
theorem check_round27_g2_two_branches_n9_a80fbdcce8_numer_coeffs_nonneg : nonnegList check_round27_g2_two_branches_n9_a80fbdcce8_numer_coeffs = true := by
  native_decide

/-- P2 `check_round28_g2_near_complete__n5__023bbe2fb6.json` / check_round28_g2_near_complete n=5 / exact-Bernstein-tt-2w / coeffs -/
def check_round28_g2_near_complete_n5_023bbe2fb6_coeffs : List ℚ :=
  [(2 : ℚ), (13 : ℚ)/9, (17 : ℚ)/16, (1601 : ℚ)/1728]
theorem check_round28_g2_near_complete_n5_023bbe2fb6_coeffs_pos : posList check_round28_g2_near_complete_n5_023bbe2fb6_coeffs = true := by
  native_decide

/-- P2 `check_round28_g2_near_complete__n5__81d4ac97a5.json` / check_round28_g2_near_complete n=5 / exact-Bernstein-tt-square-gap-endpoint / coeffs_num -/
def check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_num : List ℚ :=
  [(0 : ℚ), (-5 : ℚ)/3, (-2635 : ℚ)/1008, (-12335 : ℚ)/4032, (-38065 : ℚ)/12096, (-1728025 : ℚ)/580608, (-73067965 : ℚ)/27869184, (-9611645 : ℚ)/4478976, (-172435045 : ℚ)/107495424]
theorem check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_num_nonpos : nonposList check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_num = true := by
  native_decide

/-- P2 `check_round28_g2_near_complete__n5__81d4ac97a5.json` / check_round28_g2_near_complete n=5 / exact-Bernstein-tt-square-gap-endpoint / coeffs_den -/
def check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_den : List ℚ :=
  [(16 : ℚ), (11 : ℚ), (1621 : ℚ)/216, (1463 : ℚ)/288, (17689 : ℚ)/5184]
theorem check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_den_pos : posList check_round28_g2_near_complete_n5_81d4ac97a5_coeffs_den = true := by
  native_decide

/-- P2 `check_round28_g2_near_complete__n5__b4013f035d.json` / check_round28_g2_near_complete n=5 / exact-Bernstein-tt-square-gap-endpoint / coeffs_num -/
def check_round28_g2_near_complete_n5_b4013f035d_coeffs_num : List ℚ :=
  [(0 : ℚ), (-125 : ℚ)/9, (-365 : ℚ)/16, (-12415 : ℚ)/432, (-256915 : ℚ)/7776, (-283775 : ℚ)/7776, (-117693025 : ℚ)/2985984]
theorem check_round28_g2_near_complete_n5_b4013f035d_coeffs_num_nonpos : nonposList check_round28_g2_near_complete_n5_b4013f035d_coeffs_num = true := by
  native_decide

/-- P2 `check_round28_g2_near_complete__n5__b4013f035d.json` / check_round28_g2_near_complete n=5 / exact-Bernstein-tt-square-gap-endpoint / coeffs_den -/
def check_round28_g2_near_complete_n5_b4013f035d_coeffs_den : List ℚ :=
  [(100 : ℚ), (475 : ℚ)/6, (9025 : ℚ)/144]
theorem check_round28_g2_near_complete_n5_b4013f035d_coeffs_den_pos : posList check_round28_g2_near_complete_n5_b4013f035d_coeffs_den = true := by
  native_decide

/-- P2 `check_round28_g2_near_complete__n5__e725afebfd.json` / check_round28_g2_near_complete n=5 / exact-Bernstein-tt-square-gap-endpoint / coeffs_num -/
def check_round28_g2_near_complete_n5_e725afebfd_coeffs_num : List ℚ :=
  [(0 : ℚ), (-25 : ℚ)/6, (-1105 : ℚ)/288, (-2095 : ℚ)/864, (-155 : ℚ)/128, (-725 : ℚ)/1536]
theorem check_round28_g2_near_complete_n5_e725afebfd_coeffs_num_nonpos : nonposList check_round28_g2_near_complete_n5_e725afebfd_coeffs_num = true := by
  native_decide

/-- P2 `check_round28_g2_near_complete__n5__e725afebfd.json` / check_round28_g2_near_complete n=5 / exact-Bernstein-tt-square-gap-endpoint / coeffs_den -/
def check_round28_g2_near_complete_n5_e725afebfd_coeffs_den : List ℚ :=
  [(25 : ℚ), (75 : ℚ)/4, (225 : ℚ)/16]
theorem check_round28_g2_near_complete_n5_e725afebfd_coeffs_den_pos : posList check_round28_g2_near_complete_n5_e725afebfd_coeffs_den = true := by
  native_decide

/-- P2 `check_round33_right_nonempty__n7__db06194097.json` / check_round33_right_nonempty n=7 / exact-Bernstein-S1S2-rho / numer_coeffs -/
def check_round33_right_nonempty_n7_db06194097_numer_coeffs : List ℚ :=
  [(0 : ℚ)]
theorem check_round33_right_nonempty_n7_db06194097_numer_coeffs_nonneg : nonnegList check_round33_right_nonempty_n7_db06194097_numer_coeffs = true := by
  native_decide

/-- P2 `check_round34_left_negative__n5__4b2f2e740a.json` / check_round34_left_negative n=5 / exact-Bernstein-halfangle-square / coeffs -/
def check_round34_left_negative_n5_4b2f2e740a_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 : ℚ)/12, (-1 : ℚ)/12, (0 : ℚ), (-3 : ℚ)/16, (-1 : ℚ)/4]
theorem check_round34_left_negative_n5_4b2f2e740a_coeffs_nonpos : nonposList check_round34_left_negative_n5_4b2f2e740a_coeffs = true := by
  native_decide

/-- P2 `check_round34_left_negative__n5__94dd9628c0.json` / check_round34_left_negative n=5 / exact-Bernstein-halfangle-square / coeffs -/
def check_round34_left_negative_n5_94dd9628c0_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1 : ℚ)/12, (-1 : ℚ)/12, (0 : ℚ), (-3 : ℚ)/16, (-1 : ℚ)/4]
theorem check_round34_left_negative_n5_94dd9628c0_coeffs_nonpos : nonposList check_round34_left_negative_n5_94dd9628c0_coeffs = true := by
  native_decide

/-- P2 `check_round34_left_negative__n7__b3fc127936.json` / check_round34_left_negative n=7 / exact-Bernstein-ru-cwsw / numer_coeffs -/
def check_round34_left_negative_n7_b3fc127936_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (1 : ℚ)/3, (0 : ℚ), (0 : ℚ)]
theorem check_round34_left_negative_n7_b3fc127936_numer_coeffs_nonneg : nonnegList check_round34_left_negative_n7_b3fc127936_numer_coeffs = true := by
  native_decide

/-- P2 `check_round34_left_negative__n9__354010980c.json` / check_round34_left_negative n=9 / exact-Bernstein-eta-z-r / numer_coeffs -/
def check_round34_left_negative_n9_354010980c_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-439040 : ℚ), (-415520 : ℚ), (-392000 : ℚ), (-368480 : ℚ), (-878080 : ℚ), (-733040 : ℚ), (-588000 : ℚ), (-442960 : ℚ), (-1317120 : ℚ), (-952560 : ℚ), (-609000 : ℚ), (-296565 : ℚ), (-1756160 : ℚ), (-1074080 : ℚ), (-476000 : ℚ), (-53045 : ℚ)]
theorem check_round34_left_negative_n9_354010980c_numer_coeffs_nonpos : nonposList check_round34_left_negative_n9_354010980c_numer_coeffs = true := by
  native_decide

/-- P2 `check_round35_positive_H__n6__934f6ba957.json` / check_round35_positive_H n=6 / exact-Bernstein-A-L2 / numer_coeffs -/
def check_round35_positive_H_n6_934f6ba957_numer_coeffs : List ℚ :=
  [(0 : ℚ)]
theorem check_round35_positive_H_n6_934f6ba957_numer_coeffs_nonneg : nonnegList check_round35_positive_H_n6_934f6ba957_numer_coeffs = true := by
  native_decide

/-- P2 `check_round35_positive_H__n6__934f6ba957.json` / check_round35_positive_H n=6 / exact-Bernstein-A-L2 / denom_coeffs -/
def check_round35_positive_H_n6_934f6ba957_denom_coeffs : List ℚ :=
  [(1 : ℚ)]
theorem check_round35_positive_H_n6_934f6ba957_denom_coeffs_pos : posList check_round35_positive_H_n6_934f6ba957_denom_coeffs = true := by
  native_decide

/-- P2 `check_round36_nonempty_closed__n5__1be048b695.json` / check_round36_nonempty_closed n=5 / exact-Bernstein-r36-halfangle / numer_coeffs -/
def check_round36_nonempty_closed_n5_1be048b695_numer_coeffs : List ℚ :=
  [(0 : ℚ), (3 : ℚ)/2, (0 : ℚ), (0 : ℚ), (2 : ℚ)/3, (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
theorem check_round36_nonempty_closed_n5_1be048b695_numer_coeffs_nonneg : nonnegList check_round36_nonempty_closed_n5_1be048b695_numer_coeffs = true := by
  native_decide

/-- P2 `check_round36_nonempty_closed__n5__1be048b695.json` / check_round36_nonempty_closed n=5 / exact-Bernstein-r36-halfangle / denom_coeffs -/
def check_round36_nonempty_closed_n5_1be048b695_denom_coeffs : List ℚ :=
  [(2 : ℚ), (5 : ℚ)/2, (2 : ℚ), (10 : ℚ)/3, (11 : ℚ)/3, (10 : ℚ)/3, (16 : ℚ)/3, (16 : ℚ)/3, (16 : ℚ)/3, (8 : ℚ), (8 : ℚ), (8 : ℚ)]
theorem check_round36_nonempty_closed_n5_1be048b695_denom_coeffs_pos : posList check_round36_nonempty_closed_n5_1be048b695_denom_coeffs = true := by
  native_decide

/-- P2 `check_round36_nonempty_closed__n6__068a36fcc7.json` / check_round36_nonempty_closed n=6 / exact-Bernstein-Sigma-gap / numer_coeffs -/
def check_round36_nonempty_closed_n6_068a36fcc7_numer_coeffs : List ℚ :=
  [(0 : ℚ), (-1 : ℚ)/2, (0 : ℚ)]
theorem check_round36_nonempty_closed_n6_068a36fcc7_numer_coeffs_nonpos : nonposList check_round36_nonempty_closed_n6_068a36fcc7_numer_coeffs = true := by
  native_decide

/-- P2 `check_round36_nonempty_closed__n6__068a36fcc7.json` / check_round36_nonempty_closed n=6 / exact-Bernstein-Sigma-gap / denom_coeffs -/
def check_round36_nonempty_closed_n6_068a36fcc7_denom_coeffs : List ℚ :=
  [(1 : ℚ), (2 : ℚ)]
theorem check_round36_nonempty_closed_n6_068a36fcc7_denom_coeffs_pos : posList check_round36_nonempty_closed_n6_068a36fcc7_denom_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n6__d76911a30a.json` / check_round38_empty_right_negative n=6 / exact-Bernstein-cleared / numer_coeffs -/
def check_round38_empty_right_negative_n6_d76911a30a_numer_coeffs : List ℚ :=
  [(0 : ℚ), (1 : ℚ)/2, (0 : ℚ)]
theorem check_round38_empty_right_negative_n6_d76911a30a_numer_coeffs_nonneg : nonnegList check_round38_empty_right_negative_n6_d76911a30a_numer_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n6__d76911a30a.json` / check_round38_empty_right_negative n=6 / exact-Bernstein-cleared / denom_coeffs -/
def check_round38_empty_right_negative_n6_d76911a30a_denom_coeffs : List ℚ :=
  [(1 : ℚ)]
theorem check_round38_empty_right_negative_n6_d76911a30a_denom_coeffs_pos : posList check_round38_empty_right_negative_n6_d76911a30a_denom_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n7__4fa680734e.json` / check_round38_empty_right_negative n=7 / exact-Bernstein-z-d-eta / numer_coeffs -/
def check_round38_empty_right_negative_n7_4fa680734e_numer_coeffs : List ℚ :=
  [(0 : ℚ)]
theorem check_round38_empty_right_negative_n7_4fa680734e_numer_coeffs_nonneg : nonnegList check_round38_empty_right_negative_n7_4fa680734e_numer_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n7__4fa680734e.json` / check_round38_empty_right_negative n=7 / exact-Bernstein-z-d-eta / denom_coeffs -/
def check_round38_empty_right_negative_n7_4fa680734e_denom_coeffs : List ℚ :=
  [(1 : ℚ)]
theorem check_round38_empty_right_negative_n7_4fa680734e_denom_coeffs_pos : posList check_round38_empty_right_negative_n7_4fa680734e_denom_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n9__68193379b7.json` / check_round38_empty_right_negative n=9 / exact-Bernstein-or-eta-d / branch2_numer_coeffs -/
def check_round38_empty_right_negative_n9_68193379b7_branch2_numer_coeffs : List ℚ :=
  [(0 : ℚ), (-2 : ℚ)]
theorem check_round38_empty_right_negative_n9_68193379b7_branch2_numer_coeffs_nonpos : nonposList check_round38_empty_right_negative_n9_68193379b7_branch2_numer_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n9__68193379b7.json` / check_round38_empty_right_negative n=9 / exact-Bernstein-or-eta-d / branch2_denom_coeffs -/
def check_round38_empty_right_negative_n9_68193379b7_branch2_denom_coeffs : List ℚ :=
  [(5929 : ℚ)/60, (1001 : ℚ)/10]
theorem check_round38_empty_right_negative_n9_68193379b7_branch2_denom_coeffs_pos : posList check_round38_empty_right_negative_n9_68193379b7_branch2_denom_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n9__68193379b7.json` / check_round38_empty_right_negative n=9 / exact-Bernstein-or-eta-d / branch1_numer_coeffs -/
def check_round38_empty_right_negative_n9_68193379b7_branch1_numer_coeffs : List ℚ :=
  [(83521 : ℚ)/3600, (6613 : ℚ)/200, (4301 : ℚ)/100]
theorem check_round38_empty_right_negative_n9_68193379b7_branch1_numer_coeffs_pos : posList check_round38_empty_right_negative_n9_68193379b7_branch1_numer_coeffs = true := by
  native_decide

/-- P2 `check_round38_empty_right_negative__n9__68193379b7.json` / check_round38_empty_right_negative n=9 / exact-Bernstein-or-eta-d / branch1_denom_coeffs -/
def check_round38_empty_right_negative_n9_68193379b7_branch1_denom_coeffs : List ℚ :=
  [(254947 : ℚ)/240, (42273 : ℚ)/40, (21021 : ℚ)/20]
theorem check_round38_empty_right_negative_n9_68193379b7_branch1_denom_coeffs_pos : posList check_round38_empty_right_negative_n9_68193379b7_branch1_denom_coeffs = true := by
  native_decide

/-- P2 `check_round39_single_contact__n7__60049c9a90.json` / check_round39_single_contact n=7 / exact-Bernstein-bvv / numer_coeffs -/
def check_round39_single_contact_n7_60049c9a90_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (4 : ℚ), (2 : ℚ), (12 : ℚ), (8 : ℚ)]
theorem check_round39_single_contact_n7_60049c9a90_numer_coeffs_nonneg : nonnegList check_round39_single_contact_n7_60049c9a90_numer_coeffs = true := by
  native_decide

/-- P2 `check_round39_single_contact__n9__067364b4bc.json` / check_round39_single_contact n=9 / exact-Bernstein-bv-product / numer_coeffs -/
def check_round39_single_contact_n9_067364b4bc_numer_coeffs : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (3 : ℚ), (6 : ℚ)/5, (51 : ℚ)/50, (14 : ℚ), (34 : ℚ)/5, (71 : ℚ)/25]
theorem check_round39_single_contact_n9_067364b4bc_numer_coeffs_nonneg : nonnegList check_round39_single_contact_n9_067364b4bc_numer_coeffs = true := by
  native_decide

def p2LiftCount : ℕ := 28
theorem p2LiftCount_eq : p2LiftCount = 28 := rfl
def p2TheoremCount : ℕ := 47
theorem p2TheoremCount_eq : p2TheoremCount = 47 := rfl
def bernsteinExactP2Closed : Bool := true
theorem bernsteinExactP2Closed_true : bernsteinExactP2Closed = true := rfl
def openStatus : String :=
  "CLOSED: P2 Bernstein coeff signs (nonneg/nonpos). Not PrincipalClaim."
end S6.BernsteinExactP2
