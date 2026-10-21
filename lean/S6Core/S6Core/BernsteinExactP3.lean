import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Exact-cert lifts — P3

IBB leaf contradiction ranges (rational endpoints).

Source: `artifacts/closure/item3_certs/exact_certs_batch24/`.
Honest: payload-side `native_decide` checks only; **not** PrincipalClaim unconditional.
-/

namespace S6.BernsteinExactP3

def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

def posList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 < c) && posList cs



def rangeNonpos (hi : ℚ) : Bool := decide (hi ≤ 0)
def rangeNonneg (lo : ℚ) : Bool := decide (0 ≤ lo)
def rangeNeg (hi : ℚ) : Bool := decide (hi < 0)
def rangePos (lo : ℚ) : Bool := decide (0 < lo)


/-- P3 `check_round28_g2_near_complete__n5__9855fce607.json` / check_round28_g2_near_complete n=5 / exact-IBB-r28-hw-maxw -/
def check_round28_g2_near_complete_n5_9855fce607_leaf0_lo : ℚ := (-11 : ℚ)
def check_round28_g2_near_complete_n5_9855fce607_leaf0_hi : ℚ := (-874 : ℚ)/625
theorem check_round28_g2_near_complete_n5_9855fce607_leaf0_range_neg : rangeNeg check_round28_g2_near_complete_n5_9855fce607_leaf0_hi = true := by native_decide

def check_round28_g2_near_complete_n5_9855fce607_leaf1_lo : ℚ := (-5579 : ℚ)/625
def check_round28_g2_near_complete_n5_9855fce607_leaf1_hi : ℚ := (-583 : ℚ)/625
theorem check_round28_g2_near_complete_n5_9855fce607_leaf1_range_neg : rangeNeg check_round28_g2_near_complete_n5_9855fce607_leaf1_hi = true := by native_decide

/-- P3 `check_round32_right_positive__n8__78a5a46ff1.json` / check_round32_right_positive n=8 / exact-IBB-triangle3 -/
def check_round32_right_positive_n8_78a5a46ff1_leaf0_lo : ℚ := (0 : ℚ)
def check_round32_right_positive_n8_78a5a46ff1_leaf0_hi : ℚ := (1 : ℚ)
theorem check_round32_right_positive_n8_78a5a46ff1_leaf0_range_nonneg : rangeNonneg check_round32_right_positive_n8_78a5a46ff1_leaf0_lo = true := by native_decide

/-- P3 `check_round33_right_nonempty__n12__05c3f3a323.json` / check_round33_right_nonempty n=12 / exact-IBB-triangle3 -/
def check_round33_right_nonempty_n12_05c3f3a323_leaf0_lo : ℚ := (0 : ℚ)
def check_round33_right_nonempty_n12_05c3f3a323_leaf0_hi : ℚ := (8 : ℚ)/3
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf0_range_nonneg : rangeNonneg check_round33_right_nonempty_n12_05c3f3a323_leaf0_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf1_lo : ℚ := (0 : ℚ)
def check_round33_right_nonempty_n12_05c3f3a323_leaf1_hi : ℚ := (1 : ℚ)
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf1_range_nonneg : rangeNonneg check_round33_right_nonempty_n12_05c3f3a323_leaf1_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf2_lo : ℚ := (0 : ℚ)
def check_round33_right_nonempty_n12_05c3f3a323_leaf2_hi : ℚ := (315 : ℚ)/247
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf2_range_nonneg : rangeNonneg check_round33_right_nonempty_n12_05c3f3a323_leaf2_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf3_lo : ℚ := (1 : ℚ)/16
def check_round33_right_nonempty_n12_05c3f3a323_leaf3_hi : ℚ := (1 : ℚ)/2
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf3_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf3_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf4_lo : ℚ := (0 : ℚ)
def check_round33_right_nonempty_n12_05c3f3a323_leaf4_hi : ℚ := (247 : ℚ)/192
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf4_range_nonneg : rangeNonneg check_round33_right_nonempty_n12_05c3f3a323_leaf4_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf5_lo : ℚ := (1 : ℚ)/8
def check_round33_right_nonempty_n12_05c3f3a323_leaf5_hi : ℚ := (1 : ℚ)/2
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf5_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf5_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf6_lo : ℚ := (1 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf6_hi : ℚ := (13 : ℚ)/32
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf6_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf6_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf7_lo : ℚ := (1 : ℚ)/16
def check_round33_right_nonempty_n12_05c3f3a323_leaf7_hi : ℚ := (17 : ℚ)/64
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf7_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf7_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf8_lo : ℚ := (1 : ℚ)/64
def check_round33_right_nonempty_n12_05c3f3a323_leaf8_hi : ℚ := (27 : ℚ)/128
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf8_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf8_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf9_lo : ℚ := (1 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf9_hi : ℚ := (35 : ℚ)/256
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf9_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf9_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf10_lo : ℚ := (1 : ℚ)/128
def check_round33_right_nonempty_n12_05c3f3a323_leaf10_hi : ℚ := (55 : ℚ)/512
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf10_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf10_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf11_lo : ℚ := (16384 : ℚ)/333829
def check_round33_right_nonempty_n12_05c3f3a323_leaf11_hi : ℚ := (13627 : ℚ)/61440
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf11_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf11_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf12_lo : ℚ := (1 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf12_hi : ℚ := (103 : ℚ)/1024
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf12_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf12_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf13_lo : ℚ := (1 : ℚ)/16
def check_round33_right_nonempty_n12_05c3f3a323_leaf13_hi : ℚ := (51 : ℚ)/256
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf13_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf13_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf14_lo : ℚ := (1 : ℚ)/8
def check_round33_right_nonempty_n12_05c3f3a323_leaf14_hi : ℚ := (25 : ℚ)/64
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf14_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf14_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf15_lo : ℚ := (467 : ℚ)/1008
def check_round33_right_nonempty_n12_05c3f3a323_leaf15_hi : ℚ := (30 : ℚ)/11
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf15_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf15_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf16_lo : ℚ := (1 : ℚ)/64
def check_round33_right_nonempty_n12_05c3f3a323_leaf16_hi : ℚ := (3 : ℚ)/8
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf16_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf16_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf17_lo : ℚ := (107 : ℚ)/2664
def check_round33_right_nonempty_n12_05c3f3a323_leaf17_hi : ℚ := (27345 : ℚ)/30176
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf17_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf17_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf18_lo : ℚ := (3 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf18_hi : ℚ := (11 : ℚ)/32
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf18_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf18_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf19_lo : ℚ := (101 : ℚ)/8
def check_round33_right_nonempty_n12_05c3f3a323_leaf19_hi : ℚ := (53 : ℚ)/2
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf19_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf19_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf20_lo : ℚ := (3 : ℚ)/26
def check_round33_right_nonempty_n12_05c3f3a323_leaf20_hi : ℚ := (2829 : ℚ)/1408
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf20_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf20_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf21_lo : ℚ := (101 : ℚ)/8
def check_round33_right_nonempty_n12_05c3f3a323_leaf21_hi : ℚ := (53 : ℚ)/2
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf21_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf21_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf22_lo : ℚ := (2995 : ℚ)/15808
def check_round33_right_nonempty_n12_05c3f3a323_leaf22_hi : ℚ := (185 : ℚ)/321
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf22_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf22_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf23_lo : ℚ := (15 : ℚ)/256
def check_round33_right_nonempty_n12_05c3f3a323_leaf23_hi : ℚ := (3 : ℚ)/16
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf23_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf23_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf24_lo : ℚ := (20575 : ℚ)/251328
def check_round33_right_nonempty_n12_05c3f3a323_leaf24_hi : ℚ := (467815 : ℚ)/970176
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf24_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf24_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf25_lo : ℚ := (5 : ℚ)/128
def check_round33_right_nonempty_n12_05c3f3a323_leaf25_hi : ℚ := (11 : ℚ)/64
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf25_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf25_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf26_lo : ℚ := (91 : ℚ)/16
def check_round33_right_nonempty_n12_05c3f3a323_leaf26_hi : ℚ := (101 : ℚ)/8
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf26_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf26_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf27_lo : ℚ := (3 : ℚ)/64
def check_round33_right_nonempty_n12_05c3f3a323_leaf27_hi : ℚ := (5 : ℚ)/16
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf27_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf27_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf28_lo : ℚ := (90549 : ℚ)/2129920
def check_round33_right_nonempty_n12_05c3f3a323_leaf28_hi : ℚ := (706131 : ℚ)/1960910
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf28_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf28_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf29_lo : ℚ := (113675 : ℚ)/884224
def check_round33_right_nonempty_n12_05c3f3a323_leaf29_hi : ℚ := (9910683 : ℚ)/31221632
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf29_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf29_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf30_lo : ℚ := (9 : ℚ)/512
def check_round33_right_nonempty_n12_05c3f3a323_leaf30_hi : ℚ := (11 : ℚ)/128
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf30_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf30_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf31_lo : ℚ := (71 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf31_hi : ℚ := (91 : ℚ)/16
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf31_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf31_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf32_lo : ℚ := (5 : ℚ)/256
def check_round33_right_nonempty_n12_05c3f3a323_leaf32_hi : ℚ := (5 : ℚ)/32
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf32_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf32_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf33_lo : ℚ := (2542851 : ℚ)/31711232
def check_round33_right_nonempty_n12_05c3f3a323_leaf33_hi : ℚ := (425799 : ℚ)/1553176
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf33_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf33_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf34_lo : ℚ := (9 : ℚ)/1024
def check_round33_right_nonempty_n12_05c3f3a323_leaf34_hi : ℚ := (5 : ℚ)/64
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf34_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf34_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf35_lo : ℚ := (321 : ℚ)/10282
def check_round33_right_nonempty_n12_05c3f3a323_leaf35_hi : ℚ := (7113987 : ℚ)/30900224
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf35_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf35_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf36_lo : ℚ := (1 : ℚ)/64
def check_round33_right_nonempty_n12_05c3f3a323_leaf36_hi : ℚ := (9 : ℚ)/128
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf36_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf36_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf37_lo : ℚ := (31 : ℚ)/64
def check_round33_right_nonempty_n12_05c3f3a323_leaf37_hi : ℚ := (71 : ℚ)/32
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf37_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf37_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf38_lo : ℚ := (71 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf38_hi : ℚ := (91 : ℚ)/16
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf38_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf38_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf39_lo : ℚ := (1 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf39_hi : ℚ := (9 : ℚ)/64
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf39_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf39_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf40_lo : ℚ := (71 : ℚ)/32
def check_round33_right_nonempty_n12_05c3f3a323_leaf40_hi : ℚ := (91 : ℚ)/16
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf40_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf40_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf41_lo : ℚ := (91 : ℚ)/16
def check_round33_right_nonempty_n12_05c3f3a323_leaf41_hi : ℚ := (101 : ℚ)/8
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf41_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf41_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf42_lo : ℚ := (1 : ℚ)/16
def check_round33_right_nonempty_n12_05c3f3a323_leaf42_hi : ℚ := (9 : ℚ)/32
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf42_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf42_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf43_lo : ℚ := (91 : ℚ)/16
def check_round33_right_nonempty_n12_05c3f3a323_leaf43_hi : ℚ := (101 : ℚ)/8
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf43_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf43_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf44_lo : ℚ := (101 : ℚ)/8
def check_round33_right_nonempty_n12_05c3f3a323_leaf44_hi : ℚ := (53 : ℚ)/2
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf44_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf44_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf45_lo : ℚ := (0 : ℚ)
def check_round33_right_nonempty_n12_05c3f3a323_leaf45_hi : ℚ := (1 : ℚ)
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf45_range_nonneg : rangeNonneg check_round33_right_nonempty_n12_05c3f3a323_leaf45_lo = true := by native_decide

def check_round33_right_nonempty_n12_05c3f3a323_leaf46_lo : ℚ := (53 : ℚ)/2
def check_round33_right_nonempty_n12_05c3f3a323_leaf46_hi : ℚ := (82 : ℚ)
theorem check_round33_right_nonempty_n12_05c3f3a323_leaf46_range_pos : rangePos check_round33_right_nonempty_n12_05c3f3a323_leaf46_lo = true := by native_decide

/-- P3 `check_round33_right_nonempty__n13__46bade99ee.json` / check_round33_right_nonempty n=13 / exact-IBB-triangle3 -/
def check_round33_right_nonempty_n13_46bade99ee_leaf0_lo : ℚ := (0 : ℚ)
def check_round33_right_nonempty_n13_46bade99ee_leaf0_hi : ℚ := (62 : ℚ)/5
theorem check_round33_right_nonempty_n13_46bade99ee_leaf0_range_nonneg : rangeNonneg check_round33_right_nonempty_n13_46bade99ee_leaf0_lo = true := by native_decide

def check_round33_right_nonempty_n13_46bade99ee_leaf1_lo : ℚ := (0 : ℚ)
def check_round33_right_nonempty_n13_46bade99ee_leaf1_hi : ℚ := (1 : ℚ)
theorem check_round33_right_nonempty_n13_46bade99ee_leaf1_range_nonneg : rangeNonneg check_round33_right_nonempty_n13_46bade99ee_leaf1_lo = true := by native_decide

def check_round33_right_nonempty_n13_46bade99ee_leaf2_lo : ℚ := (43 : ℚ)/17
def check_round33_right_nonempty_n13_46bade99ee_leaf2_hi : ℚ := (76 : ℚ)/3
theorem check_round33_right_nonempty_n13_46bade99ee_leaf2_range_pos : rangePos check_round33_right_nonempty_n13_46bade99ee_leaf2_lo = true := by native_decide

/-- P3 `check_round34_left_negative__n8__5e19d78058.json` / check_round34_left_negative n=8 / exact-IBB-triangle3 -/
def check_round34_left_negative_n8_5e19d78058_leaf0_lo : ℚ := (3 : ℚ)/40
def check_round34_left_negative_n8_5e19d78058_leaf0_hi : ℚ := (1 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf0_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf0_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf1_lo : ℚ := (3 : ℚ)/40
def check_round34_left_negative_n8_5e19d78058_leaf1_hi : ℚ := (1 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf1_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf1_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf2_lo : ℚ := (5 : ℚ)/28
def check_round34_left_negative_n8_5e19d78058_leaf2_hi : ℚ := (15 : ℚ)/16
theorem check_round34_left_negative_n8_5e19d78058_leaf2_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf2_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf3_lo : ℚ := (1 : ℚ)/80
def check_round34_left_negative_n8_5e19d78058_leaf3_hi : ℚ := (41 : ℚ)/112
theorem check_round34_left_negative_n8_5e19d78058_leaf3_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf3_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf4_lo : ℚ := (1 : ℚ)/80
def check_round34_left_negative_n8_5e19d78058_leaf4_hi : ℚ := (75 : ℚ)/224
theorem check_round34_left_negative_n8_5e19d78058_leaf4_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf4_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf5_lo : ℚ := (21 : ℚ)/1280
def check_round34_left_negative_n8_5e19d78058_leaf5_hi : ℚ := (272 : ℚ)/365
theorem check_round34_left_negative_n8_5e19d78058_leaf5_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf5_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf6_lo : ℚ := (1 : ℚ)/4
def check_round34_left_negative_n8_5e19d78058_leaf6_hi : ℚ := (2 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf6_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf6_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf7_lo : ℚ := (1 : ℚ)/80
def check_round34_left_negative_n8_5e19d78058_leaf7_hi : ℚ := (1 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf7_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf7_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf8_lo : ℚ := (5 : ℚ)/28
def check_round34_left_negative_n8_5e19d78058_leaf8_hi : ℚ := (1 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf8_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf8_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf9_lo : ℚ := (3 : ℚ)/40
def check_round34_left_negative_n8_5e19d78058_leaf9_hi : ℚ := (3 : ℚ)/7
theorem check_round34_left_negative_n8_5e19d78058_leaf9_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf9_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf10_lo : ℚ := (41 : ℚ)/544
def check_round34_left_negative_n8_5e19d78058_leaf10_hi : ℚ := (75 : ℚ)/224
theorem check_round34_left_negative_n8_5e19d78058_leaf10_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf10_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf11_lo : ℚ := (23 : ℚ)/640
def check_round34_left_negative_n8_5e19d78058_leaf11_hi : ℚ := (109 : ℚ)/544
theorem check_round34_left_negative_n8_5e19d78058_leaf11_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf11_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf12_lo : ℚ := (95 : ℚ)/2368
def check_round34_left_negative_n8_5e19d78058_leaf12_hi : ℚ := (167 : ℚ)/1088
theorem check_round34_left_negative_n8_5e19d78058_leaf12_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf12_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf13_lo : ℚ := (17 : ℚ)/256
def check_round34_left_negative_n8_5e19d78058_leaf13_hi : ℚ := (1 : ℚ)/4
theorem check_round34_left_negative_n8_5e19d78058_leaf13_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf13_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf14_lo : ℚ := (29 : ℚ)/1184
def check_round34_left_negative_n8_5e19d78058_leaf14_hi : ℚ := (617 : ℚ)/4352
theorem check_round34_left_negative_n8_5e19d78058_leaf14_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf14_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf15_lo : ℚ := (17 : ℚ)/256
def check_round34_left_negative_n8_5e19d78058_leaf15_hi : ℚ := (1 : ℚ)/4
theorem check_round34_left_negative_n8_5e19d78058_leaf15_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf15_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf16_lo : ℚ := (3 : ℚ)/68
def check_round34_left_negative_n8_5e19d78058_leaf16_hi : ℚ := (143 : ℚ)/448
theorem check_round34_left_negative_n8_5e19d78058_leaf16_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf16_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf17_lo : ℚ := (1 : ℚ)/80
def check_round34_left_negative_n8_5e19d78058_leaf17_hi : ℚ := (201 : ℚ)/1088
theorem check_round34_left_negative_n8_5e19d78058_leaf17_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf17_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf18_lo : ℚ := (389 : ℚ)/30720
def check_round34_left_negative_n8_5e19d78058_leaf18_hi : ℚ := (608 : ℚ)/1639
theorem check_round34_left_negative_n8_5e19d78058_leaf18_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf18_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf19_lo : ℚ := (3 : ℚ)/56
def check_round34_left_negative_n8_5e19d78058_leaf19_hi : ℚ := (7 : ℚ)/8
theorem check_round34_left_negative_n8_5e19d78058_leaf19_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf19_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf20_lo : ℚ := (65 : ℚ)/1088
def check_round34_left_negative_n8_5e19d78058_leaf20_hi : ℚ := (17 : ℚ)/56
theorem check_round34_left_negative_n8_5e19d78058_leaf20_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf20_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf21_lo : ℚ := (7 : ℚ)/474
def check_round34_left_negative_n8_5e19d78058_leaf21_hi : ℚ := (799 : ℚ)/1584
theorem check_round34_left_negative_n8_5e19d78058_leaf21_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf21_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf22_lo : ℚ := (7 : ℚ)/544
def check_round34_left_negative_n8_5e19d78058_leaf22_hi : ℚ := (61 : ℚ)/224
theorem check_round34_left_negative_n8_5e19d78058_leaf22_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf22_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf23_lo : ℚ := (107 : ℚ)/1968
def check_round34_left_negative_n8_5e19d78058_leaf23_hi : ℚ := (43 : ℚ)/74
theorem check_round34_left_negative_n8_5e19d78058_leaf23_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf23_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf24_lo : ℚ := (23 : ℚ)/352
def check_round34_left_negative_n8_5e19d78058_leaf24_hi : ℚ := (94 : ℚ)/95
theorem check_round34_left_negative_n8_5e19d78058_leaf24_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf24_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf25_lo : ℚ := (3 : ℚ)/56
def check_round34_left_negative_n8_5e19d78058_leaf25_hi : ℚ := (13 : ℚ)/16
theorem check_round34_left_negative_n8_5e19d78058_leaf25_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf25_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf26_lo : ℚ := (35 : ℚ)/176
def check_round34_left_negative_n8_5e19d78058_leaf26_hi : ℚ := (23 : ℚ)/32
theorem check_round34_left_negative_n8_5e19d78058_leaf26_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf26_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf27_lo : ℚ := (107 : ℚ)/3680
def check_round34_left_negative_n8_5e19d78058_leaf27_hi : ℚ := (26 : ℚ)/41
theorem check_round34_left_negative_n8_5e19d78058_leaf27_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf27_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf28_lo : ℚ := (3 : ℚ)/22
def check_round34_left_negative_n8_5e19d78058_leaf28_hi : ℚ := (43 : ℚ)/64
theorem check_round34_left_negative_n8_5e19d78058_leaf28_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf28_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf29_lo : ℚ := (559 : ℚ)/7680
def check_round34_left_negative_n8_5e19d78058_leaf29_hi : ℚ := (32 : ℚ)/45
theorem check_round34_left_negative_n8_5e19d78058_leaf29_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf29_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf30_lo : ℚ := (45 : ℚ)/2176
def check_round34_left_negative_n8_5e19d78058_leaf30_hi : ℚ := (27 : ℚ)/112
theorem check_round34_left_negative_n8_5e19d78058_leaf30_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf30_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf31_lo : ℚ := (53 : ℚ)/680
def check_round34_left_negative_n8_5e19d78058_leaf31_hi : ℚ := (3101 : ℚ)/6320
theorem check_round34_left_negative_n8_5e19d78058_leaf31_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf31_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf32_lo : ℚ := (31 : ℚ)/340
def check_round34_left_negative_n8_5e19d78058_leaf32_hi : ℚ := (1093 : ℚ)/1672
theorem check_round34_left_negative_n8_5e19d78058_leaf32_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf32_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf33_lo : ℚ := (7 : ℚ)/1056
def check_round34_left_negative_n8_5e19d78058_leaf33_hi : ℚ := (31 : ℚ)/39
theorem check_round34_left_negative_n8_5e19d78058_leaf33_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf33_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf34_lo : ℚ := (39 : ℚ)/256
def check_round34_left_negative_n8_5e19d78058_leaf34_hi : ℚ := (48 : ℚ)/41
theorem check_round34_left_negative_n8_5e19d78058_leaf34_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf34_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf35_lo : ℚ := (1 : ℚ)/4
def check_round34_left_negative_n8_5e19d78058_leaf35_hi : ℚ := (2 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf35_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf35_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf36_lo : ℚ := (1 : ℚ)/80
def check_round34_left_negative_n8_5e19d78058_leaf36_hi : ℚ := (1 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf36_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf36_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf37_lo : ℚ := (3 : ℚ)/56
def check_round34_left_negative_n8_5e19d78058_leaf37_hi : ℚ := (7 : ℚ)/8
theorem check_round34_left_negative_n8_5e19d78058_leaf37_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf37_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf38_lo : ℚ := (1 : ℚ)/12
def check_round34_left_negative_n8_5e19d78058_leaf38_hi : ℚ := (127 : ℚ)/90
theorem check_round34_left_negative_n8_5e19d78058_leaf38_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf38_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf39_lo : ℚ := (5 : ℚ)/28
def check_round34_left_negative_n8_5e19d78058_leaf39_hi : ℚ := (1 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf39_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf39_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf40_lo : ℚ := (1 : ℚ)/10
def check_round34_left_negative_n8_5e19d78058_leaf40_hi : ℚ := (8 : ℚ)/5
theorem check_round34_left_negative_n8_5e19d78058_leaf40_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf40_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf41_lo : ℚ := (5 : ℚ)/144
def check_round34_left_negative_n8_5e19d78058_leaf41_hi : ℚ := (48 : ℚ)/19
theorem check_round34_left_negative_n8_5e19d78058_leaf41_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf41_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf42_lo : ℚ := (1 : ℚ)/4
def check_round34_left_negative_n8_5e19d78058_leaf42_hi : ℚ := (2 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf42_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf42_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf43_lo : ℚ := (17 : ℚ)/448
def check_round34_left_negative_n8_5e19d78058_leaf43_hi : ℚ := (3 : ℚ)/4
theorem check_round34_left_negative_n8_5e19d78058_leaf43_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf43_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf44_lo : ℚ := (59 : ℚ)/352
def check_round34_left_negative_n8_5e19d78058_leaf44_hi : ℚ := (11 : ℚ)/16
theorem check_round34_left_negative_n8_5e19d78058_leaf44_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf44_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf45_lo : ℚ := (15 : ℚ)/94
def check_round34_left_negative_n8_5e19d78058_leaf45_hi : ℚ := (1247 : ℚ)/1512
theorem check_round34_left_negative_n8_5e19d78058_leaf45_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf45_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf46_lo : ℚ := (17 : ℚ)/250
def check_round34_left_negative_n8_5e19d78058_leaf46_hi : ℚ := (145 : ℚ)/112
theorem check_round34_left_negative_n8_5e19d78058_leaf46_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf46_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf47_lo : ℚ := (1 : ℚ)/5
def check_round34_left_negative_n8_5e19d78058_leaf47_hi : ℚ := (341 : ℚ)/200
theorem check_round34_left_negative_n8_5e19d78058_leaf47_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf47_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf48_lo : ℚ := (1 : ℚ)/42
def check_round34_left_negative_n8_5e19d78058_leaf48_hi : ℚ := (107 : ℚ)/44
theorem check_round34_left_negative_n8_5e19d78058_leaf48_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf48_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf49_lo : ℚ := (13 : ℚ)/96
def check_round34_left_negative_n8_5e19d78058_leaf49_hi : ℚ := (40 : ℚ)/11
theorem check_round34_left_negative_n8_5e19d78058_leaf49_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf49_lo = true := by native_decide

def check_round34_left_negative_n8_5e19d78058_leaf50_lo : ℚ := (1 : ℚ)/4
def check_round34_left_negative_n8_5e19d78058_leaf50_hi : ℚ := (2 : ℚ)
theorem check_round34_left_negative_n8_5e19d78058_leaf50_range_pos : rangePos check_round34_left_negative_n8_5e19d78058_leaf50_lo = true := by native_decide

/-- P3 `check_round35_positive_H__n12__c23d75b876.json` / check_round35_positive_H n=12 / exact-IBB-triangle3 -/
def check_round35_positive_H_n12_c23d75b876_leaf0_lo : ℚ := (0 : ℚ)
def check_round35_positive_H_n12_c23d75b876_leaf0_hi : ℚ := (8 : ℚ)/3
theorem check_round35_positive_H_n12_c23d75b876_leaf0_range_nonneg : rangeNonneg check_round35_positive_H_n12_c23d75b876_leaf0_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf1_lo : ℚ := (0 : ℚ)
def check_round35_positive_H_n12_c23d75b876_leaf1_hi : ℚ := (1 : ℚ)
theorem check_round35_positive_H_n12_c23d75b876_leaf1_range_nonneg : rangeNonneg check_round35_positive_H_n12_c23d75b876_leaf1_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf2_lo : ℚ := (0 : ℚ)
def check_round35_positive_H_n12_c23d75b876_leaf2_hi : ℚ := (315 : ℚ)/247
theorem check_round35_positive_H_n12_c23d75b876_leaf2_range_nonneg : rangeNonneg check_round35_positive_H_n12_c23d75b876_leaf2_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf3_lo : ℚ := (1 : ℚ)/16
def check_round35_positive_H_n12_c23d75b876_leaf3_hi : ℚ := (1 : ℚ)/2
theorem check_round35_positive_H_n12_c23d75b876_leaf3_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf3_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf4_lo : ℚ := (0 : ℚ)
def check_round35_positive_H_n12_c23d75b876_leaf4_hi : ℚ := (247 : ℚ)/192
theorem check_round35_positive_H_n12_c23d75b876_leaf4_range_nonneg : rangeNonneg check_round35_positive_H_n12_c23d75b876_leaf4_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf5_lo : ℚ := (1 : ℚ)/8
def check_round35_positive_H_n12_c23d75b876_leaf5_hi : ℚ := (1 : ℚ)/2
theorem check_round35_positive_H_n12_c23d75b876_leaf5_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf5_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf6_lo : ℚ := (1 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf6_hi : ℚ := (13 : ℚ)/32
theorem check_round35_positive_H_n12_c23d75b876_leaf6_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf6_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf7_lo : ℚ := (1 : ℚ)/16
def check_round35_positive_H_n12_c23d75b876_leaf7_hi : ℚ := (17 : ℚ)/64
theorem check_round35_positive_H_n12_c23d75b876_leaf7_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf7_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf8_lo : ℚ := (1 : ℚ)/64
def check_round35_positive_H_n12_c23d75b876_leaf8_hi : ℚ := (27 : ℚ)/128
theorem check_round35_positive_H_n12_c23d75b876_leaf8_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf8_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf9_lo : ℚ := (1 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf9_hi : ℚ := (35 : ℚ)/256
theorem check_round35_positive_H_n12_c23d75b876_leaf9_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf9_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf10_lo : ℚ := (1 : ℚ)/128
def check_round35_positive_H_n12_c23d75b876_leaf10_hi : ℚ := (55 : ℚ)/512
theorem check_round35_positive_H_n12_c23d75b876_leaf10_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf10_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf11_lo : ℚ := (16384 : ℚ)/333829
def check_round35_positive_H_n12_c23d75b876_leaf11_hi : ℚ := (13627 : ℚ)/61440
theorem check_round35_positive_H_n12_c23d75b876_leaf11_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf11_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf12_lo : ℚ := (1 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf12_hi : ℚ := (103 : ℚ)/1024
theorem check_round35_positive_H_n12_c23d75b876_leaf12_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf12_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf13_lo : ℚ := (1 : ℚ)/16
def check_round35_positive_H_n12_c23d75b876_leaf13_hi : ℚ := (51 : ℚ)/256
theorem check_round35_positive_H_n12_c23d75b876_leaf13_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf13_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf14_lo : ℚ := (1 : ℚ)/8
def check_round35_positive_H_n12_c23d75b876_leaf14_hi : ℚ := (25 : ℚ)/64
theorem check_round35_positive_H_n12_c23d75b876_leaf14_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf14_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf15_lo : ℚ := (467 : ℚ)/1008
def check_round35_positive_H_n12_c23d75b876_leaf15_hi : ℚ := (30 : ℚ)/11
theorem check_round35_positive_H_n12_c23d75b876_leaf15_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf15_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf16_lo : ℚ := (1 : ℚ)/64
def check_round35_positive_H_n12_c23d75b876_leaf16_hi : ℚ := (3 : ℚ)/8
theorem check_round35_positive_H_n12_c23d75b876_leaf16_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf16_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf17_lo : ℚ := (107 : ℚ)/2664
def check_round35_positive_H_n12_c23d75b876_leaf17_hi : ℚ := (27345 : ℚ)/30176
theorem check_round35_positive_H_n12_c23d75b876_leaf17_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf17_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf18_lo : ℚ := (3 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf18_hi : ℚ := (11 : ℚ)/32
theorem check_round35_positive_H_n12_c23d75b876_leaf18_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf18_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf19_lo : ℚ := (101 : ℚ)/8
def check_round35_positive_H_n12_c23d75b876_leaf19_hi : ℚ := (53 : ℚ)/2
theorem check_round35_positive_H_n12_c23d75b876_leaf19_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf19_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf20_lo : ℚ := (3 : ℚ)/26
def check_round35_positive_H_n12_c23d75b876_leaf20_hi : ℚ := (2829 : ℚ)/1408
theorem check_round35_positive_H_n12_c23d75b876_leaf20_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf20_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf21_lo : ℚ := (101 : ℚ)/8
def check_round35_positive_H_n12_c23d75b876_leaf21_hi : ℚ := (53 : ℚ)/2
theorem check_round35_positive_H_n12_c23d75b876_leaf21_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf21_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf22_lo : ℚ := (2995 : ℚ)/15808
def check_round35_positive_H_n12_c23d75b876_leaf22_hi : ℚ := (185 : ℚ)/321
theorem check_round35_positive_H_n12_c23d75b876_leaf22_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf22_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf23_lo : ℚ := (15 : ℚ)/256
def check_round35_positive_H_n12_c23d75b876_leaf23_hi : ℚ := (3 : ℚ)/16
theorem check_round35_positive_H_n12_c23d75b876_leaf23_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf23_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf24_lo : ℚ := (20575 : ℚ)/251328
def check_round35_positive_H_n12_c23d75b876_leaf24_hi : ℚ := (467815 : ℚ)/970176
theorem check_round35_positive_H_n12_c23d75b876_leaf24_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf24_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf25_lo : ℚ := (5 : ℚ)/128
def check_round35_positive_H_n12_c23d75b876_leaf25_hi : ℚ := (11 : ℚ)/64
theorem check_round35_positive_H_n12_c23d75b876_leaf25_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf25_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf26_lo : ℚ := (91 : ℚ)/16
def check_round35_positive_H_n12_c23d75b876_leaf26_hi : ℚ := (101 : ℚ)/8
theorem check_round35_positive_H_n12_c23d75b876_leaf26_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf26_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf27_lo : ℚ := (3 : ℚ)/64
def check_round35_positive_H_n12_c23d75b876_leaf27_hi : ℚ := (5 : ℚ)/16
theorem check_round35_positive_H_n12_c23d75b876_leaf27_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf27_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf28_lo : ℚ := (90549 : ℚ)/2129920
def check_round35_positive_H_n12_c23d75b876_leaf28_hi : ℚ := (706131 : ℚ)/1960910
theorem check_round35_positive_H_n12_c23d75b876_leaf28_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf28_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf29_lo : ℚ := (113675 : ℚ)/884224
def check_round35_positive_H_n12_c23d75b876_leaf29_hi : ℚ := (9910683 : ℚ)/31221632
theorem check_round35_positive_H_n12_c23d75b876_leaf29_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf29_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf30_lo : ℚ := (9 : ℚ)/512
def check_round35_positive_H_n12_c23d75b876_leaf30_hi : ℚ := (11 : ℚ)/128
theorem check_round35_positive_H_n12_c23d75b876_leaf30_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf30_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf31_lo : ℚ := (71 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf31_hi : ℚ := (91 : ℚ)/16
theorem check_round35_positive_H_n12_c23d75b876_leaf31_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf31_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf32_lo : ℚ := (5 : ℚ)/256
def check_round35_positive_H_n12_c23d75b876_leaf32_hi : ℚ := (5 : ℚ)/32
theorem check_round35_positive_H_n12_c23d75b876_leaf32_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf32_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf33_lo : ℚ := (2542851 : ℚ)/31711232
def check_round35_positive_H_n12_c23d75b876_leaf33_hi : ℚ := (425799 : ℚ)/1553176
theorem check_round35_positive_H_n12_c23d75b876_leaf33_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf33_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf34_lo : ℚ := (9 : ℚ)/1024
def check_round35_positive_H_n12_c23d75b876_leaf34_hi : ℚ := (5 : ℚ)/64
theorem check_round35_positive_H_n12_c23d75b876_leaf34_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf34_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf35_lo : ℚ := (321 : ℚ)/10282
def check_round35_positive_H_n12_c23d75b876_leaf35_hi : ℚ := (7113987 : ℚ)/30900224
theorem check_round35_positive_H_n12_c23d75b876_leaf35_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf35_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf36_lo : ℚ := (1 : ℚ)/64
def check_round35_positive_H_n12_c23d75b876_leaf36_hi : ℚ := (9 : ℚ)/128
theorem check_round35_positive_H_n12_c23d75b876_leaf36_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf36_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf37_lo : ℚ := (31 : ℚ)/64
def check_round35_positive_H_n12_c23d75b876_leaf37_hi : ℚ := (71 : ℚ)/32
theorem check_round35_positive_H_n12_c23d75b876_leaf37_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf37_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf38_lo : ℚ := (71 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf38_hi : ℚ := (91 : ℚ)/16
theorem check_round35_positive_H_n12_c23d75b876_leaf38_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf38_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf39_lo : ℚ := (1 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf39_hi : ℚ := (9 : ℚ)/64
theorem check_round35_positive_H_n12_c23d75b876_leaf39_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf39_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf40_lo : ℚ := (71 : ℚ)/32
def check_round35_positive_H_n12_c23d75b876_leaf40_hi : ℚ := (91 : ℚ)/16
theorem check_round35_positive_H_n12_c23d75b876_leaf40_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf40_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf41_lo : ℚ := (91 : ℚ)/16
def check_round35_positive_H_n12_c23d75b876_leaf41_hi : ℚ := (101 : ℚ)/8
theorem check_round35_positive_H_n12_c23d75b876_leaf41_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf41_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf42_lo : ℚ := (1 : ℚ)/16
def check_round35_positive_H_n12_c23d75b876_leaf42_hi : ℚ := (9 : ℚ)/32
theorem check_round35_positive_H_n12_c23d75b876_leaf42_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf42_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf43_lo : ℚ := (91 : ℚ)/16
def check_round35_positive_H_n12_c23d75b876_leaf43_hi : ℚ := (101 : ℚ)/8
theorem check_round35_positive_H_n12_c23d75b876_leaf43_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf43_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf44_lo : ℚ := (101 : ℚ)/8
def check_round35_positive_H_n12_c23d75b876_leaf44_hi : ℚ := (53 : ℚ)/2
theorem check_round35_positive_H_n12_c23d75b876_leaf44_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf44_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf45_lo : ℚ := (0 : ℚ)
def check_round35_positive_H_n12_c23d75b876_leaf45_hi : ℚ := (1 : ℚ)
theorem check_round35_positive_H_n12_c23d75b876_leaf45_range_nonneg : rangeNonneg check_round35_positive_H_n12_c23d75b876_leaf45_lo = true := by native_decide

def check_round35_positive_H_n12_c23d75b876_leaf46_lo : ℚ := (53 : ℚ)/2
def check_round35_positive_H_n12_c23d75b876_leaf46_hi : ℚ := (82 : ℚ)
theorem check_round35_positive_H_n12_c23d75b876_leaf46_range_pos : rangePos check_round35_positive_H_n12_c23d75b876_leaf46_lo = true := by native_decide

/-- P3 `check_round38_empty_right_negative__n7__bd26f7b647.json` / check_round38_empty_right_negative n=7 / exact-IBB-raw -/
def check_round38_empty_right_negative_n7_bd26f7b647_leaf0_lo : ℚ := (5 : ℚ)/192
def check_round38_empty_right_negative_n7_bd26f7b647_leaf0_hi : ℚ := (180 : ℚ)/197
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf0_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf0_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf1_lo : ℚ := (93 : ℚ)/788
def check_round38_empty_right_negative_n7_bd26f7b647_leaf1_hi : ℚ := (419 : ℚ)/702
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf1_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf1_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf2_lo : ℚ := (41 : ℚ)/702
def check_round38_empty_right_negative_n7_bd26f7b647_leaf2_hi : ℚ := (537 : ℚ)/1232
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf2_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf2_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf3_lo : ℚ := (7 : ℚ)/128
def check_round38_empty_right_negative_n7_bd26f7b647_leaf3_hi : ℚ := (4 : ℚ)/15
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf3_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf3_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf4_lo : ℚ := (41 : ℚ)/702
def check_round38_empty_right_negative_n7_bd26f7b647_leaf4_hi : ℚ := (537 : ℚ)/1232
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf4_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf4_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf5_lo : ℚ := (19 : ℚ)/468
def check_round38_empty_right_negative_n7_bd26f7b647_leaf5_hi : ℚ := (723 : ℚ)/2636
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf5_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf5_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf6_lo : ℚ := (1 : ℚ)/48
def check_round38_empty_right_negative_n7_bd26f7b647_leaf6_hi : ℚ := (11 : ℚ)/58
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf6_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf6_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf7_lo : ℚ := (5 : ℚ)/1318
def check_round38_empty_right_negative_n7_bd26f7b647_leaf7_hi : ℚ := (887 : ℚ)/4928
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf7_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf7_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf8_lo : ℚ := (5 : ℚ)/116
def check_round38_empty_right_negative_n7_bd26f7b647_leaf8_hi : ℚ := (17 : ℚ)/112
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf8_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf8_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf9_lo : ℚ := (19 : ℚ)/468
def check_round38_empty_right_negative_n7_bd26f7b647_leaf9_hi : ℚ := (723 : ℚ)/2636
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf9_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf9_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf10_lo : ℚ := (1 : ℚ)/48
def check_round38_empty_right_negative_n7_bd26f7b647_leaf10_hi : ℚ := (11 : ℚ)/58
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf10_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf10_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf11_lo : ℚ := (5 : ℚ)/1318
def check_round38_empty_right_negative_n7_bd26f7b647_leaf11_hi : ℚ := (887 : ℚ)/4928
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf11_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf11_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf12_lo : ℚ := (5 : ℚ)/116
def check_round38_empty_right_negative_n7_bd26f7b647_leaf12_hi : ℚ := (17 : ℚ)/112
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf12_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf12_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf13_lo : ℚ := (93 : ℚ)/788
def check_round38_empty_right_negative_n7_bd26f7b647_leaf13_hi : ℚ := (419 : ℚ)/702
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf13_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf13_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf14_lo : ℚ := (41 : ℚ)/702
def check_round38_empty_right_negative_n7_bd26f7b647_leaf14_hi : ℚ := (537 : ℚ)/1232
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf14_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf14_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf15_lo : ℚ := (7 : ℚ)/128
def check_round38_empty_right_negative_n7_bd26f7b647_leaf15_hi : ℚ := (4 : ℚ)/15
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf15_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf15_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf16_lo : ℚ := (13 : ℚ)/3080
def check_round38_empty_right_negative_n7_bd26f7b647_leaf16_hi : ℚ := (19 : ℚ)/60
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf16_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf16_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf17_lo : ℚ := (3 : ℚ)/32
def check_round38_empty_right_negative_n7_bd26f7b647_leaf17_hi : ℚ := (4 : ℚ)/7
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf17_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf17_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf18_lo : ℚ := (93 : ℚ)/788
def check_round38_empty_right_negative_n7_bd26f7b647_leaf18_hi : ℚ := (419 : ℚ)/702
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf18_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf18_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf19_lo : ℚ := (41 : ℚ)/702
def check_round38_empty_right_negative_n7_bd26f7b647_leaf19_hi : ℚ := (537 : ℚ)/1232
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf19_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf19_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf20_lo : ℚ := (19 : ℚ)/468
def check_round38_empty_right_negative_n7_bd26f7b647_leaf20_hi : ℚ := (723 : ℚ)/2636
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf20_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf20_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf21_lo : ℚ := (5 : ℚ)/1318
def check_round38_empty_right_negative_n7_bd26f7b647_leaf21_hi : ℚ := (887 : ℚ)/4928
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf21_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf21_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf22_lo : ℚ := (1 : ℚ)/448
def check_round38_empty_right_negative_n7_bd26f7b647_leaf22_hi : ℚ := (1 : ℚ)/9
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf22_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf22_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf23_lo : ℚ := (79 : ℚ)/18480
def check_round38_empty_right_negative_n7_bd26f7b647_leaf23_hi : ℚ := (1483 : ℚ)/9240
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf23_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf23_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf24_lo : ℚ := (41 : ℚ)/1155
def check_round38_empty_right_negative_n7_bd26f7b647_leaf24_hi : ℚ := (783 : ℚ)/3080
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf24_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf24_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf25_lo : ℚ := (617 : ℚ)/9240
def check_round38_empty_right_negative_n7_bd26f7b647_leaf25_hi : ℚ := (146 : ℚ)/385
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf25_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf25_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf26_lo : ℚ := (199 : ℚ)/1540
def check_round38_empty_right_negative_n7_bd26f7b647_leaf26_hi : ℚ := (17 : ℚ)/30
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf26_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf26_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf27_lo : ℚ := (1 : ℚ)/56
def check_round38_empty_right_negative_n7_bd26f7b647_leaf27_hi : ℚ := (5 : ℚ)/13
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf27_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf27_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf28_lo : ℚ := (617 : ℚ)/9240
def check_round38_empty_right_negative_n7_bd26f7b647_leaf28_hi : ℚ := (146 : ℚ)/385
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf28_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf28_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf29_lo : ℚ := (1 : ℚ)/56
def check_round38_empty_right_negative_n7_bd26f7b647_leaf29_hi : ℚ := (5 : ℚ)/13
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf29_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf29_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf30_lo : ℚ := (617 : ℚ)/9240
def check_round38_empty_right_negative_n7_bd26f7b647_leaf30_hi : ℚ := (146 : ℚ)/385
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf30_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf30_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf31_lo : ℚ := (199 : ℚ)/1540
def check_round38_empty_right_negative_n7_bd26f7b647_leaf31_hi : ℚ := (17 : ℚ)/30
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf31_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf31_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf32_lo : ℚ := (1 : ℚ)/15
def check_round38_empty_right_negative_n7_bd26f7b647_leaf32_hi : ℚ := (145 : ℚ)/154
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf32_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf32_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf33_lo : ℚ := (1 : ℚ)/8
def check_round38_empty_right_negative_n7_bd26f7b647_leaf33_hi : ℚ := (4 : ℚ)/3
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf33_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf33_lo = true := by native_decide

def check_round38_empty_right_negative_n7_bd26f7b647_leaf34_lo : ℚ := (443 : ℚ)/2310
def check_round38_empty_right_negative_n7_bd26f7b647_leaf34_hi : ℚ := (111 : ℚ)/77
theorem check_round38_empty_right_negative_n7_bd26f7b647_leaf34_range_pos : rangePos check_round38_empty_right_negative_n7_bd26f7b647_leaf34_lo = true := by native_decide

/-- P3 `check_round38_empty_right_negative__n8__93e5a9a520.json` / check_round38_empty_right_negative n=8 / exact-IBB-triangle3 -/
def check_round38_empty_right_negative_n8_93e5a9a520_leaf0_lo : ℚ := (-1 : ℚ)
def check_round38_empty_right_negative_n8_93e5a9a520_leaf0_hi : ℚ := (-3 : ℚ)/16
theorem check_round38_empty_right_negative_n8_93e5a9a520_leaf0_range_neg : rangeNeg check_round38_empty_right_negative_n8_93e5a9a520_leaf0_hi = true := by native_decide

def check_round38_empty_right_negative_n8_93e5a9a520_leaf1_lo : ℚ := (1 : ℚ)/4
def check_round38_empty_right_negative_n8_93e5a9a520_leaf1_hi : ℚ := (1 : ℚ)
theorem check_round38_empty_right_negative_n8_93e5a9a520_leaf1_range_pos : rangePos check_round38_empty_right_negative_n8_93e5a9a520_leaf1_lo = true := by native_decide

/-- P3 `check_round39_single_contact__n7__93f5a6f026.json` / check_round39_single_contact n=7 / exact-IBB-triangle3 -/
def check_round39_single_contact_n7_93f5a6f026_leaf0_lo : ℚ := (1 : ℚ)/4
def check_round39_single_contact_n7_93f5a6f026_leaf0_hi : ℚ := (2 : ℚ)
theorem check_round39_single_contact_n7_93f5a6f026_leaf0_range_pos : rangePos check_round39_single_contact_n7_93f5a6f026_leaf0_lo = true := by native_decide

def check_round39_single_contact_n7_93f5a6f026_leaf1_lo : ℚ := (1 : ℚ)/4
def check_round39_single_contact_n7_93f5a6f026_leaf1_hi : ℚ := (2 : ℚ)
theorem check_round39_single_contact_n7_93f5a6f026_leaf1_range_pos : rangePos check_round39_single_contact_n7_93f5a6f026_leaf1_lo = true := by native_decide

def check_round39_single_contact_n7_93f5a6f026_leaf2_lo : ℚ := (0 : ℚ)
def check_round39_single_contact_n7_93f5a6f026_leaf2_hi : ℚ := (1 : ℚ)/4
theorem check_round39_single_contact_n7_93f5a6f026_leaf2_range_nonneg : rangeNonneg check_round39_single_contact_n7_93f5a6f026_leaf2_lo = true := by native_decide

def check_round39_single_contact_n7_93f5a6f026_leaf3_lo : ℚ := (1 : ℚ)/4
def check_round39_single_contact_n7_93f5a6f026_leaf3_hi : ℚ := (2 : ℚ)
theorem check_round39_single_contact_n7_93f5a6f026_leaf3_range_pos : rangePos check_round39_single_contact_n7_93f5a6f026_leaf3_lo = true := by native_decide

def check_round39_single_contact_n7_93f5a6f026_leaf4_lo : ℚ := (0 : ℚ)
def check_round39_single_contact_n7_93f5a6f026_leaf4_hi : ℚ := (1 : ℚ)/4
theorem check_round39_single_contact_n7_93f5a6f026_leaf4_range_nonneg : rangeNonneg check_round39_single_contact_n7_93f5a6f026_leaf4_lo = true := by native_decide

def check_round39_single_contact_n7_93f5a6f026_leaf5_lo : ℚ := (1 : ℚ)/4
def check_round39_single_contact_n7_93f5a6f026_leaf5_hi : ℚ := (3 : ℚ)/4
theorem check_round39_single_contact_n7_93f5a6f026_leaf5_range_pos : rangePos check_round39_single_contact_n7_93f5a6f026_leaf5_lo = true := by native_decide

/-- P3 `check_round39_single_contact__n9__14f5e26215.json` / check_round39_single_contact n=9 / exact-IBB-triangle3 -/
def check_round39_single_contact_n9_14f5e26215_leaf0_lo : ℚ := (0 : ℚ)
def check_round39_single_contact_n9_14f5e26215_leaf0_hi : ℚ := (1 : ℚ)
theorem check_round39_single_contact_n9_14f5e26215_leaf0_range_nonneg : rangeNonneg check_round39_single_contact_n9_14f5e26215_leaf0_lo = true := by native_decide

def p3LiftCount : ℕ := 10
theorem p3LiftCount_eq : p3LiftCount = 10 := rfl
def p3LeafTheoremCount : ℕ := 195
theorem p3LeafTheoremCount_eq : p3LeafTheoremCount = 195 := rfl
def bernsteinExactP3Closed : Bool := true
theorem bernsteinExactP3Closed_true : bernsteinExactP3Closed = true := rfl
def openStatus : String :=
  "CLOSED: P3 IBB leaf ranges (+ nested gap coeffs where present). Not PrincipalClaim."
end S6.BernsteinExactP3
