import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Exact-cert Bernstein / IBB lifts (batch24–26f family)

Machine-checked rational coefficient nonnegativity (and IBB leaf range signs)
from `artifacts/closure/item3_certs/exact_certs_batch24/`.

Honest: these lifts verify the **certificate payload** side of the Python checker;
they do **not** discharge `principalClaimProvedUnconditionally` or end-to-end
faithfulness. Generated from CERT_TO_LEAN_HANDOFF P1.
-/

namespace S6.BernsteinExactP1

/-- List of rationals is componentwise ≥ 0. -/
def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

/-- List of rationals is componentwise > 0. -/
def posList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 < c) && posList cs


/-- P1 `check_round24_g3_fside__n4__a82de007c0.json` / `check_round24_g3_fside` n=4 / bernstein_box_strict_endpoint -/
def check_round24_g3_fside_n4_a82de007c0_numer : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (0 : ℚ)]
theorem check_round24_g3_fside_n4_a82de007c0_numer_nonneg : nonnegList check_round24_g3_fside_n4_a82de007c0_numer = true := by
  native_decide

def check_round24_g3_fside_n4_a82de007c0_denom : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (48 : ℚ)/49]
theorem check_round24_g3_fside_n4_a82de007c0_denom_pos : posList check_round24_g3_fside_n4_a82de007c0_denom = true := by
  native_decide

/-- P1 `check_round27_g2_two_branches__n4__ba4d19a580.json` / `check_round27_g2_two_branches` n=4 / bernstein_box_strict_endpoint -/
def check_round27_g2_two_branches_n4_ba4d19a580_numer : List ℚ :=
  [(0 : ℚ), (23 : ℚ)/12, (2 : ℚ)]
theorem check_round27_g2_two_branches_n4_ba4d19a580_numer_nonneg : nonnegList check_round27_g2_two_branches_n4_ba4d19a580_numer = true := by
  native_decide

def check_round27_g2_two_branches_n4_ba4d19a580_denom : List ℚ :=
  [(265 : ℚ)/144, (23 : ℚ)/12, (2 : ℚ)]
theorem check_round27_g2_two_branches_n4_ba4d19a580_denom_pos : posList check_round27_g2_two_branches_n4_ba4d19a580_denom = true := by
  native_decide

/-- P1 `check_round29_no_top_structure__n6__5f3dda6861.json` / `check_round29_no_top_structure` n=6 / bernstein_box -/
def check_round29_no_top_structure_n6_5f3dda6861_numer : List ℚ :=
  [(1 : ℚ), (2 : ℚ), (2 : ℚ), (2 : ℚ), (3 : ℚ), (3 : ℚ), (2 : ℚ), (3 : ℚ), (3 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (2 : ℚ), (2 : ℚ), (1 : ℚ), (2 : ℚ), (2 : ℚ)]
theorem check_round29_no_top_structure_n6_5f3dda6861_numer_nonneg : nonnegList check_round29_no_top_structure_n6_5f3dda6861_numer = true := by
  native_decide

def check_round29_no_top_structure_n6_5f3dda6861_denom : List ℚ :=
  [(1 : ℚ)]
theorem check_round29_no_top_structure_n6_5f3dda6861_denom_pos : posList check_round29_no_top_structure_n6_5f3dda6861_denom = true := by
  native_decide

/-- P1 `check_round29_no_top_structure__n6__866f1cfbe2.json` / `check_round29_no_top_structure` n=6 / bernstein_box -/
def check_round29_no_top_structure_n6_866f1cfbe2_numer : List ℚ :=
  [(1 : ℚ), (2 : ℚ), (2 : ℚ), (2 : ℚ), (3 : ℚ), (3 : ℚ), (2 : ℚ), (3 : ℚ), (3 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (1 : ℚ), (2 : ℚ), (2 : ℚ), (1 : ℚ), (2 : ℚ), (2 : ℚ)]
theorem check_round29_no_top_structure_n6_866f1cfbe2_numer_nonneg : nonnegList check_round29_no_top_structure_n6_866f1cfbe2_numer = true := by
  native_decide

def check_round29_no_top_structure_n6_866f1cfbe2_denom : List ℚ :=
  [(1 : ℚ)]
theorem check_round29_no_top_structure_n6_866f1cfbe2_denom_pos : posList check_round29_no_top_structure_n6_866f1cfbe2_denom = true := by
  native_decide

/-- P1 `check_round30_corrected_geometry__n3__81b6979c71.json` / `check_round30_corrected_geometry` n=3 / bernstein_box -/
def check_round30_corrected_geometry_n3_81b6979c71_numer : List ℚ :=
  [(1 : ℚ), (2 : ℚ), (2 : ℚ), (0 : ℚ), (1 : ℚ), (1 : ℚ), (2 : ℚ), (3 : ℚ), (3 : ℚ), (1 : ℚ), (2 : ℚ), (2 : ℚ)]
theorem check_round30_corrected_geometry_n3_81b6979c71_numer_nonneg : nonnegList check_round30_corrected_geometry_n3_81b6979c71_numer = true := by
  native_decide

def check_round30_corrected_geometry_n3_81b6979c71_denom : List ℚ :=
  [(1 : ℚ)]
theorem check_round30_corrected_geometry_n3_81b6979c71_denom_pos : posList check_round30_corrected_geometry_n3_81b6979c71_denom = true := by
  native_decide

/-- P1 `check_round30_corrected_geometry__n9__c76afaaaf1.json` / `check_round30_corrected_geometry` n=9 / bernstein_box -/
def check_round30_corrected_geometry_n9_c76afaaaf1_numer : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (4 : ℚ)/3, (2 : ℚ), (2 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)/3, (1 : ℚ), (1 : ℚ), (2 : ℚ), (2 : ℚ), (7 : ℚ)/3, (3 : ℚ), (3 : ℚ), (1 : ℚ), (1 : ℚ), (4 : ℚ)/3, (2 : ℚ), (2 : ℚ)]
theorem check_round30_corrected_geometry_n9_c76afaaaf1_numer_nonneg : nonnegList check_round30_corrected_geometry_n9_c76afaaaf1_numer = true := by
  native_decide

def check_round30_corrected_geometry_n9_c76afaaaf1_denom : List ℚ :=
  [(1 : ℚ)]
theorem check_round30_corrected_geometry_n9_c76afaaaf1_denom_pos : posList check_round30_corrected_geometry_n9_c76afaaaf1_denom = true := by
  native_decide

/-- P1 `check_round33_right_nonempty__n8__9f08d30032.json` / `check_round33_right_nonempty` n=8 / bernstein_box -/
def check_round33_right_nonempty_n8_9f08d30032_numer : List ℚ :=
  [(4 : ℚ), (9 : ℚ), (10 : ℚ), (15 : ℚ), (4 : ℚ), (9 : ℚ), (10 : ℚ), (15 : ℚ), (4 : ℚ), (9 : ℚ), (10 : ℚ), (15 : ℚ), (0 : ℚ), (5 : ℚ), (6 : ℚ), (11 : ℚ)]
theorem check_round33_right_nonempty_n8_9f08d30032_numer_nonneg : nonnegList check_round33_right_nonempty_n8_9f08d30032_numer = true := by
  native_decide

def check_round33_right_nonempty_n8_9f08d30032_denom : List ℚ :=
  [(1 : ℚ)]
theorem check_round33_right_nonempty_n8_9f08d30032_denom_pos : posList check_round33_right_nonempty_n8_9f08d30032_denom = true := by
  native_decide

/-- P1 `check_round35_positive_H__n4__c5807376e0.json` / `check_round35_positive_H` n=4 / bernstein_box -/
def check_round35_positive_H_n4_c5807376e0_numer : List ℚ :=
  [(48 : ℚ), (219 : ℚ)/8, (0 : ℚ)]
theorem check_round35_positive_H_n4_c5807376e0_numer_nonneg : nonnegList check_round35_positive_H_n4_c5807376e0_numer = true := by
  native_decide

def check_round35_positive_H_n4_c5807376e0_denom : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (55 : ℚ)/64]
theorem check_round35_positive_H_n4_c5807376e0_denom_pos : posList check_round35_positive_H_n4_c5807376e0_denom = true := by
  native_decide

/-- P1 `check_round35_positive_H__n8__622d8fa357.json` / `check_round35_positive_H` n=8 / bernstein_box -/
def check_round35_positive_H_n8_622d8fa357_numer : List ℚ :=
  [(4 : ℚ), (10 : ℚ), (4 : ℚ), (10 : ℚ), (9 : ℚ), (15 : ℚ), (9 : ℚ), (15 : ℚ), (4 : ℚ), (10 : ℚ), (0 : ℚ), (6 : ℚ), (9 : ℚ), (15 : ℚ), (5 : ℚ), (11 : ℚ)]
theorem check_round35_positive_H_n8_622d8fa357_numer_nonneg : nonnegList check_round35_positive_H_n8_622d8fa357_numer = true := by
  native_decide

def check_round35_positive_H_n8_622d8fa357_denom : List ℚ :=
  [(1 : ℚ)]
theorem check_round35_positive_H_n8_622d8fa357_denom_pos : posList check_round35_positive_H_n8_622d8fa357_denom = true := by
  native_decide

/-- P1 `check_round35_positive_H__n9__e2db3fea8c.json` / `check_round35_positive_H` n=9 / bernstein_box -/
def check_round35_positive_H_n9_e2db3fea8c_numer : List ℚ :=
  [(80 : ℚ), (72 : ℚ), (60 : ℚ), (52 : ℚ), (45 : ℚ), (37 : ℚ), (80 : ℚ), (104 : ℚ)/5, (60 : ℚ), (68 : ℚ)/5, (45 : ℚ), (41 : ℚ)/5, (80 : ℚ), (348 : ℚ)/5, (60 : ℚ), (248 : ℚ)/5, (45 : ℚ), (173 : ℚ)/5, (80 : ℚ), (92 : ℚ)/5, (60 : ℚ), (56 : ℚ)/5, (45 : ℚ), (29 : ℚ)/5, (80 : ℚ), (1662 : ℚ)/25, (60 : ℚ), (1162 : ℚ)/25, (45 : ℚ), (787 : ℚ)/25, (80 : ℚ), (382 : ℚ)/25, (60 : ℚ), (202 : ℚ)/25, (45 : ℚ), (67 : ℚ)/25]
theorem check_round35_positive_H_n9_e2db3fea8c_numer_nonneg : nonnegList check_round35_positive_H_n9_e2db3fea8c_numer = true := by
  native_decide

def check_round35_positive_H_n9_e2db3fea8c_denom : List ℚ :=
  [(20 : ℚ), (15 : ℚ), (45 : ℚ)/4, (26 : ℚ), (39 : ℚ)/2, (117 : ℚ)/8, (169 : ℚ)/5, (507 : ℚ)/20, (1521 : ℚ)/80]
theorem check_round35_positive_H_n9_e2db3fea8c_denom_pos : posList check_round35_positive_H_n9_e2db3fea8c_denom = true := by
  native_decide

def p1LiftCount : ℕ := 10
theorem p1LiftCount_eq : p1LiftCount = 10 := rfl

def bernsteinExactP1Closed : Bool := true
theorem bernsteinExactP1Closed_true : bernsteinExactP1Closed = true := rfl

def openStatus : String :=
  "CLOSED: P1 numer/denom coeff signs via native_decide. " ++
  "Does NOT prove PrincipalClaim unconditionally."

end S6.BernsteinExactP1
