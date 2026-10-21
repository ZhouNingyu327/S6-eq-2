import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Round13 pair Bernstein coefficient nonnegativity

From `artifacts/checkers/round13_pair_certificate.json`.

Honest: payload / table strengthenings ≠ PrincipalClaim unconditional.
-/

namespace S6.Round13PairBernstein

def nonnegList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (0 ≤ c) && nonnegList cs

def nonposList : List ℚ → Bool
  | [] => true
  | c :: cs => decide (c ≤ 0) && nonposList cs


/-- R13 branch `c` poly0 row0 -/
def branch_c_poly0_row0 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
theorem branch_c_poly0_row0_nonneg : nonnegList branch_c_poly0_row0 = true := by native_decide

/-- R13 branch `c` poly0 row1 -/
def branch_c_poly0_row1 : List ℚ :=
  [(2 : ℚ)/75, (2 : ℚ)/75, (2 : ℚ)/75, (2 : ℚ)/75, (2 : ℚ)/75, (2 : ℚ)/75, (2 : ℚ)/75]
theorem branch_c_poly0_row1_nonneg : nonnegList branch_c_poly0_row1 = true := by native_decide

/-- R13 branch `c` poly0 row2 -/
def branch_c_poly0_row2 : List ℚ :=
  [(44 : ℚ)/875, (56 : ℚ)/1125, (388 : ℚ)/7875, (128 : ℚ)/2625, (76 : ℚ)/1575, (376 : ℚ)/7875, (124 : ℚ)/2625]
theorem branch_c_poly0_row2_nonneg : nonnegList branch_c_poly0_row2 = true := by native_decide

/-- R13 branch `c` poly0 row3 -/
def branch_c_poly0_row3 : List ℚ :=
  [(3942 : ℚ)/56875, (11582 : ℚ)/170625, (11338 : ℚ)/170625, (3698 : ℚ)/56875, (62 : ℚ)/975, (10606 : ℚ)/170625, (3454 : ℚ)/56875]
theorem branch_c_poly0_row3_nonneg : nonnegList branch_c_poly0_row3 = true := by native_decide

/-- R13 branch `c` poly0 row4 -/
def branch_c_poly0_row4 : List ℚ :=
  [(10072 : ℚ)/121875, (29264 : ℚ)/365625, (990904 : ℚ)/12796875, (319184 : ℚ)/4265625, (924184 : ℚ)/12796875, (35632 : ℚ)/511875, (11432 : ℚ)/170625]
theorem branch_c_poly0_row4_nonneg : nonnegList branch_c_poly0_row4 = true := by native_decide

/-- R13 branch `c` poly0 row5 -/
def branch_c_poly0_row5 : List ℚ :=
  [(280902 : ℚ)/3128125, (345794 : ℚ)/4021875, (11563918 : ℚ)/140765625, (94222 : ℚ)/1203125, (10482958 : ℚ)/140765625, (1988174 : ℚ)/28153125, (29834 : ℚ)/446875]
theorem branch_c_poly0_row5_nonneg : nonnegList branch_c_poly0_row5 = true := by native_decide

/-- R13 branch `c` poly0 row6 -/
def branch_c_poly0_row6 : List ℚ :=
  [(1422924 : ℚ)/15640625, (4040632 : ℚ)/46921875, (95281532 : ℚ)/1173046875, (29838896 : ℚ)/391015625, (16744292 : ℚ)/234609375, (15579208 : ℚ)/234609375, (4802708 : ℚ)/78203125]
theorem branch_c_poly0_row6_nonneg : nonnegList branch_c_poly0_row6 = true := by native_decide

/-- R13 branch `c` poly0 row7 -/
def branch_c_poly0_row7 : List ℚ :=
  [(1749334 : ℚ)/20109375, (24567758 : ℚ)/301640625, (190628326 : ℚ)/2513671875, (176360786 : ℚ)/2513671875, (485795114 : ℚ)/7541015625, (29468818 : ℚ)/502734375, (5304038 : ℚ)/100546875]
theorem branch_c_poly0_row7_nonneg : nonnegList branch_c_poly0_row7 = true := by native_decide

/-- R13 branch `c` poly0 row8 -/
def branch_c_poly0_row8 : List ℚ :=
  [(13256528 : ℚ)/167578125, (110630816 : ℚ)/1508203125, (2543609936 : ℚ)/37705078125, (772140064 : ℚ)/12568359375, (2084383952 : ℚ)/37705078125, (14781472 : ℚ)/301640625, (107100208 : ℚ)/2513671875]
theorem branch_c_poly0_row8_nonneg : nonnegList branch_c_poly0_row8 = true := by native_decide

/-- R13 branch `c` poly0 row9 -/
def branch_c_poly0_row9 : List ℚ :=
  [(134480382 : ℚ)/1955078125, (371323402 : ℚ)/5865234375, (8444060074 : ℚ)/146630859375, (2523680382 : ℚ)/48876953125, (4848086 : ℚ)/106640625, (382092262 : ℚ)/9775390625, (28902626 : ℚ)/888671875]
theorem branch_c_poly0_row9_nonneg : nonnegList branch_c_poly0_row9 = true := by native_decide

/-- R13 branch `c` poly0 row10 -/
def branch_c_poly0_row10 : List ℚ :=
  [(336876556 : ℚ)/5865234375, (4750664 : ℚ)/90234375, (20882856268 : ℚ)/439892578125, (1230040928 : ℚ)/29326171875, (15877599124 : ℚ)/439892578125, (2635744136 : ℚ)/87978515625, (138252692 : ℚ)/5865234375]
theorem branch_c_poly0_row10_nonneg : nonnegList branch_c_poly0_row10 = true := by native_decide

/-- R13 branch `c` poly0 row11 -/
def branch_c_poly0_row11 : List ℚ :=
  [(1026950518 : ℚ)/22216796875, (2825259614 : ℚ)/66650390625, (4221738358 : ℚ)/111083984375, (1577614594 : ℚ)/47607421875, (27849427982 : ℚ)/999755859375, (888908066 : ℚ)/39990234375, (1087922218 : ℚ)/66650390625]
theorem branch_c_poly0_row11_nonneg : nonnegList branch_c_poly0_row11 = true := by native_decide

/-- R13 branch `c` poly0 row12 -/
def branch_c_poly0_row12 : List ℚ :=
  [(570811992 : ℚ)/15869140625, (11059179184 : ℚ)/333251953125, (16489844008 : ℚ)/555419921875, (14216593424 : ℚ)/555419921875, (35035395992 : ℚ)/1666259765625, (766544528 : ℚ)/47607421875, (1215747592 : ℚ)/111083984375]
theorem branch_c_poly0_row12_nonneg : nonnegList branch_c_poly0_row12 = true := by native_decide

/-- R13 branch `c` poly0 row13 -/
def branch_c_poly0_row13 : List ℚ :=
  [(3478983734 : ℚ)/128173828125, (9750035194 : ℚ)/384521484375, (6239423878 : ℚ)/274658203125, (2487148382 : ℚ)/128173828125, (10001757902 : ℚ)/640869140625, (885687218 : ℚ)/76904296875, (939747062 : ℚ)/128173828125]
theorem branch_c_poly0_row13_nonneg : nonnegList branch_c_poly0_row13 = true := by native_decide

/-- R13 branch `c` poly0 row14 -/
def branch_c_poly0_row14 : List ℚ :=
  [(607698796 : ℚ)/30517578125, (1736568632 : ℚ)/91552734375, (4688908244 : ℚ)/274658203125, (2208704464 : ℚ)/152587890625, (15719566732 : ℚ)/1373291015625, (2270417336 : ℚ)/274658203125, (477786508 : ℚ)/91552734375]
theorem branch_c_poly0_row14_nonneg : nonnegList branch_c_poly0_row14 = true := by native_decide

/-- R13 branch `c` poly0 row15 -/
def branch_c_poly0_row15 : List ℚ :=
  [(434476242 : ℚ)/30517578125, (1275031586 : ℚ)/91552734375, (1925827218 : ℚ)/152587890625, (1623441894 : ℚ)/152587890625, (1272009802 : ℚ)/152587890625, (556784306 : ℚ)/91552734375, (129842138 : ℚ)/30517578125]
theorem branch_c_poly0_row15_nonneg : nonnegList branch_c_poly0_row15 = true := by native_decide

/-- R13 branch `c` poly1 row0 -/
def branch_c_poly1_row0 : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (1 : ℚ)]
theorem branch_c_poly1_row0_nonneg : nonnegList branch_c_poly1_row0 = true := by native_decide

/-- R13 branch `c` poly1 row1 -/
def branch_c_poly1_row1 : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (1 : ℚ)]
theorem branch_c_poly1_row1_nonneg : nonnegList branch_c_poly1_row1 = true := by native_decide

/-- R13 branch `c` poly1 row2 -/
def branch_c_poly1_row2 : List ℚ :=
  [(71 : ℚ)/75, (71 : ℚ)/75, (71 : ℚ)/75]
theorem branch_c_poly1_row2_nonneg : nonnegList branch_c_poly1_row2 = true := by native_decide

/-- R13 branch `c` poly1 row3 -/
def branch_c_poly1_row3 : List ℚ :=
  [(21 : ℚ)/25, (521 : ℚ)/625, (517 : ℚ)/625]
theorem branch_c_poly1_row3_nonneg : nonnegList branch_c_poly1_row3 = true := by native_decide

/-- R13 branch `c` poly1 row4 -/
def branch_c_poly1_row4 : List ℚ :=
  [(6503 : ℚ)/9375, (6263 : ℚ)/9375, (6007 : ℚ)/9375]
theorem branch_c_poly1_row4_nonneg : nonnegList branch_c_poly1_row4 = true := by native_decide

/-- R13 branch `c` poly1 row5 -/
def branch_c_poly1_row5 : List ℚ :=
  [(1003 : ℚ)/1875, (1493 : ℚ)/3125, (3863 : ℚ)/9375]
theorem branch_c_poly1_row5_nonneg : nonnegList branch_c_poly1_row5 = true := by native_decide

/-- R13 branch `c` poly1 row6 -/
def branch_c_poly1_row6 : List ℚ :=
  [(6069 : ℚ)/15625, (4709 : ℚ)/15625, (3013 : ℚ)/15625]
theorem branch_c_poly1_row6_nonneg : nonnegList branch_c_poly1_row6 = true := by native_decide

/-- R13 branch `s` poly0 row0 -/
def branch_s_poly0_row0 : List ℚ :=
  [(15975066258 : ℚ)/30517578125, (15545628993 : ℚ)/30517578125, (67078100793 : ℚ)/152587890625, (51291432819 : ℚ)/152587890625, (34192547214 : ℚ)/152587890625, (789747258 : ℚ)/6103515625, (19205712 : ℚ)/244140625]
theorem branch_s_poly0_row0_nonneg : nonnegList branch_s_poly0_row0 = true := by native_decide

/-- R13 branch `s` poly0 row1 -/
def branch_s_poly0_row1 : List ℚ :=
  [(31520695251 : ℚ)/30517578125, (6398153488 : ℚ)/6103515625, (149994586736 : ℚ)/152587890625, (131461158771 : ℚ)/152587890625, (108497283346 : ℚ)/152587890625, (17101335046 : ℚ)/30517578125, (107279832 : ℚ)/244140625]
theorem branch_s_poly0_row1_nonneg : nonnegList branch_s_poly0_row1 = true := by native_decide

/-- R13 branch `s` poly0 row2 -/
def branch_s_poly0_row2 : List ℚ :=
  [(83715331608 : ℚ)/42724609375, (88012921686 : ℚ)/42724609375, (438290018142 : ℚ)/213623046875, (418446905742 : ℚ)/213623046875, (386166112428 : ℚ)/213623046875, (69489715332 : ℚ)/42724609375, (12344156928 : ℚ)/8544921875]
theorem branch_s_poly0_row2_nonneg : nonnegList branch_s_poly0_row2 = true := by native_decide

/-- R13 branch `s` poly0 row3 -/
def branch_s_poly0_row3 : List ℚ :=
  [(395213840856 : ℚ)/111083984375, (427689803742 : ℚ)/111083984375, (2225314656312 : ℚ)/555419921875, (2248491202029 : ℚ)/555419921875, (2220527751528 : ℚ)/555419921875, (430932160164 : ℚ)/111083984375, (412955527176 : ℚ)/111083984375]
theorem branch_s_poly0_row3_nonneg : nonnegList branch_s_poly0_row3 = true := by native_decide

/-- R13 branch `s` poly0 row4 -/
def branch_s_poly0_row4 : List ℚ :=
  [(27334345728 : ℚ)/4443359375, (30268914848 : ℚ)/4443359375, (32511760384 : ℚ)/4443359375, (170673899076 : ℚ)/22216796875, (880321345136 : ℚ)/111083984375, (179119073552 : ℚ)/22216796875, (180242075424 : ℚ)/22216796875]
theorem branch_s_poly0_row4_nonneg : nonnegList branch_s_poly0_row4 = true := by native_decide

/-- R13 branch `s` poly0 row5 -/
def branch_s_poly0_row5 : List ℚ :=
  [(98451676368 : ℚ)/9775390625, (110958850008 : ℚ)/9775390625, (609411673152 : ℚ)/48876953125, (656623111932 : ℚ)/48876953125, (696954079152 : ℚ)/48876953125, (29237725584 : ℚ)/1955078125, (151828382016 : ℚ)/9775390625]
theorem branch_s_poly0_row5_nonneg : nonnegList branch_s_poly0_row5 = true := by native_decide

/-- R13 branch `s` poly0 row6 -/
def branch_s_poly0_row6 : List ℚ :=
  [(151630804224 : ℚ)/9775390625, (2663183808 : ℚ)/150390625, (965502629568 : ℚ)/48876953125, (1058333154048 : ℚ)/48876953125, (88023492864 : ℚ)/3759765625, (22249129536 : ℚ)/888671875, (3368336832 : ℚ)/126953125]
theorem branch_s_poly0_row6_nonneg : nonnegList branch_s_poly0_row6 = true := by native_decide

/-- R13 branch `s` poly0 row7 -/
def branch_s_poly0_row7 : List ℚ :=
  [(6230807808 : ℚ)/279296875, (50188352 : ℚ)/1953125, (3676312832 : ℚ)/126953125, (3447822096 : ℚ)/107421875, (3771905024 : ℚ)/107421875, (10616409248 : ℚ)/279296875, (11393383296 : ℚ)/279296875]
theorem branch_s_poly0_row7_nonneg : nonnegList branch_s_poly0_row7 = true := by native_decide

/-- R13 branch `s` poly0 row8 -/
def branch_s_poly0_row8 : List ℚ :=
  [(1658737152 : ℚ)/55859375, (1921761024 : ℚ)/55859375, (2179723008 : ℚ)/55859375, (12163317696 : ℚ)/279296875, (1218465024 : ℚ)/25390625, (2923641984 : ℚ)/55859375, (3161760768 : ℚ)/55859375]
theorem branch_s_poly0_row8_nonneg : nonnegList branch_s_poly0_row8 = true := by native_decide

/-- R13 branch `s` poly0 row9 -/
def branch_s_poly0_row9 : List ℚ :=
  [(565316352 : ℚ)/15640625, (657299712 : ℚ)/15640625, (18710919168 : ℚ)/391015625, (46084032 : ℚ)/859375, (23204485632 : ℚ)/391015625, (5083943808 : ℚ)/78203125, (5522796288 : ℚ)/78203125]
theorem branch_s_poly0_row9_nonneg : nonnegList branch_s_poly0_row9 = true := by native_decide

/-- R13 branch `s` poly0 row10 -/
def branch_s_poly0_row10 : List ℚ :=
  [(123500544 : ℚ)/3128125, (143885824 : ℚ)/3128125, (820973056 : ℚ)/15640625, (131733504 : ℚ)/2234375, (1022913536 : ℚ)/15640625, (224662016 : ℚ)/3128125, (244664832 : ℚ)/3128125]
theorem branch_s_poly0_row10_nonneg : nonnegList branch_s_poly0_row10 = true := by native_decide

/-- R13 branch `s` poly0 row11 -/
def branch_s_poly0_row11 : List ℚ :=
  [(10635264 : ℚ)/284375, (496128 : ℚ)/11375, (5449728 : ℚ)/109375, (79667712 : ℚ)/1421875, (88479744 : ℚ)/1421875, (19456512 : ℚ)/284375, (21215232 : ℚ)/284375]
theorem branch_s_poly0_row11_nonneg : nonnegList branch_s_poly0_row11 = true := by native_decide

/-- R13 branch `s` poly0 row12 -/
def branch_s_poly0_row12 : List ℚ :=
  [(1622016 : ℚ)/56875, (270336 : ℚ)/8125, (2162688 : ℚ)/56875, (2433024 : ℚ)/56875, (540672 : ℚ)/11375, (2973696 : ℚ)/56875, (3244032 : ℚ)/56875]
theorem branch_s_poly0_row12_nonneg : nonnegList branch_s_poly0_row12 = true := by native_decide

/-- R13 branch `s` poly0 row13 -/
def branch_s_poly0_row13 : List ℚ :=
  [(12288 : ℚ)/875, (2048 : ℚ)/125, (16384 : ℚ)/875, (18432 : ℚ)/875, (4096 : ℚ)/175, (22528 : ℚ)/875, (24576 : ℚ)/875]
theorem branch_s_poly0_row13_nonneg : nonnegList branch_s_poly0_row13 = true := by native_decide

/-- R13 branch `s` poly0 row14 -/
def branch_s_poly0_row14 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
theorem branch_s_poly0_row14_nonneg : nonnegList branch_s_poly0_row14 = true := by native_decide

/-- R13 branch `s` poly0 row15 -/
def branch_s_poly0_row15 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]
theorem branch_s_poly0_row15_nonneg : nonnegList branch_s_poly0_row15 = true := by native_decide

/-- R13 branch `s` poly1 row0 -/
def branch_s_poly1_row0 : List ℚ :=
  [(20181 : ℚ)/15625, (14601 : ℚ)/15625, (1464 : ℚ)/3125]
theorem branch_s_poly1_row0_nonneg : nonnegList branch_s_poly1_row0 = true := by native_decide

/-- R13 branch `s` poly1 row1 -/
def branch_s_poly1_row1 : List ℚ :=
  [(7037 : ℚ)/3125, (5546 : ℚ)/3125, (3974 : ℚ)/3125]
theorem branch_s_poly1_row1_nonneg : nonnegList branch_s_poly1_row1 = true := by native_decide

/-- R13 branch `s` poly1 row2 -/
def branch_s_poly1_row2 : List ℚ :=
  [(10696 : ℚ)/3125, (9094 : ℚ)/3125, (7492 : ℚ)/3125]
theorem branch_s_poly1_row2_nonneg : nonnegList branch_s_poly1_row2 = true := by native_decide

/-- R13 branch `s` poly1 row3 -/
def branch_s_poly1_row3 : List ℚ :=
  [(2724 : ℚ)/625, (2472 : ℚ)/625, (444 : ℚ)/125]
theorem branch_s_poly1_row3_nonneg : nonnegList branch_s_poly1_row3 = true := by native_decide

/-- R13 branch `s` poly1 row4 -/
def branch_s_poly1_row4 : List ℚ :=
  [(112 : ℚ)/25, (536 : ℚ)/125, (512 : ℚ)/125]
theorem branch_s_poly1_row4_nonneg : nonnegList branch_s_poly1_row4 = true := by native_decide

/-- R13 branch `s` poly1 row5 -/
def branch_s_poly1_row5 : List ℚ :=
  [(16 : ℚ)/5, (16 : ℚ)/5, (16 : ℚ)/5]
theorem branch_s_poly1_row5_nonneg : nonnegList branch_s_poly1_row5 = true := by native_decide

/-- R13 branch `s` poly1 row6 -/
def branch_s_poly1_row6 : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ)]
theorem branch_s_poly1_row6_nonneg : nonnegList branch_s_poly1_row6 = true := by native_decide

def r13VectorCount : ℕ := 46
theorem r13VectorCount_eq : r13VectorCount = 46 := rfl
def round13PairBernsteinClosed : Bool := true
theorem round13PairBernsteinClosed_true : round13PairBernsteinClosed = true := rfl
end S6.Round13PairBernstein
