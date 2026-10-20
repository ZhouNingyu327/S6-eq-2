# M7 / M8–M11 证书盘点

更新：2026-10-20 Asia/Shanghai（miss_certs dual 重跑后）

| 块 | 脚本数 | catalog/CERT | exact 升级 | 仍(S) | dual-wrapper 通过 |
|---|---|---|---|---|---|
| M7 | 14 | 222 | 70 | **0** | SMT 侧清零 |
| M8 | 3 | 3 | 2 | **0** | 3/3 |
| M9 | 17 | 21 | 0 | 0 | **20/21** |
| M10 | 3 | 4 | 0 | 0 | **4/4** |
| M11 | 2 | 3 | 0 | 0 | **3/3** |

**全局 still_S = 0**。M8–M11 registry：`m8/m9/m10/m11_certificate_registry.json`。

## 卸除阻碍（crisp）

- **M7**: SMT still_S=0；Lean `S6Core.M7_1` 骨架 certificate-discharged；PDF 前提对齐仍 blocked
- **M8**: registry 接线；R41/R42 dual PASS
- **M9–M11**: miss_certs 后主 checker PASS；`check_round55` 由 `check_round55_final` 取代；PDF 几何仍 blocked

## 按脚本

| 块 | round | file | catalog | exact | still_S | status |
|---|---|---|---|---|---|---|
| M10 | 60 | check_round60 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M10 | 61 | check_round61 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M10 | 62 | check_round62 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M11 | 63 | check_round63 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M11 | 64 | check_round64 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M7 | 29 | check_round29_far_top_complete | 17 | 2 | 0 | no-remaining-S |
| M7 | 29 | check_round29_no_top_structure | 9 | 4 | 1 | still-S:0 |
| M7 | 29 | check_round29_no_top_structure_original_20261014 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M7 | 30 | check_round30_corrected_geometry | 21 | 6 | 2 | still-S:0 |
| M7 | 31 | check_round31_extended_pair | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M7 | 31 | check_round31_three_nonempty | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M7 | 32 | check_round32_right_positive | 28 | 8 | 4 | still-S:0 |
| M7 | 33 | check_round33_right_nonempty | 26 | 6 | 2 | still-S:0 |
| M7 | 34 | check_round34_left_negative | 23 | 10 | 5 | still-S:0 |
| M7 | 35 | check_round35_positive_H | 20 | 7 | 2 | still-S:0 |
| M7 | 36 | check_round36_nonempty_closed | 19 | 11 | 1 | still-S:0 |
| M7 | 37 | check_round37_empty_left_negative | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M7 | 38 | check_round38_empty_right_negative | 30 | 10 | 5 | still-S:0 |
| M7 | 39 | check_round39_single_contact | 29 | 6 | 2 | still-S:0 |
| M8 | 41 | check_round41_certificates | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M8 | 41 | check_round41_geometry | 8 | 2 | 0 | no-remaining-S |
| M8 | 42 | check_round42 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 44 | check_round44 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 45 | check_round45 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 46 | check_round46 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 47 | check_round47 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 47 | check_round47_forced_fit | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 48 | check_round48 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 49 | check_round49 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 50 | check_round50 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 51 | check_round51 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 52 | check_round52 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 53 | check_round53 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 54 | check_round54 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 55 | check_round55_final | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 56 | check_round56 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 57 | check_round57 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 58 | check_round58 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
| M9 | 59 | check_round59 | 0 | 0 | 0 | checker-present-not-in-dual-catalog |
