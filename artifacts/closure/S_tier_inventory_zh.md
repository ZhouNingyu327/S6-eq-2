# 剩余 (S) 级双求解器清单

**时间：** 2026-10-21（Asia/Shanghai）。
**来源：** `artifacts/closure/item3_certs/`、`certificate_counts.json`、`M4_unsat_inventory.md`。

标签：**(E)** 精确证书；**(H)** 手证+求解器交叉；**(S)** 仅双求解器 UNSAT（非机器无关证明）。

## 总表

| 量 | 值 |
| --- | --- |
| Item3 去重键 | 264 |
| Item3 升为 exact（唯一） | 113 |
| 仍为 (S) / cvc5-only（唯一） | **151** |
| 跟踪唯一合计（M4） | 391 |
| 约 (E)/(H) 占比 | ~61% |
| 约 (S) 占比 | ~39% |

## 按核验文件的剩余 (S)

| 核验文件 | 剩余 (S) | Item3 已 exact |
| --- | ---: | ---: |
| `check_round34_left_negative` | 15 | 6 |
| `check_round38_empty_right_negative` | 15 | 7 |
| `check_round26_g2_top` | 13 | 7 |
| `check_round28_g2_near_complete` | 12 | 3 |
| `check_round32_right_positive` | 12 | 1 |
| `check_round36_nonempty_closed` | 12 | 4 |
| `check_round27_g2_two_branches` | 11 | 19 |
| `check_round25_g3_complete` | 10 | 13 |
| `check_round35_positive_H` | 9 | 4 |
| `check_round24_g3_fside` | 8 | 8 |
| `check_round30_corrected_geometry` | 8 | 4 |
| `check_round33_right_nonempty` | 8 | 5 |
| `check_round39_single_contact` | 8 | 16 |
| `check_round29_no_top_structure` | 5 | 1 |
| `check_round29_far_top_complete` | 2 | 9 |
| `check_round41_geometry` | 2 | 1 |
| `check_round24_g3_cside` | 1 | 5 |

本推送将既有 Item3 升级台账纳入公开树；**未**新造叶子证书。剩余 (S) 仍只能当双求解器证据。
