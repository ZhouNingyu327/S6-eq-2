# 变更说明（投稿级外部审稿包）

**日期：** 2026-10-21（Asia/Shanghai）  
**对照：** 公开快照审阅 `9930699` + 成熟度修订 `d2411c5`  
**本树：** `/workspace/s6_submission_ready/` → 推送 `ZhouNingyu327/S6-eq-2` main

公开口径：**AI 产出计算机辅助候选证明**；发布者周宁宇维护 dump、不宣称逐步掌握；**不**宣称定理已确认解决。

## 本包相对成熟度修订新增

1. **`referee_pack/`**：英文优先入口（README、REFEREE_BRIEF、ACCURACY_TIER、KNOWN_GAPS、HOW_TO_REPRODUCE、COVER_LETTER_DRAFT）+ 中文镜像。
2. **短文可读性：** Guide for referees；§§5–7 等命题改为 Hyp⇒Concl + 模块 ID；附录 A–D 并入 M1–M4；重建 `paper.pdf`。
3. **`artifacts/closure/`：** M1–M4 中文源注 + `m3_branch_checker.py`（PASS）。
4. **`artifacts/ex_all.tar.gz`** + 解压 `ex/all/` + `SHA256SUMS.txt`（干净克隆可核对）。
5. **顶层 README** 改为外人单入口：referee pack → paper → long proof → reproduce。
6. **`SUBMISSION_CHECKLIST_zh.md`**：arXiv/期刊字段、披露、允许/禁止措辞。

## 审阅五项对照（摘要）

| 项 | 状态 |
| --- | --- |
| 1 长证明/证书 | 长稿+伴侣证书+ex/all 已上；短文仍提纲 |
| 2 Lean 旗标 | 诚实元数据 |
| 3 分类语义 | **仍开放** |
| 4 规范化强结论 | 短文已削弱；附录 A 为候选手续 |
| 5 Π 量词 | 已修 |

## 适宜对外一句

> 已整理供外部审稿人直接阅读的候选包；准确度分层已披露。**不是**文献意义上结案。
