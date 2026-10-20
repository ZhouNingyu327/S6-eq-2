# 定理级缺口清单（still_S = 0 之后）

**时间：** 2026-10-20（Asia/Shanghai）  
**Lean：** `lake build` OK；**0 axiom / 0 sorry**。  
**G1 / G2 / G3：** `G1_overallClosed = true`，`G2_overallClosed = true`，**`G3_overallClosed = true`**（分支逻辑/标准形片段）。  
**诚实：不宣称文献定理。** 度量打包不等式仍在证书层（still_S=0）。

---

## 0. 一句话

G1 弦长桥、G2 规范化片段、G3 M7.1 **分支逻辑 ↔ checker 前置片段 + StandardForm 谓词** 均已在 Lean 关闭。  
定量平行预算 / R13 等度量内容仍由 SMT 证书卸除，**不宣称文献结算**。

---

## 1. 缺口状态

| ID | 子项 | 旗标 | 状态 |
|---|---|---|---|
| G1 | 全套 | `G1_overallClosed` | **闭** |
| G2 | PDF 规范化片段 | `G2_overallClosed` | **闭** |
| G3 | citation 机检 | `G3_checklistClosed` | **闭** |
| G3 | 五步 leanGeometry 片段 | `leanGeometry=true`×5 / `G3_overallClosed` | **闭**（片段） |
| G4–G6 | dual / 审稿 / 文献 | — | dual PASS；审稿未做 |

---

## 2. G3 Lean 几何片段（本轮）

模块：`S6Core/M7_1Geometry.lean`

| 步 | Narrative Prop | Checker 前置片段 | 证明 |
|---|---|---|---|
| topGap | `NarrativeTopGap` + `OuterEdgeState` | `CheckerTopGapPre` 三分法 | `toOuter_toChecker` / `toChecker_toOuter` / `topGap_narrative_iff_checker` |
| FmeetH | `NarrativeFmeetH` + `FHorizStatus` | `CheckerFmeetHPre` empty/nonempty | `FmeetH_nonempty_excluded_implies_empty` 等 |
| sideGap | `NarrativeSideGap.isRightGapBranch` | `CheckerSideGapPre.exclusionBranch` | `sideGap_narrative_iff_checker` |
| sideGapPrime | `NarrativeSideGapPrime.isLeftGapBranch` | `CheckerSideGapPrimePre.exclusionBranch` | `sideGapPrime_narrative_iff_checker` |
| tripleToStd | `NarrativeTripleToStd.ready` | `CheckerStdFormPre` + **`StandardForm`** | `tripleToStd_narrative_iff_checker`；`toStandardForm_wellFormed`；`reduction_to_standardForm` |

**建模说明：** leanGeometry = M3.2/R29N 离散分支逻辑与标准形接口；`check_round29–39` 内度量不等式仍为证书层。

**可选残留（不挡 G3_overallClosed）：** 将平行预算 B(μ)、R13 有理证书等写成 Lean 度量 Prop。

---

## 3. 路径

`M7_1Geometry.lean`、`g3_m7_1_alignment_checklist.json`、`G3_M7_1_ALIGNMENT_zh.md`、`THEOREM_STATUS_zh.md`


---

## 4. 本轮附加

- `S6Core/ParallelBudget.lean` — R29N.2 代数快胜：`8+3B+vF < 12μ`、`8+2B+2μ < 12μ`（不构造几何 B(μ)）
- G4 faithfulness 扩样：`faithfulness_G4_M8_M11_expanded.json`（dual 31/31 PASS）
- 状态包：`/workspace/uploads/s6_user_proof/theorem_pack/`（`THEOREM_CORE_zh.md` + `s6_theorem_pack_sources.tar.gz`）
- **不宣称文献结算。**
