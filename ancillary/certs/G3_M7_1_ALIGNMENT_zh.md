# G3：M7.1 叙事 ↔ 证书假设对齐清单（可机检 + Lean 片段）

**时间：** 2026-10-20（Asia/Shanghai）  
**状态：**
- `G3_checklistClosed = true`
- **`G3_overallClosed = true`**（`M7_1Geometry` 分支逻辑/StandardForm 片段）
- **不宣称文献定理**；度量不等式仍证书层（still_S=0）

| M7.1 步 | Lean ctor | Narrative / Checker Props | lean_geometry |
|---|---|---|---|
| (1) TOP | `topGap` | `NarrativeTopGap` ↔ `CheckerTopGapPre` / `OuterEdgeState` | **true** |
| (2) F∩H | `FmeetH` | `NarrativeFmeetH` ↔ `CheckerFmeetHPre` / `FHorizStatus` | **true** |
| (3) RIGHT | `sideGap` | `NarrativeSideGap` ↔ `CheckerSideGapPre` | **true** |
| (3′) LEFT | `sideGapPrime` | `NarrativeSideGapPrime` ↔ `CheckerSideGapPrimePre` | **true** |
| (4) 标准形 | `tripleToStd` | `StandardForm` / `NarrativeTripleToStd` ↔ `CheckerStdFormPre` | **true** |

机检：`certs/g3_m7_1_alignment_checklist.json` + `audit/g3_alignment_check.py`  
Lean：`S6Core/M7_1.lean`、`S6Core/M7_1Geometry.lean`
