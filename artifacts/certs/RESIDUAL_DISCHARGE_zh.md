# 残留义务：如何卸除（精确清单）

**时间：** 2026-10-20（Asia/Shanghai）  
**全局 still_S = 0**（b23d）。详见 `certs/THEOREM_LEVEL_GAP_zh.md`。

## 1. `general_rotated_f_formula`

| 已有（Lean） | 卸除尚缺 |
|---|---|
| `f` 代数；`f_cleared`；相似三角形乘积；边法向平行弦 ≤1；`FreeEndpointChart`；**`ChartHypotheses` ⇒ chord = f** | 任意刚体运动下构造 chart / 证归约到边法向 |

**卸除判据：** Lean：任意定向单位正方形平行割线弦长 = `f(z,d)`。  
**当前：** 条件识别已闭；刚体 → chart **blocked**。

## 2. `far_end_reduction_M7`（命题 M7.1）

| 步 | 模块 | 状态 |
|---|---|---|
| 1–4 / 3′ | R27–R39 | SMT still_S=0；`S6Core.M7_1` certificate-discharged |
| 前提对齐 / Lean 几何 | — | **blocked**（`premiseAligned = false`） |

**卸除判据：** 五步前提对齐 + Lean 几何，或等价 PDF 形式化。

## 3. `final_form_M8_M11`

| 块 | dual-wrapper | blocked |
|---|---|---|
| M8 | PASS；registry 接线 | Lean/PDF 几何 |
| M9 | 主 checker PASS（miss_certs）；R55→final | 同上 |
| M10 | PASS | 同上 |
| M11 | PASS | 同上 |

## 4. `top_class_G1_G5`

布尔已卸。`OwnershipBridge` 提供 `CoveringFlags` 条件运输。  
**blocked：** 欧氏覆盖 → `CoveringFlags`。

## 5. `near_end_leaf_closures`

**17/17 全证书**。PDF→Lean 几何可选。
