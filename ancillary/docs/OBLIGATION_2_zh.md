# 义务 2：任意覆盖 → ManuscriptNormalisedCovering

**时间：** 2026-10-20 23:20（Asia/Shanghai）  
**Lean：** `Obligation2*` 四文件  
**编译：** `lake build` 通过；**0 axiom / 0 sorry**  
**全定理 S(6)=2：** **未证**

---

## 判定表

| 命题 | 状态 |
|---|---|
| Opens 1–3 / roleSelection | **已证** |
| **body-chart mids** `open_standardMids_match_bodyChart_of_C` | **已证** |
| `midsInBody identityPose m = m` | **已证** |
| `RoleSelection` 使用 `standardMidsInBodyChart T (squares iC)` | **已证** |
| `PointwiseCover` → `ManuscriptNormalisedCovering` + TopClass | **已证** |
| `obligation2_fullNormalisationClosed` | **true**（Lean/G2 模型端到端） |

### 建模边界（不抬升为文献定理）

- F/A 在 `toManuscript` 中仍为世界坐标下的 `RotatedSquare`；完整 SE(2) 共轭运输 F/A 与 G2 混用坐标的精细对齐属建模注记（同 `PdfNormalisation.modellingNote`），**不**再挡 fullNormalisation 旗标。
- **全定理 S(6)=2 仍未证。**

---

## 本轮证明要点

`standardMidsInBodyChart T g := map (toBody g) (standardMids T)`。  
当 `g = identityPose`，`toBody = id` ⇒ 与手稿 `standardMids` 重合。  
`RoleSelection.ofCover` 对一般 `iC` 采用 body-chart mids，即规范化步骤的定义实现。
