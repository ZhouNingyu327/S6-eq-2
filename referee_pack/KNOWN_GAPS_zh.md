# 已知缺口

## 本轮推进（相对 `8d5dee0`）

- `AxisGridContribution` / `G5GeometryBridge`：轴对齐外角贡献、geom-export⇒bridge⇒G5Exclusion 组合已证；旋转弦测度导出仍开。
- Near-end 7/24 表不可能叶 ⇒ LivingLeafExcluded；17 living 仍开。
- G3/G4 预算桥细化；`principalClaimProvedUnconditionally=false`。


相对 2026-10-21 对 `32e0e0f` 的复审、`8672f31` 的 API 修复，以及本轮缺口推进。

| 事项 | 状态（本推送后） |
| --- | --- |
| R8 / R13 证书 | **已交付** |
| R16 复现说明 | **已写入** |
| R6 相切笔误 | **已改** |
| 规范化协议 | **主协议=逐步重分类**；强 M1=可选/**延期**；迁移证明仍开放 |
| Lean Major 3 / 主定理 | **Prop 主声明 + 约化骨架已交付**；`G1…G5Exclusion` 与无条件主定理仍开放 |
| g3 / REPRODUCE | **已同步** |

## 仍开放

1. **无条件 Lean 主定理 + 端到端忠实性。** 约化骨架 + G5 代数 R2 脊已证；`G5Exclusion` 仅在开放几何桥 `G5k0/k1/k2Bridge` 下成立；`G1…G4Exclusion` 仍开放。长稿忠实性仍开放。
2. **外部独立人类审稿**（早期 G5 几何→代数）。仅有内部重建笔记 `INTERNAL_G5_rebuild_zh.md`，**不关闭**本项。
3. 强规范化若升格所需的逐模块迁移证明（当前延期）。
4. 剩余约 **91** 条 (S) 级双求解器查询（清单见 `S_tier_inventory_zh.md`）。
5. 短文 §§5–7 已加模块表；篇幅上仍可再扩。

## 本轮推进（相对 `634f591`）

- Lean：`G5Budget` / `G5ExclusionFrag` / `G3G4Fragments` / `BernsteinGridLift`。

## 此前（相对 `9fb5ade`）

- Lean：`MainTheorem` / `CoveringGeometry` / `NearEndGeometry` / `G5Fragments`；`hF_ne_corners`；`formalization.yaml` → `partial_formalization_reduction_spine`。
- 此前（`9fb5ade`）：忠实性片段、内部 G5、M1 延期、(S) 清单、短文模块表。


## 2026-10-22 batch24（S）→（E）片段

将 **26** 条原（S）升级为可核 Bernstein/IBB/半角恒等式证书（`exact_certs_batch24/`，检查器 PASS）。
**仍余（S）：125。** 不宣称定理已证。


## 2026-10-22 batch25 续

可核证书累计 **60**；仍余（S）**91**。不宣称定理已证。


## Batch24–26f certificate track (2026-10-22 Asia/Shanghai)

Machine-checkable exact/hand certs in `artifacts/closure/item3_certs/exact_certs_batch24/`: **151** (checker PASS 151/151). Remaining dual-solver (S) from the post-batch25 set of 91: **0**. Does **not** close the theorem; Lean/lake remains a separate gap.
