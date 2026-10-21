# Changelog

## 2026-10-21 — 缺口推进（相对 `8672f31`）

- Lean：`Faithfulness.lean` + 分类回归；README / formalization.yaml 区分已证与开放。
- 内部 G5 重建笔记（EN+ZH）；外部审稿项保持开放。
- 强 M1 明确为延期；主协议仍为逐步重分类。
- Item3 升级台账与剩余 (S) 清单入库。
- 短文 §§5–7 增加 Hyp⇒Concl 模块表。

# 变更说明

## 2026-10-21 — Lean Major 3 接口 + 规范化迁移说明（相对 `5bfd66a`）

- **分类标志：** 默认 API 改为 `flagsOfTarget*`（四个目标外中点 + `F∋O`）；旧 MidCandidates 接线仅留在 `legacyFlagsOf*`。
- **回归例子：** `ClassificationExample.lean` 复审局部例子在新 API 下为 `k=1`、`fHasO=false`。
- **角色：** `iF`=第六块；`toManuscript` 用同一 `pullback` 把自由块拉到中心体坐标。
- **规范化：** 增加 `M1_module_migration_zh.md`；长稿“后续恒等”限定为可选强方案。
- **不声称：** 端到端忠实性定理、外部审稿、或强 M1 升格。


## 2026-10-21 — 复审修订（相对 `32e0e0f`）

按 2026-10-21 公开仓复审意见修改（不发明新几何）：

- **R8：** 交付 `artifacts/ex/all/round8_pair_bernstein_certificate.json`（45 叶；`checkers/` 有副本）。
- **R13：** 交付 `round13_pair_certificate.json`。
- **R16：** 写入两步生成 + Fraction 核验命令。
- **R6：** 长稿 Markdown 相切笔误改为 `d0≥0`，并用 `c(1−α)+sβ≥μ>1`。
- **规范化：** 主协议=短文逐步重分类；附录 A/长稿 M1=可选强方案候选；闭象限+轴向分支；`W`=全局预处理后的自由角块。
- **复现卫生：** g3 的 R38/R39 指向长稿锚点；去掉与已交付 `ex/all` 冲突的旧叙述。
- **Lean Major 3：** **仍开放**（仅加强注释）。

详见 [`referee_pack/KNOWN_GAPS_zh.md`](referee_pack/KNOWN_GAPS_zh.md)。英文完整日志见 [`CHANGELOG.md`](CHANGELOG.md)。
