# 复现说明（arXiv ancillary）

英文主说明见 `REPRODUCE.md`。此处仅作中文摘要。

## 要做什么
1. `cd lean/S6Core && lake build`（toolchain `v4.35.0`，mathlib 同 pin）
2. 查看 `still_S/STILL_S_BLOCKED_zh.md`：`still_S = 0`
3. 抽查 `audit/` 与 `certs/` 注册表；关键 round 的 checker 在 `checkers/`

## 诚实边界
- **可宣称：** 计算机辅助意义下 \(S(6)=2\) 数学完备
- **不可宣称：** 已完成独立外部同行评审；每一条度量不等式已全 Lean 重证

细节见 `docs/UPLOAD_GATE_zh.md`。
