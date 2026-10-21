# 复现说明（中文摘要）

详见同目录 [`REPRODUCE.md`](REPRODUCE.md)。要点：

1. 公开口径为**计算机辅助候选**论证；**不宣称**已确认解决 \(S(6)=2\)。缺口见 `referee_pack/KNOWN_GAPS.md`。
2. Lean 中布尔完成旗标为**状态元数据**，不是几何定理；Major 3（分类语义）仍开放。
3. 长验证稿以 `artifacts/long_proof/S6_full_proof.md` 为源；PDF 可能滞后。
4. `ex/all/` 已上架；**R8 / R13** 证书已随检查器交付；**R16** 需先生成树再核验（命令见英文版 §5）。
5. 干净树建议先跑：`check_round8_two_corners.py`、`check_round13_pair.py`、`check_round64.py`、`check_round63.py`、`m3_branch_checker.py`。
6. 规范化**主协议**为短文逐步重分类；附录 A / 长稿 M1 为可选强方案候选。
