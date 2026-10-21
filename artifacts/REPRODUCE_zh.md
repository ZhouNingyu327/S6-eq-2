# 复现说明（中文摘要）

详见同目录 [`REPRODUCE.md`](REPRODUCE.md)。要点：

1. 公开口径为**计算机辅助候选**论证；**不宣称**已确认解决 \(S(6)=2\)。缺口见 `referee_pack/KNOWN_GAPS.md`。
2. Lean 中 `wholeTheorem_S6_eq_2_closed` 等布尔值为**状态元数据**，不是几何定理。
3. 长验证稿在 `artifacts/long_proof/`；R64 等伴侣证书在 `artifacts/checkers/`。
4. `ex/all/` 已随 `ex_all.tar.gz` 与 `SHA256SUMS.txt` 上架。
5. 干净树可跑：`check_round64.py`、`check_round63.py`、`m3_branch_checker.py`。
