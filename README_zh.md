# 六个单位正方形不能覆盖边长大于 2 的正方形

**定理。** \(S(6)=2\)，等价于 \(\Pi(2)=7\)。

六个闭单位正方形（允许刚体运动与重叠）无法覆盖边长严格大于 \(2\) 的欧氏正方形；边长 \(2\) 可由显然的 \(2\times 2\) 铺陈达到。此结果解决 Dósa–Lángi–Tuza（arXiv:2601.16535）的猜想。

| | |
|---|---|
| **作者** | 周宁宇（北京大学物理学院） |
| **状态（2026-10-21，Asia/Shanghai）** | 数学上已证（计算机辅助）；**尚未**独立外部同行审稿；**尚未**对长验证手稿中每一条度量不等式做完整 Lean 再证 |
| **主 PDF** | [`paper/main.pdf`](paper/main.pdf) |
| **TeX** | [`paper/main.tex`](paper/main.tex) |
| **附件** | [`ancillary/`](ancillary/)（Lean 4 骨架、复现说明、部分证书） |

## 精度分层（请先读）

- **主张：** 计算机辅助证明 \(S(6)=2\)；`still_S=0`；Lean 义务 1–4 已闭合（交付骨架中 0 `sorry` / 额外公理）；内部审计将软残留标为非阻断。
- **不主张：** 独立期刊审稿；对长验证手稿中全部不等式的完整 Lean 形式化。
- 完整叶子证书 JSON 树（`ex/all/`）因体积**未收录**；见 `ancillary/REPRODUCE.md` §4。

更多中文说明：[`docs/STATUS_zh.md`](docs/STATUS_zh.md)、[`docs/SUBMISSION_READY_zh.md`](docs/SUBMISSION_READY_zh.md)。

## 使用顺序

1. 阅读 **`paper/main.pdf`**。
2. 机器核验 / Lean：从 **`ancillary/REPRODUCE.md`**（或 `REPRODUCE_zh.md`）开始；文件索引见 `ancillary/MANIFEST.md`。
3. 可选整包：`arxiv_submission_bundle.tar.gz`。

## 引用

见英文 [`README.md`](README.md) 中的 BibTeX；仓库公开链接拟为 `https://github.com/ZhouNingyu327/S6-eq-2`。
