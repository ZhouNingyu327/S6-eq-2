# 变更说明（成熟度修订包）

**日期：** 2026-10-21（Asia/Shanghai）  
**对照审阅：** `/workspace/uploads/S6_public_repository_referee_report_20261021.md`（公开快照 `9930699`）  
**本树路径：** `/workspace/s6_maturity_fix/`（**未**推送 GitHub）

公开口径保持：**AI 产出的计算机辅助候选证明 / GitHub dump**；发布者周宁宇不宣称逐步掌握；不宣称定理已被确认解决。

---

## 审阅五项主要意见 → 本包状态

| 审阅项 | 状态 | 本包做了什么 | 故意延期 / 未完成 |
| --- | --- | --- | --- |
| **Major 1** 关键证明与证书未交付 | **部分完成** | 长验证稿收入 `artifacts/long_proof/`（md+pdf+哈希）；R42/R54/R55/R64 伴侣 JSON 放在 `artifacts/checkers/`（及 `work/`）；`REPRODUCE.md` 改为干净克隆路径；空的 `still_S_after_b23d.jsonl` 换成清单 | 完整 `ex/all/` 树仍省略（见 `artifacts/DOWNLOADS/`）；私有 `closure/*.md` 未并入；命题 5.1/6.1/7.1 正文仍是提纲（未在本轮把长稿全文并进短 PDF） |
| **Major 2** Lean 完成旗标 / True 占位 | **完成（诚实化）** | `WholeTheoremStatus` 标明 STATUS METADATA，并增加 `statusMetadata_candidate_S6_eq_2_flag`；`Exhaustiveness` / `reduction_to_standardForm` 标明 NON-PROOF；README / docs / yaml / 论文 Lean 段同步 | **未**把接口改写成带原始覆盖对象的几何定理（本轮不发明数学） |
| **Major 3** 分类语义失配 | **部分完成（诚实 + 局部重命名）** | `fHasOOf(_rot)` → `fHasAnyMidCandidate(_rot)`（旧名 abbrev）；`kOf` / `midsAdjacent` / `RoleSelection.ofCover` 加 FIXME；文档写明 ownership bridge **尚未**忠实于正文 \(k\) / \(F\ni O\) / 第六块选取 | **未**给出忠实归约证明；未改 classify 数学含义去“假装”已对齐 |
| **Major 4** 一次规范化 ⇒ 后续恒等 | **完成（撤回/削弱）** | 命题改为“支配扩大 + 逐步重分类”；明确幂等性推不出 β 夹取等后续操作恒等；指向 `S6_round65_full_audit.md` §4 | **未**新证一个更强的全局规范化算子 |
| **Major 5** Π 量词错误 | **完成** | 定义/摘要/引言改为存在 \(\varepsilon>0\)；保留 \(S(6)=2\Leftrightarrow\Pi(2)=7\) 叙事并写明依赖已知 \(\Pi(2)\le 7\)；引理 3.2 证明改为闭第一象限 | 七块构造未在本包新给显式图，仅文献指针（Soifer / surveys / DLT 语境） |

### 补充意见

| 项 | 状态 |
| --- | --- |
| `g3_alignment_check.py` 硬编码私有路径 | **完成**：改为仓库相对路径（无 `/workspace/uploads`）；干净克隆会因缺 `closure/*.md` 等报错——属延期交付，已写入结果 JSON |
| 空 `still_S_after_b23d.jsonl` | **完成**：替换为清单 + 一行 jsonl 指针 |
| Lean ℚ 模型 vs 实数原问题 | **延期**（审阅未要求本轮修补） |

---

## 适宜对外表述

> 提出 \(S(6)=2\) 的计算机辅助**候选**证明；公开材料与部分形式化正在根据 2026-10-21 公开快照审阅意见修订核验。  
> **不能**仅凭内部闭合标签、空日志或 Lean 无 sorry，宣称问题已确认解决。

---

## 建议下一步（不在本包内）

1. 将私有 `closure/` 与完整证书入口以固定哈希公开，或提供可下载归档。  
2. 按审阅 3.1–3.3 重写 Lean/正文一致的 \(k\)、\(F\ni O\)、第六块角色选取，并证明字段等价。  
3. 为逐步重分类补全“保点 / 保宿主 / 填平缺口转入分支”的短稿引理链。  
4. 外部同行独立重建最关键归约后再考虑投稿署名规范。
