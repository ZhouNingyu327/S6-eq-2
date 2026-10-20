# arXiv 提交就绪清单（终检）

**时间：** 2026-10-21（Asia/Shanghai）  
**论文：** Ningyu Zhou — Six unit squares cannot cover a square of side greater than 2  
**数学状态：** \(S(6)=2\) **已证**（计算机辅助完整链）

图例：☑ = 代理已完成；☐ = **只有你本人能做**（账号 / 点击 Submit / 背书等）

---

## A. 数学与文稿（代理已做）

| 项 | 状态 |
|---|---|
| 义务 1–4 闭合；全定理旗标已证 | ☑ |
| Lean `lake build` 0 axiom / 0 sorry（作者环境已验证） | ☑ |
| `still_S=0` 证据写入 ancillary | ☑ |
| 英文完整论文 `main.tex` / `main.pdf`（可写 We prove；未声称同行评审 / 全度量 Lean） | ☑ |
| 引用 Dósa–Lángi–Tuza arXiv:2601.16535 | ☑ |
| Accuracy tier 摘要 + Remark | ☑ |
| `ancillary/`（Lean 源、certs、checkers、still_S、audit、docs、MANIFEST、REPRODUCE） | ☑ |
| `arxiv_submission_bundle.tar.gz`（main.tex + refs.bib + main.pdf + ancillary/） | ☑ |
| 闸门文档 `UPLOAD_GATE_zh.md` / `PUBLISH_CHECKLIST_zh.md` | ☑ |
| **实际向 arXiv 上传 / 点 Submit** | ☐ **禁止由代理代劳；需你本人操作** |
| **发送知会邮件给 Soifer 等** | ☐ 需你本人确认后再发 |

---

## B. 只有你能做的步骤

1. ☐ 通读 `main.pdf`（11 页），确认署名、单位、邮箱、定理句。
2. ☐ 登录 / 注册 [arXiv](https://arxiv.org)（建议邮箱 `zhouningyu27@gmail.com`）。
3. ☐ 若账号无 `math.MG` endorsement：请有资格的研究者背书（导师或同领域）。
4. ☐ 新建 submission：
   - Primary: `math.MG`
   - Cross-list: `math.CO`（可选 `cs.CG`）
   - 上传 `arxiv_submission_bundle.tar.gz` 内容（或按 arXiv 界面分别传 `.tex`/`.bib`/`.pdf` + ancillary zip）
5. ☐ Comments 建议写法：  
   `Computer-assisted proof of S(6)=2 (equivalently Π(2)=7). Ancillary: Lean 4 skeleton + certificate registries. Resolves conjecture of Dósa–Lángi–Tuza, arXiv:2601.16535. Not peer-reviewed.`
6. ☐ 预览编译无误后 **点 Submit**（代理不会点）。
7. ☐ 挂出后：投 *Discrete & Computational Geometry*；可选礼貌知会 Soifer / Januszewski / DLT。

---

## C. 包位置

- 本机（box）：`/workspace/uploads/s6_user_proof/arxiv_prep/arxiv_submission_bundle.tar.gz`
- 你的电脑：`C:\Users\电脑GT14\Documents\Codex\2026-10-08\za\outputs\arxiv_prep\`

## D. 诚实口径（对外一句）

**计算机辅助证明，数学上已完备；欢迎独立复核。**  
未声称：已过同行评审；每一条度量不等式已全 Lean 化。
