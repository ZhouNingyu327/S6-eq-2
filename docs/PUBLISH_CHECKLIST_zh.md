# 公布 / 投稿前你需要做的事（Ningyu Zhou）

**时间：** 2026-10-21（Asia/Shanghai）  
**数学完备性：** 已证（计算机辅助完整链；见 UPLOAD_GATE 精度分层）  
**本文用途：** 个人行动清单，不是再审一遍定理。

---

## A. 立刻可做（优先权）

1. **通读终稿** `arxiv_prep/main.tex` / `main.pdf`：确认作者信息、单位、邮箱、定理陈述与你本人理解一致。
2. **准备 ancillary**：Lean 源码树、证书 registry、checker 脚本、`still_S=0` 复现说明、`REPRODUCE_zh.md` 英文化摘要。
3. **注册 / 登录 arXiv**（若还没有）：用 `zhouningyu27@gmail.com`；首次投稿可能需学术背书人（endorsement），可请导师或同领域研究者 endorsement `math.MG`。
4. **挂预印本**：主类 `math.MG`，次类 `math.CO`（可选 `cs.CG`）。Comments 写清：computer-assisted；certificates + Lean skeleton；cite arXiv:2601.16535。
5. **摘要措辞**：可写 “We prove \(S(6)=2\)”；**不要**写已获独立同行评审或全文度量已全 Lean 化。

## B. 投稿期刊

6. **主投** *Discrete & Computational Geometry*（主文 + supplement）。
7. Suggest referees（例）：Soifer；Januszewski；Friedman；Dósa / Lángi / Tuza 中 1–2 人；一位计算机辅助证明向。
8. Competing interests / related work：明确引用 Dósa–Lángi–Tuza 猜想文。

## C. 公布渠道（arXiv 之后）

9. 通知相关作者（礼貌邮件，附 arXiv 链接）：Soifer；Januszewski；Dósa–Lángi–Tuza；可选 Friedman。
10. 可选：个人主页 / 北大相关汇报；GitHub `ZhouNingyu327` 放复现包永久链接。
11. 不要同时一稿两投；会议短报告（EuroCG/SoCG 2027）可在期刊在审时再规划。

## D. 诚实边界（对外口径）

12. 对外统一说：**计算机辅助证明，数学上已完备；欢迎独立复核。**
13. 未做：独立外部同行评审；每一条 R30–64 度量不等式的全 Lean 重证（证书主层）。
