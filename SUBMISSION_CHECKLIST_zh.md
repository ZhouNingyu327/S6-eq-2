# 投稿前清单（诚实版）

**口径：** 计算机辅助**候选**证明包，已整理供外部审稿；**不是**“定理已确认 / 已同行评审”。

## 仓库与材料

- [x] 短文 PDF 可编译，含 Guide for referees 与 M1–M4 附录
- [x] 长验证稿在 `artifacts/long_proof/`
- [x] `artifacts/closure/` 含 M1–M4 与 `m3_branch_checker.py`
- [x] `ex_all.tar.gz` + `SHA256SUMS.txt` + 解压 `ex/all/`
- [x] `check_round64.py` / `check_round63.py` 干净树通过
- [x] `referee_pack/` 入口齐全
- [x] Lean 旗标诚实化为元数据；Major 3 在 KNOWN_GAPS 标明开放
- [ ] 外部独立人类审稿人意见（投稿前强烈建议至少一位）
- [ ] 期刊/arXiv 具体栏目与模板最终套排（若需要）

## 允许的主张语言

- “提出 S(6)=2 的计算机辅助候选论证”
- “材料已按外部审稿可读性整理；准确度分层已披露”
- “欢迎独立核验”

## 禁止的主张语言

- “已证明 / 已解决 / 业经同行评审确认”
- “Lean 已完成几何全定理”
- “全部 SMT 步骤均有机器无关精确证书”

## arXiv / 期刊字段备忘

| 字段 | 建议 |
| --- | --- |
| Title | Six unit squares cannot cover a square of side greater than 2 |
| Authors | 按期刊 AI/披露政策；建议明确 AI 产出 + 发布者周宁宇；勿默认“作者掌握全文” |
| MSC | 52C15 (primary); 52C17, 68Q60, 68V15 |
| License | 仓库 LICENSE；arXiv 选与之兼容选项 |
| Ancillary | 指向 GitHub 或上传 `artifacts/` 关键证书 |
| Endorsement | 新账号数学类 endorsement 仍可能困难；可先私下送 DLT 作者或相关专家；勿伪造 endorsement |
| Cover letter | 使用 `referee_pack/COVER_LETTER_DRAFT.txt` 诚实稿 |

## 伦理

见 [`DISCLOSURE.md`](DISCLOSURE.md)。发送知会邮件前须用户明确批准收件人与正文。
