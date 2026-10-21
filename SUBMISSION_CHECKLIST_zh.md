# 投稿前清单

**口径：** 计算机辅助**候选**论证，已整理供外审；**不是**“定理已确认 / 已同行评审”。

## 材料

- [x] 短文 PDF（含审稿指南与 M1–M4 附录）
- [x] 长验证稿 `artifacts/long_proof/`
- [x] `artifacts/closure/` 与 `m3_branch_checker.py`
- [x] `ex_all.tar.gz` + `SHA256SUMS.txt` + `ex/all/`
- [x] `check_round64` / `check_round63` 干净树通过
- [x] `referee_pack/` 阅读路径齐全
- [x] Lean 旗标为元数据；Major 3 在 KNOWN_GAPS 标明开放
- [ ] 外部独立人类审稿意见
- [ ] 期刊/arXiv 最终套排（若需要）

## 允许 / 禁止措辞

允许：提出 \(S(6)=2\) 的计算机辅助候选论证；欢迎独立核验。  
禁止：已证明 / 已解决 / 业经同行评审确认；Lean 已完成几何全定理；全部 SMT 均有机器无关精确证书。

## 字段备忘

| 字段 | 建议 |
| --- | --- |
| Title | Six unit squares cannot cover a square of side greater than 2 |
| Authors | 按期刊披露政策；见 `DISCLOSURE.md` |
| MSC | 52C15; 52C17, 68Q60, 68V15 |
| Ancillary | GitHub 或上传 `artifacts/` |
| Cover letter | `referee_pack/CONTACT_DRAFT.txt` |
