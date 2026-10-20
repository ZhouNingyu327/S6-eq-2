# Six unit squares cannot cover a square of side > 2

**Theorem.** \(S(6)=2\), or equivalently \(\Pi(2)=7\).

Six closed unit squares (rigid motions and overlaps allowed) cannot cover any Euclidean square of side strictly greater than \(2\). Side \(2\) is attained by the obvious \(2\times 2\) tiling. This resolves the conjecture of Dósa–Lángi–Tuza (arXiv:2601.16535).

| | |
|---|---|
| **Author** | Ningyu Zhou (School of Physics, Peking University) |
| **Status (2026-10-21, Asia/Shanghai)** | Mathematically complete (computer-assisted); **no** independent external peer review; **no** full Lean re-proof of every metric inequality |
| **Primary PDF** | [`paper/main.pdf`](paper/main.pdf) |
| **Source** | [`paper/main.tex`](paper/main.tex) |
| **Companion** | [`ancillary/`](ancillary/) (Lean 4 skeleton, reproduce notes, selected certificates) |

## Accuracy tier (read this)

- **Claimed:** computer-assisted proof that \(S(6)=2\), with `still_S=0`, Lean obligations 1–4 closed (0 `sorry` / extra axioms in the shipped skeleton), and soft residuals classified non-blocking in the internal audit.
- **Not claimed:** independent journal peer review; a full Lean formalisation of every inequality in the long verification manuscript.
- Full leaf-certificate JSON trees (`ex/all/`) are **omitted** here for size; see `ancillary/REPRODUCE.md` §4.

中文状态见 [`docs/STATUS_zh.md`](docs/STATUS_zh.md)。

## Quick start

1. Read **`paper/main.pdf`** (theorem paper).
2. For machine checks / Lean: start at **`ancillary/REPRODUCE.md`** (or `REPRODUCE_zh.md`), index in `ancillary/MANIFEST.md`.
3. Optional one-shot archive: `arxiv_submission_bundle.tar.gz` (same contents packaged for arXiv ancillary).

## Repository layout

```
paper/          # AMS-style theorem paper (PDF + TeX + bib)
ancillary/      # Lean S6Core, scripts, selected certs, reproduce docs
docs/           # Chinese status / publish notes
arxiv_submission_bundle.tar.gz
README.md       # this file
README_zh.md    # 中文说明
CITATION.cff
LICENSE         # CC BY-NC-ND 4.0 for text; code under MIT (see LICENSE)
```

## Citation

```bibtex
@unpublished{Zhou2026S6,
  author = {Zhou, Ningyu},
  title  = {Six unit squares cannot cover a square of side greater than 2},
  year   = {2026},
  note   = {Computer-assisted preprint; GitHub release},
  url    = {https://github.com/ZhouNingyu327/S6-eq-2}
}
```

## Contact

Ningyu Zhou — `zhouningyu27@gmail.com` · school email `nyzhou25@stu.pku.edu.cn`
