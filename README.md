# Readme

This repository contains a mathematical manuscript and supporting proof artifacts **produced by a generative AI system**, released publicly in the style of the [OpenAI math collection](https://github.com/openai/math).

The human releaser (**Ningyu Zhou**, School of Physics, Peking University) hosts and maintains the package. The releaser **does not claim** independent mastery of every step. Independent peer review has **not** occurred.

**Status (2026-10-21 submission-ready pack):** computer-assisted **candidate** package prepared for **external referee review**; accuracy tier disclosed. Appropriate phrase: organized for peer review — **not** “confirmed solved.” See [`referee_pack/`](referee_pack/) and [`CHANGELOG_zh.md`](CHANGELOG_zh.md).

## Start here (external readers)

1. **[`referee_pack/README.md`](referee_pack/README.md)** — bilingual entry  
2. **[`referee_pack/REFEREE_BRIEF.md`](referee_pack/REFEREE_BRIEF.md)** — 30 min / 2 h / full-day paths  
3. **Short paper** — [`preprints/Six-unit-squares-cannot-cover-a-square-of-side-greater-than-2-October-21-2026/paper.pdf`](preprints/Six-unit-squares-cannot-cover-a-square-of-side-greater-than-2-October-21-2026/paper.pdf)  
4. **Long proof** — [`artifacts/long_proof/`](artifacts/long_proof/)  
5. **Reproduce** — [`referee_pack/HOW_TO_REPRODUCE.md`](referee_pack/HOW_TO_REPRODUCE.md) (`check_round64`, `check_round63`, `m3_branch_checker`)  
6. **Gaps / tier** — [`referee_pack/KNOWN_GAPS.md`](referee_pack/KNOWN_GAPS.md), [`referee_pack/ACCURACY_TIER.md`](referee_pack/ACCURACY_TIER.md)  
7. **Submission checklist (zh)** — [`SUBMISSION_CHECKLIST_zh.md`](SUBMISSION_CHECKLIST_zh.md)

## Navigating the collection

- [overview](overview.md) · [CONTENTS](CONTENTS.md) · [history](history.md) · [DISCLOSURE](DISCLOSURE.md) · [CITATION.cff](CITATION.cff)
- [`preprints/`](preprints/) — TeX + PDF (Guide for referees; Apps.\ A–D = M1–M4)
- [`lean/`](lean/) — partial skeleton; Boolean flags = status metadata ([`lean/docs/001.md`](lean/docs/001.md))
- [`artifacts/`](artifacts/) — `long_proof/`, `checkers/` (+ companion JSON), `closure/` (M1–M4), `ex_all.tar.gz` + `ex/all/`, `SHA256SUMS.txt`
- [`referee_pack/`](referee_pack/) — **preferred entry for outsiders**

## Honesty snapshot

| Item | State |
| --- | --- |
| Π(n) quantifier (∃ε) | Fixed |
| Normalisation “later = id” overclaim | Weakened; App.\ A candidate protocol |
| Long proof + R64 certs + `ex/all` | Shipped |
| Closure M1–M4 | In `artifacts/closure/` + paper appendices |
| Lean Bool “theorem closed” | Status metadata only |
| Lean ↔ manuscript classification fidelity | **Open** (Major 3) |
| External peer review | **Not done** |

## How the result was produced

Generative AI assistants under the releaser’s direction produced the manuscript and certificate / Lean scaffolding (end-to-end exploration dump). Release *format* follows OpenAI’s public math repository; this is not a classical sole-author paper from personal mastery of every lemma.

## License

See [LICENSE](LICENSE).
