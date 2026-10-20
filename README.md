# Candidate package: \(S(6)=2\)? (AI-produced exploration)

> **Release mode (OpenAI-style public dump).** This repository publishes an **AI-produced, computer-assisted candidate proof package** for the claim \(S(6)=2\) (equivalently \(\Pi(2)=7\)), via GitHub (and optional social posts). It is **not** a traditional journal/arXiv authorship claim by a human who independently mastered every step.

## Read this first (ethics / accuracy)

| | |
|---|---|
| **What this is** | Machine-generated case analysis, certificates, Lean skeleton, and a drafted AMS-style narrative arguing that six unit squares cannot cover a square of side \(>2\). |
| **What this is not** | A human-verified theorem paper ready for silent “we prove …” credit. Independent peer review has **not** happened. |
| **Human role** | Released / maintained by **Ningyu Zhou** (School of Physics, Peking University). The releaser used AI systems end-to-end and **does not claim** to personally understand or vouch for every lemma in the package. |
| **How to cite cautiously** | Treat as *software / exploration artifact*, not as an established theorem, until independent experts audit it. |

If you are looking for a deferential academic statement: **do not** treat this repo alone as closing Dósa–Lángi–Tuza’s conjecture.

## Claim under investigation

Dósa–Lángi–Tuza (arXiv:2601.16535) conjectured \(S(6)=2\). This package contains a **candidate** computer-assisted argument (ownership case split → normalisation → joining-mode elimination; `still_S=0` in the shipped audit slice; Lean obligations 1–4 closed in the shipped skeleton with 0 `sorry` / extra axioms **in that skeleton**). Soft residuals were classified non-blocking in an **internal** AI-assisted audit only.

**Not claimed by the releaser as personal mathematical knowledge:** correctness of the full narrative; a complete Lean re-proof of every metric inequality in the long manuscript; external peer review.

## Artifacts

| Path | Contents |
|---|---|
| [`paper/main.pdf`](paper/main.pdf) | AI-drafted AMS-style writeup (**draft**; claims inside are those of the draft, not a human-certified theorem) |
| [`paper/main.tex`](paper/main.tex) | Source |
| [`ancillary/`](ancillary/) | Lean `S6Core`, reproduce notes, selected certificates |
| [`DISCLOSURE.md`](DISCLOSURE.md) | AI-use & release-policy disclosure |
| [`docs/STATUS_zh.md`](docs/STATUS_zh.md) | Chinese status |
| `arxiv_submission_bundle.tar.gz` | Same materials as a single archive |

Full `ex/all/` leaf-certificate JSON trees are **omitted** for size; see `ancillary/REPRODUCE.md` §4.

## Intended use

1. Experts: audit, attempt to break, or formalise further.
2. Reproducers: follow `ancillary/REPRODUCE.md`.
3. Media / social: link this repo; quote the disclosure, not “undergraduate proved S(6)=2” without the caveats above.

## Contact

Ningyu Zhou — `zhouningyu27@gmail.com` · `nyzhou25@stu.pku.edu.cn`  
Repo: https://github.com/ZhouNingyu327/S6-eq-2
