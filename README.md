# Readme

This repository contains a mathematical manuscript and supporting proof artifacts **produced by a generative AI system**, released publicly in the style of the [OpenAI math collection](https://github.com/openai/math).

The human releaser (**Ningyu Zhou**, School of Physics, Peking University) hosts and maintains the package. The releaser **does not claim** independent mastery of every step. Independent peer review has **not** occurred.

**Status (2026-10-21 maturity fix):** computer-assisted **candidate** package under revision after a public-snapshot review of commit `9930699`. Appropriate phrase: materials are being revised and verified — **not** “confirmed solved.” See [`CHANGELOG_zh.md`](CHANGELOG_zh.md).

This collection includes results at different stages of verification. Lean coverage is a **partial skeleton**; Boolean “closed” flags are human-maintained **status metadata**, not geometric theorems. Some unformalized or certificate-backed steps could have issues; please open an issue or PR if you find one.

## Navigating the collection

The current catalogue contains **1 manuscript** organized into **1 family**, in convex / metric geometry.

- Start with the [overview](overview.md) for a short description of the family.
- Use the [manuscript map](CONTENTS.md) to find the paper and supporting materials.
- The [`preprints/`](preprints/) directory contains the PDF, TeX sources, and manuscript-specific citation instructions.
- The [Lean library](lean/README.md) and [formalization catalogue](lean/formalization.yaml) describe the available formalization scope. See [`lean/docs/001.md`](lean/docs/001.md).
- Certificates, long proof, and reproduce notes live under [`artifacts/`](artifacts/) (`long_proof/`, `checkers/`, `REPRODUCE.md`).
- Updates are recorded in [`history.md`](history.md) and [`CHANGELOG_zh.md`](CHANGELOG_zh.md).
- Release ethics: [`DISCLOSURE.md`](DISCLOSURE.md).

## Referee-facing fixes in this tree (summary)

| Item | State |
| --- | --- |
| Π(n) quantifier (exists ε, not ∀ε) | Fixed in TeX/PDF |
| Lemma norm “closed first quadrant” | Fixed |
| One-shot normalisation ⇒ later = id | Weakened to stepwise reclassification |
| Long proof + R64/R42/R55 companion certs | Shipped under `artifacts/` |
| Empty `still_S_after_b23d.jsonl` | Replaced by honest manifest |
| Lean Bool “theorem closed” reading | Relabeled as status metadata |
| Ownership / role manuscript fidelity | Documented FIXMEs + renames; **not** fully repaired |
| Full `ex/all/` + private `closure/*.md` | Deferred (size / packaging) |

## How the result was produced

The manuscript and accompanying case-management / certificate / Lean scaffolding were produced with generative AI assistants under the releaser’s direction (end-to-end exploration dump), analogous in *release format* to OpenAI’s public math repository—not a classical sole-author paper written from personal mastery of every lemma.

## Versions and citations

Public release history is preserved in git and summarized in [`history.md`](history.md). Corrections are recorded as new versions when needed.

To cite the manuscript, use the BibTeX block in its preprint directory README.
