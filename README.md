# Readme

This repository contains a mathematical manuscript and supporting proof artifacts **produced by a generative AI system**, released publicly in the style of the [OpenAI math collection](https://github.com/openai/math).

The human releaser (**Ningyu Zhou**, School of Physics, Peking University) hosts and maintains the package. The releaser **does not claim** independent mastery of every step. Independent peer review has **not** occurred.

This collection includes results at different stages of verification. Lean coverage is a **partial skeleton**. Some unformalized or certificate-backed steps could have issues; please open an issue or PR if you find one.

## Navigating the collection

The current catalogue contains **1 manuscript** organized into **1 family**, in convex / metric geometry.

- Start with the [overview](overview.md) for a short description of the family.
- Use the [manuscript map](CONTENTS.md) to find the paper and supporting materials.
- The [`preprints/`](preprints/) directory contains the PDF, TeX sources, and manuscript-specific citation instructions.
- The [Lean library](lean/README.md) and [formalization catalogue](lean/formalization.yaml) describe the available formalization scope. See [`lean/docs/001.md`](lean/docs/001.md).
- Selected certificates and reproduce notes live under [`artifacts/`](artifacts/).
- Updates are recorded in [`history.md`](history.md).
- Release ethics: [`DISCLOSURE.md`](DISCLOSURE.md).

## How the result was produced

The manuscript and accompanying case-management / certificate / Lean scaffolding were produced with generative AI assistants under the releaser’s direction (end-to-end exploration dump), analogous in *release format* to OpenAI’s public math repository—not a classical sole-author paper written from personal mastery of every lemma.

Compute and tooling mix includes SMT / interval / Bernstein-style certificates and a Lean 4 skeleton. Full leaf-certificate JSON trees (`ex/all/`) are omitted for size; see `artifacts/REPRODUCE.md` §4.

## Versions and citations

Public release history is preserved in git and summarized in [`history.md`](history.md). Corrections will be recorded as new versions when needed.

To cite the manuscript, use the BibTeX block in its preprint directory README.
