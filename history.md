# History

## October 21, 2026

**Initial public release (OpenAI-math-style layout).**

- Reorganized the repository to mirror the navigation pattern of `openai/math`: `README.md`, `CONTENTS.md`, `overview.md`, `preprints/`, `lean/`, `artifacts/`, `history.md`, `DISCLOSURE.md`.
- Reframed authorship as AI-produced candidate manuscript with human releaser Ningyu Zhou.
- Deferred traditional arXiv/journal theorem-authorship claims pending independent scrutiny or human scientific responsibility.
- Shipped partial Lean `S6Core` skeleton and selected certificate / `still_S` artifacts; full `ex/all/` trees omitted for size.

## October 21, 2026 (earlier same day)

- First GitHub dump under theorem-style README; later reframed to candidate / disclosure language before adopting the OpenAI-style directory layout.

## 2026-10-21 — OpenAI math-style repository layout

Restructured the public dump to mirror [openai/math](https://github.com/openai/math): top-level README / CONTENTS / overview / history / DISCLOSURE, `preprints/<Title-Date>/` with paper.pdf + build/, `lean/` with formalization.yaml + docs, `artifacts/`, and `reasoning_traces/`. Author line and acknowledgements updated to AI-produced / human-released framing. PDF rebuilt from TeX on 2026-10-21 (Asia/Shanghai).

## October 21, 2026 — maturity fix (post public-snapshot review)

Addressed the five major items in the 2026-10-21 referee report on commit `9930699` without claiming a confirmed theorem:

- Fixed \(\Pi(n)\) quantifier; weakened one-shot normalisation claim; closed-quadrant wording in Lemma norm.
- Shipped long verification manuscript under `artifacts/long_proof/`; companion certs for R42/R54–55/R64; repo-relative `g3_alignment_check.py`.
- Replaced empty `still_S_after_b23d.jsonl` with an honest manifest.
- Relabeled Lean whole-theorem Bools as status metadata; documented Exhaustiveness/`reduction_to_standardForm` non-proofs; OwnershipBridge/Obligation2Roles FIXMEs + renames.
- Full `ex/all/` tree and private `closure/*.md` sources remain deferred for size/packaging.
