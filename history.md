# History

## 2026-10-21 (Asia/Shanghai) — expert-facing cleanup

- README rewritten for mathematicians (problem → paper → long proof → certificates → Lean).
- Removed non-math packaging (`reasoning_traces/`, process run logs, redundant CONTENTS/overview).
- Concise `DISCLOSURE.md`; referee guide retitled for mathematicians.
- Paper author line and acknowledgements minimised; PDF rebuilt.

## 2026-10-21 — external referee pack

- Added `referee_pack/`, short-paper appendices A–D (M1–M4), `artifacts/closure/`, `ex_all.tar.gz`.
- Open: Lean classification fidelity (Major 3); independent peer review.

## 2026-10-21 — maturity revision (post public-snapshot review)

Addressed five items from the review of commit `9930699`:

- Fixed \(\Pi(n)\) quantifier (∃ε); weakened one-shot normalisation claim.
- Shipped long verification manuscript and companion certificates (R42/R54–55/R64).
- Relabeled Lean whole-theorem Booleans as status metadata; documented ownership/role FIXMEs.
- Honest replacement for empty `still_S_after_b23d.jsonl`.

## 2026-10-21 — initial public release

- First public GitHub tree with short paper, partial Lean `S6Core`, and selected certificate artifacts.
