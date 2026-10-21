# Known gaps

Relative to the 2026-10-21 **rereview** of commit `32e0e0f` (and the earlier review of `9930699`).

| Review item | Ask | Status after this push |
| --- | --- | --- |
| R8 certificate delivery | Ship `round8_pair_bernstein_certificate.json`; clean `certificate()` | **Shipped** under `artifacts/ex/all/` (+ `artifacts/checkers/` copy). |
| R13 coefficients | Ship JSON or deterministic generator | **Shipped** `round13_pair_certificate.json`. |
| R16 reproduce docs | Document two-step generate + Fraction verify | **Documented** in `HOW_TO_REPRODUCE.md` / `artifacts/REPRODUCE.md`. |
| R6 tangency typo | `d0>0` → `d0≥0`; use `c(1−α)+sβ≥μ>1` | **Fixed** in `artifacts/long_proof/S6_full_proof.md` (Markdown = source of truth). |
| Normalisation protocol | One primary story; closed quadrant; W identity | **Primary = short-paper stepwise reclassification (Prop. 3.3).** App. A / long-proof M1 = optional candidate; closed quadrant + axial branch + W = post-preprocess free corner. Full module-migration proof still **open**. |
| g3 / REPRODUCE hygiene | R38/R39 paths; drop “ex/all not shipped” | **Addressed.** |
| Lean Major 3 | Faithful k / F∋O / sixth tile | **Still open** (comments strengthened; no semantic fix claimed). |
| Π quantifier | ∃ε | Fixed earlier. |
| Lean Bool metadata | Honesty | Fixed earlier. |

## Still open

1. Manuscript-faithful Lean ownership/role selection (Major 3).
2. Independent external human referee rebuild of critical reductions (esp. early G5 geometry → algebraic premises).
3. Full premise-migration proof if the optional strong normalisation candidate is ever elevated to primary.
4. Reducing remaining (S)-tier dual-solver queries to (E)/(H).
5. Short paper still outlines §§5–7 to long-proof module IDs (page length).

## Closed this round (vs `32e0e0f` rereview)

- R8 necessary Bernstein certificate delivered and runnable on a clean tree.
- R13 certificate delivered.
- R16 generation steps documented.
- R6 tangency strictness corrected in the long-proof Markdown.
- Normalisation primary protocol unified in short paper / App. A / long proof / M1 note.
- Reproduce docs and g3 R38/R39 anchors synced.
