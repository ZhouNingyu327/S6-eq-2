# Known gaps

Relative to the 2026-10-21 **rereview** of commit `32e0e0f` / `5bfd66a`, plus this round’s Lean Major‑3 repair.

| Review item | Ask | Status |
| --- | --- | --- |
| R8 / R13 / R16 / R6 / reproduce hygiene | Ship certs; fix tangency; docs | **Done** (prior push `5bfd66a`). |
| Normalisation protocol | One primary story + migration note | **Primary = stepwise reclassification.** Strong M1 optional. Module-family migration note: `artifacts/closure/M1_module_migration.md`. Full premise-migration **proofs** still open. |
| Lean Major 3 | Faithful `k` / `F∋O` / sixth tile / body-chart motion | **API repaired this round** (`flagsOfTarget*`, `fContainsO`, sixth-tile `iF`, `pullback`). Rereview counterexample now classifies as `k=1`, `fHasO=false` under the primary API (`ClassificationExample.lean`). Legacy MidCandidates wiring kept only under `legacyFlagsOf*`. **Not claimed:** a completed proof that every geometric covering’s roles match the manuscript end-to-end. |
| Π quantifier / Bool metadata | Honesty | Fixed earlier. |

## Still open

1. End-to-end Lean proof that arbitrary coverings reduce with the new faithful flags (existence of roles + faithfulness theorem) — API fix ≠ full geometric theorem.
2. Independent external human referee rebuild of critical reductions (esp. early G5 geometry → algebraic premises).
3. Premise-migration **proofs** if the optional strong normalisation candidate is elevated to primary.
4. Reducing remaining (S)-tier dual-solver queries to (E)/(H).
5. Short paper still outlines §§5–7 to long-proof module IDs.

## Closed / improved this round (vs `5bfd66a`)

- Manuscript-faithful ownership flag definitions are the default Lean API.
- Rereview local counterexample is a machine-checked regression test under the new API (and a witness that legacy wiring still mismatches).
- Sixth-tile role selection + consistent body-chart `pullback` for free blocks.
- Normalisation module-migration note shipped; long-proof “later = id” wording scoped to the optional strong scheme.
