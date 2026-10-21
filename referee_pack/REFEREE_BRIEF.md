# Reading paths

**Claim:** candidate argument that \(S(6)=2\) (six unit squares cannot cover any square of side \(>2\); side \(2\) is attained). Equivalently \(\Pi(2)=7\) given the classical \(\Pi(2)\le 7\).

Do **not** treat Lean Boolean flags as a geometric proof of the theorem.

## 30-minute path

1. Root [README.md](../README.md) + [STATUS.md](STATUS.md) + [KNOWN_GAPS.md](KNOWN_GAPS.md).
2. Short paper: abstract, Guide for referees, §Definitions (Π quantifier), Prop.\ on normalisation honesty, Prop.\ on top-level classes, Theorem statement, Appendices A–D (M1–M4).
3. Run:
   ```bash
   cd artifacts/checkers && python3 check_round64.py && python3 check_round63.py
   cd ../closure && python3 m3_branch_checker.py
   ```

## 2-hour path

Everything in the 30-minute path, plus:

4. Short paper §§5–11: each proposition’s Hyp ⇒ Concl and module IDs (R2–R64).
5. Spot-check long proof TOC / one near-end leaf (e.g.\ R16) and one far-end step (R29N / R31).
6. Read `artifacts/closure/M1_proposition_zh.md`, `M2_R29_module_zh.md`, `M3_branch_table_zh.md`, `M4_unsat_inventory.md` (Chinese source notes; English summaries in paper Apps.\ A–D).
7. Sample one (S)-tier dual-solver item from the M4 inventory for modelling faithfulness.

## Full-day path

8. Read `artifacts/long_proof/S6_full_proof.pdf` (or `.md`) along the elimination order G5→…→double-direct.
9. Verify companion JSONs for R42/R54/R55/R64 next to checkers; unpack `artifacts/ex_all.tar.gz` if needed (`SHA256SUMS.txt`).
10. Optional: `cd lean/S6Core && lake build` — skeleton; ownership flags now manuscript-oriented (`ClassificationExample`); full faithfulness still open (KNOWN_GAPS).
11. Optional: audit notes under `artifacts/still_S/` and `artifacts/audit/`.

## Priority mathematical gates

1. **Classification exhaustiveness (M3)** — Tables M3.0–M3.3 vs narrative.
2. **Normalisation cycle (M1)** — stepwise reclassification in short paper vs stronger global protocol in App.\ A; no module needs non-normalised corners (addendum).
3. **R29N frozen (M2)** — no citation of withdrawn note §5.
4. **μ→1⁺ strictness** — exclusions use μ>1, not a fixed δ-gap.
5. **Certificate tiers (M4)** — (E)/(H)/(S); (S) ≠ machine-independent.
6. **Lean fidelity (partial)** — default ownership/role API repaired; end-to-end faithfulness theorem still open (Major 3).

## Suggested editorial outcomes

- **Accept for further journal review:** only after independent human verification of exhaustiveness + certificate sampling + M1–M4 present in the manuscript under review.
- **Major revision:** gaps in classification, missing certificates, or (S) steps presented as exact.
- **Reject:** genuine geometric counterexample or unfixable classification hole.
