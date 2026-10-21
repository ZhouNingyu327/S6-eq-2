# Known gaps

Relative to the 2026-10-21 public-snapshot review of commit `9930699`.

| Review major | Ask | Status |
| --- | --- | --- |
| **1** Delivery of long proof + certificates | Ship long proof, companion JSON, clean reproduce | **Mostly addressed:** `artifacts/long_proof/`, R42/R54/R55/R64 JSON beside checkers, `ex_all.tar.gz` + `SHA256SUMS.txt`, `ex/all/` unpacked. Short §§5–7 outline to module IDs (page length). |
| **2** Lean Bool / `True` placeholders | Do not present as geometric theorems | **Addressed (honesty):** status-metadata labels. |
| **3** Classification Lean ≠ manuscript \(k\), \(F\ni O\), sixth tile | Faithful bridge | **Open.** Renames/FIXMEs only. |
| **4** One-shot normalisation ⇒ later = id | Withdraw or prove | **Addressed in short paper** (stepwise reclassification). Stronger global M1 protocol in App.\ A is **candidate text**, not independently certified. |
| **5** Π quantifier ∀ε | Fix to ∃ε | **Fixed.** |

## Still open

1. Manuscript-faithful Lean ownership/role selection (Major 3).
2. Independent external human referee rebuild of critical reductions.
3. Reducing remaining (S)-tier dual-solver queries to (E)/(H).
4. Short paper does not contain full leaf-by-leaf geometry (points to long proof).
5. Stronger global normalisation (App.\ A) beyond the weakened Prop.\ in §3 is not a newly certified proof.

## Fixed / shipped relative to `9930699`

- Π quantifier; normalisation wording; Lean flag honesty.
- Long proof + R64 and companion certs; empty `still_S` honesty.
- Closure M1–M4 under `artifacts/closure/` and paper Apps.\ A–D.
- `ex/all` archived with hashes; `check_round64.py` / `check_round63.py` / `m3_branch_checker.py` pass on clean tree.
