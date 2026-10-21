# Verification status

| Layer | Status |
| --- | --- |
| Problem statement / classical \(S(6)\ge 2\), \(\Pi(2)\le 7\) | Standard |
| Short paper narrative + Hyp⇒Concl outlines | Candidate packaging; §§5–7 cite long-proof module tables |
| Long verification manuscript (Markdown source of truth) | Candidate; primary geometric reference |
| Exact Bernstein / interval / rational certificates (E) | Machine-checkable where shipped (incl. **R8**, R13, R64, …) |
| Hand + solver cross-check (H) | Human-readable + solver assist |
| Dual-solver UNSAT (S) | ~151 unique leftovers inventoried; not machine-independent proofs |
| Lean 4 `S6Core` skeleton | Builds without sorry/extra axioms *as skeleton*; Boolean “closed” flags are status metadata |
| Ownership / role Lean ↔ manuscript API | **Partial:** `flagsOfTarget*`, `F∋O`, sixth-tile `iF`, pullback, `Faithfulness.lean` fragments; end-to-end faithfulness **open** |
| Normalisation | **Primary:** stepwise reclassification. Strong global M1 = optional / **deferred** |
| Internal G5 critical rebuild note | Shipped (`INTERNAL_G5_rebuild.md`); not external review |
| Independent external peer review | **Not done** |

## Suitable phrasing

> Computer-assisted **candidate** argument; verification status and known gaps disclosed.

## Unsuitable phrasing

- “\(S(6)=2\) has been proved / confirmed / peer-reviewed.”
- “Lean proves the geometric theorem.”
- “All SMT steps have independent exact certificates.”
- Treating an empty log or Bool `:= true` as PASS.
- “Already proved; only lacking external review.”
