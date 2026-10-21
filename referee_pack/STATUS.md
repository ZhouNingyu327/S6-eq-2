# Verification status

| Layer | Status |
| --- | --- |
| Problem statement / classical \(S(6)\ge 2\), \(\Pi(2)\le 7\) | Standard |
| Short paper narrative + Hyp⇒Concl outlines | Candidate packaging |
| Long verification manuscript (Markdown source of truth) | Candidate; primary geometric reference |
| Exact Bernstein / interval / rational certificates (E) | Machine-checkable where shipped (incl. R8, R13, R64, …) |
| Hand + solver cross-check (H) | Human-readable + solver assist |
| Dual-solver UNSAT (S) | Not machine-independent proofs |
| Lean 4 `S6Core` skeleton | Builds without sorry/extra axioms *as skeleton*; Boolean “closed” flags are status metadata |
| Ownership / role Lean ↔ manuscript | **Default API aligned** (`flagsOfTarget*`, sixth-tile `iF`, body-chart `pullback`); full faithfulness theorem still open — see KNOWN_GAPS |
| Normalisation | **Primary:** short-paper stepwise reclassification. Strong global M1 = optional; migration note shipped |
| Independent external peer review | **Not done** |

## Suitable phrasing

> Computer-assisted **candidate** argument; verification status and known gaps disclosed.

## Unsuitable phrasing

- “\(S(6)=2\) has been proved / confirmed / peer-reviewed.”
- “Lean proves the geometric theorem.”
- “All SMT steps have independent exact certificates.”
- Treating an empty log or Bool `:= true` as PASS.
