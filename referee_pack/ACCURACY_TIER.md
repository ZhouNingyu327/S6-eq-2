# Accuracy tier (disclosure)

| Layer | Status |
| --- | --- |
| Problem statement / classical \(S(6)\ge 2\), \(\Pi(2)\le 7\) | Standard |
| Short paper narrative + Hyp⇒Concl outlines | Candidate packaging |
| Long verification manuscript | Candidate; primary geometric reference |
| Exact Bernstein / interval / rational certificates (E) | Machine-checkable where shipped |
| Hand + solver cross-check (H) | Human-readable + solver assist |
| Dual-solver UNSAT (S) | **Not** machine-independent proofs |
| Lean 4 `S6Core` skeleton | Builds without sorry/extra axioms *as skeleton*; Boolean “closed” flags are **status metadata** |
| Ownership / role Lean ↔ manuscript fidelity | **Open** (KNOWN_GAPS Major 3) |
| Independent external peer review | **Not done** |

## Allowed public claim

> Computer-assisted **candidate** package prepared for external referee review; accuracy tier disclosed.

## Disallowed claims

- “S(6)=2 has been proved / confirmed / peer-reviewed.”
- “Lean proves the geometric theorem.”
- “All SMT steps have independent exact certificates.”
- Treating an empty log or Bool `:= true` as PASS.
