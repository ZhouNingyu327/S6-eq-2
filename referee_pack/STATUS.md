# Verification status

| Layer | Status |
| --- | --- |
| Problem statement / classical \(S(6)\ge 2\), \(\Pi(2)\le 7\) | Standard |
| Short paper narrative + Hyp⇒Concl outlines | Candidate packaging; §§5–7 cite long-proof module tables |
| Long verification manuscript (Markdown source of truth) | Candidate; primary geometric reference |
| Exact Bernstein / interval / rational certificates (E) | Machine-checkable where shipped (R8, R13, R64, … + **batch24–26f family 151/151 PASS** at `80e8ee0`) |
| Hand + solver cross-check (H) | Human-readable + checkable identity/cascade certificates in the same family |
| Dual-solver UNSAT (S) | **Inventory cleared to (E)/(H)** for the post-batch25 set of 91 (remaining **0**). See `artifacts/closure/S_tier_inventory.md`. Cleared (S) ≠ theorem proved |
| Lean 4 `S6Core` skeleton | Builds without sorry/extra axioms *as skeleton*; Boolean “closed” flags are status metadata |
| Ownership / role Lean ↔ manuscript API | **Partial:** `flagsOfTarget*`, `F∋O`, sixth-tile `iF`, pullback, `Faithfulness.lean` fragments; end-to-end faithfulness **open** |
| Normalisation | **Primary:** stepwise reclassification. Strong global M1 = optional / **deferred** |
| Internal G5 critical rebuild note | Shipped (`INTERNAL_G5_rebuild.md`); not external review |
| Independent external peer review | **Not done** |
| Cert → Lean Bernstein handoff | `artifacts/closure/CERT_TO_LEAN_HANDOFF.md` (suggested next lifts; not closure) |

## Suitable phrasing

> Computer-assisted **candidate** argument; verification status and known gaps disclosed. The former dual-solver (S) inventory has recomputable (E)/(H) certificates (checker PASS), but the principal geometric claim and Lean end-to-end faithfulness remain **open**.

## Unsuitable phrasing

- “\(S(6)=2\) has been proved / confirmed / peer-reviewed.”
- “Lean proves the geometric theorem.”
- “All SMT steps have independent exact certificates.” *(the tracked (S) set is cleared; that is not a global SMT claim)*
- Treating an empty log or Bool `:= true` as PASS.
- “Already proved; only lacking external review.”
- “Clearing the (S) inventory proves the theorem.”
