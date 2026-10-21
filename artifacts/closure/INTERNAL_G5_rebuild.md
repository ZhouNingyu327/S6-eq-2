# INTERNAL rebuild: early G5 geometry → algebra bridges

**Label:** internal critical rebuild (NOT independent external peer review).  
**Date:** 2026-10-21 (Asia/Shanghai).  
**Sources:** `artifacts/long_proof/S6_full_proof.md` §§3–4 and modules R2–R8; short paper Prop. M4.1; shipped R8 Bernstein certificate.

This note re-derives the early G5 chain as a checkable outline for maintainers.
It does **not** close KNOWN_GAPS item 2 (true external referee rebuild).

---

## 1. Standing assumptions (imported, not re-proved here)

| ID | Assumption | Where used | Status in public package |
| --- | --- | --- | --- |
| A1 | Six closed unit squares cover \(T=[0,2\mu]^2\), \(\mu>1\) | all | problem hypothesis |
| A2 | Diameter \(\sqrt2\) ⇒ four distinct corner owners; none contain \(O\) | R2–R3 | classical; sketched in long proof |
| A3 | Parallel-chord bound \(B(d)<1\) and \(d+B(d)<2\) for \(1<d\le\sqrt2\) | R2–R3, R8 | long-proof lemmas + checkers |
| A4 | Long-chord three-ray strict budget \(<2\) for a corner tile | R2, R8 | long-proof + independent verify scripts |
| A5 | Grid \(\mathcal G\) (four sides + two midlines) has length \(12\mu\); corner tiles contribute \(\le 2\) each | R2 | long-proof §R2 |
| A6 | Ownership: \(k=\#\{\text{outer mid}\in C\cup F\}\); G5 means \(O\in C\cap F\) | classification | aligned with Lean `flagsOfTarget*` / `fHasO` |
| A7 | Dominated corner enlargement / stepwise reclassification primary protocol | normalisation | short-paper Prop. 3.3; strong M1 optional |

---

## 2. Chain map (Hyp ⇒ Concl)

### R2 — G5, \(k=2\)

- **Hyp.** G5 and exactly two outer mids in \(C\cup F\) (adjacent or opposite).
- **Bridge.** Adjacent: apply three-ray budgets on each centre tile; midlines covered by \(\max\) estimates ⇒ \(|(C\cup F)\cap\mathcal G|<4\). Opposite: horizontal midline \(2\mu\) plus two \(B(\mu)\) budgets ⇒ same.
- **Concl.** Total grid coverage \(<8+4=12<12\mu\), contradiction.
- **Checkable claims.** Inequality \(\mu+B(\mu)<2\) on \(1<\mu\le\sqrt2\); triangle-area obstruction for a tile meeting \(m_i\) and a far side.
- **Gaps found.** Scope note in long proof: argument uses one mid per centre tile — must not be copied to \(k=0,1\).

### R3 — G5, \(k=0\)

- **Hyp.** G5 and all four outer mids owned by corner tiles (matching after reflection).
- **Bridge.** Residual-gap case split (0 / 1 / 2 / ≥3) with parallel budgets, weighted three-ray bound, and leg-ratio estimates after one dominated normalisation of corners.
- **Concl.** No covering; also rules out “four mids all on corners” even if mids also meet centres.
- **Checkable claims.** \(B(d)\) formula branches; \(\beta\le\min(1,s/c)\) normalisation does not create a second mid on a unit square.
- **Gaps found.** Relies on R2 lemmas as black boxes; independent human rebuild should re-verify residual-gap endpoint geometry, not only the algebra lines.

### R4–R7 — G5, \(k=1\) reduction

- **Hyp.** G5 with unique outer mid in \(C\cup F\).
- **Bridge.** R4: \(F\) cannot meet the side of that mid (near/far representatives). R5–R6: near residual. R7: far contacts reduce to triple abutment with second centre tile interior.
- **Concl.** Only the interior second-centre / triple-abutment leaf remains for R8.
- **Checkable claims.** Host-injection representatives; “cannot meet both LEFT and RIGHT at distance \(2\mu>\sqrt2\)”.
- **Gaps found.** Several representative choices are narrative-heavy; algebraic premises fed into R8 (unit-circle legs, projection caps, \(S_1+S_2\ge1\)) need explicit export from geometry — this is the main early critical bridge risk.

### R8 — final G5 leaf

- **Hyp.** Reduced triple-abutment / interior second centre with two-corner inequality premises.
- **Bridge.** Map 2D domain into the unit square; 45 rational rectangles; Bernstein nonnegativity of
  \[
  L_1+L_2+\min(t_1,t_2)+\tfrac45\max(t_1,t_2)-\tfrac{14}{5}
  \]
  then compare to weighted three-ray bounds on the interior tile (both orderings of \((t_1,t_2)\)).
- **Concl.** Contradiction ⇒ G5 empty; hence unique centre tile and \(O\) interior to it (with positive distance from the other five tiles).
- **Checkable claims.** Shipped `artifacts/ex/all/round8_pair_bernstein_certificate.json` + `verify_round8.py` / checkers copy; prefix-tree coverage of rectangles.
- **Gaps found.** Premises \(S_1+S_2\ge1\) and projection caps are geometric; certificate proves the polynomial step only.

---

## 3. Downstream consequence used later

Corollary M5.3 (universal centre forbids outer mids) depends on M4.1 (this chain) plus M4.2–M4.3 and M5.1–M5.2. Any flaw in R4–R7 premise export contaminates near-end / far-end residual G2.

---

## 4. What this rebuild does / does not claim

| Claims | Does not claim |
| --- | --- |
| Internal outline of G5 Hyp⇒Concl with module IDs | External independent referee sign-off |
| Points to shipped R8 machine certificate | R4–R7 fully re-proved by a third party |
| Lists assumptions and known fragile bridges | Theorem \(S(6)=2\) confirmed |

KNOWN_GAPS item 2 remains **open**.
