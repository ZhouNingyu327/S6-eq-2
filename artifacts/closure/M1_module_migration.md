# Normalisation protocol and module migration

**Primary protocol (this repository):** short-paper Prop. 3.3 — after a dominated corner enlargement, **reclassify** if hosts/gaps may have changed. Idempotence of one operator does **not** imply that later local clamps act as the identity.

**Optional strong scheme (deferred):** App. A / long-proof §2.1 one-shot global bilateral clamp (M1.1–M1.3). **Not** promoted to primary. No module-by-module premise-migration proof is claimed in this package.

---

## Why strong M1 stays deferred

Elevating M1.1–M1.3 to primary would require, for each elimination family below, a written proof that:

1. **Premise preservation.** After the global clamp, every hypothesis used by that module still holds (or the covering has left the module’s class).
2. **Branch migration.** If the clamp fills a true gap, the covering lands in an already-eliminated abutting leaf — with an explicit map of old constraints → new leaf ID.
3. **No hidden dependence on “un-normalised W”.** Modules marked “original \(W\)” must be checked not to need a non-clamped free corner (long-proof M1.3 claims this; it is not independently re-proved here).

Until (1)–(3) exist as referee-readable proofs, public verification follows **stepwise reclassification only**.

---

## Module families under the primary protocol

| Family | Rounds | Expected inputs under stepwise reclassification | If enlargement fills a true gap |
| --- | --- | --- | --- |
| G5 / early centre | R2–R8 | `F∋O` or matching `k∈{0,1,2}` | Leave to abutting leaves already eliminated; no normalisation loop |
| Near residual G2 | R13–R28 | Unique mid on `F`∩BOTTOM; host injection representatives | Reclassify out of residual G2 into abutting/duplicate-host leaves |
| Far reduction | R29–R39 | Post-preprocess free corner called `W` (≠ near-end raw `F`); centre fixed | Reclassify into abutting or far standard-form leaves |
| Final form | M8–M11 / R40–R64 | Far standard-form seams + area/diameter | Do not iterate normalisation inside M8–M11; fix inputs upstream |

---

## App. A strong clamp — status wording

| Statement | Status |
| --- | --- |
| Short-paper Prop. 3.3 stepwise reclassification | **Primary** |
| App. A / M1.1–M1.3 one-shot global clamp | **Optional candidate; deferred** |
| Full premise-migration proof for strong M1 | **Open** (KNOWN_GAPS item 3) |
| Closed quadrant + axial branch + \(W\) identity after preprocess | Stated for free corner after far preprocess; not a substitute for migration proofs |

Public verification and reproduce docs follow the primary protocol.
