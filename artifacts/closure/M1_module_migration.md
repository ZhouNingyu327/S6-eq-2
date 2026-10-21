# Normalisation protocol and module migration

**Primary protocol (this repository):** short-paper Prop. 3.3 — after a dominated corner enlargement, **reclassify** if hosts/gaps may have changed. Idempotence of one operator does **not** imply that later local clamps act as the identity.

**Optional strong scheme:** App. A / long-proof §2.1 one-shot global bilateral clamp (M1.1–M1.3). Not promoted to primary until premise-migration proofs exist.

## Module families

| Family | Rounds | Expected inputs under stepwise reclassification | If enlargement fills a true gap |
| --- | --- | --- | --- |
| G5 / early centre | R2–R8 | `F∋O` or matching `k∈{0,1,2}` | Leave to abutting leaves already eliminated; no normalisation loop |
| Near residual G2 | R13–R28 | Unique mid on `F`∩BOTTOM; host injection representatives | Reclassify out of residual G2 into abutting/duplicate-host leaves |
| Far reduction | R29–R39 | Post-preprocess free corner called `W` (≠ near-end raw `F`); centre fixed | Reclassify into abutting or far standard-form leaves |
| Final form | M8–M11 / R40–R64 | Far standard-form seams + area/diameter | Do not iterate normalisation inside M8–M11; fix inputs upstream |

## App. A strong clamp

Optional. Public verification follows the short-paper primary protocol.
