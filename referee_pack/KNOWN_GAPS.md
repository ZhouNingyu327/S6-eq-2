# Known gaps

Relative to the 2026-10-21 **rereview** of commit `32e0e0f`, the API repair at `8672f31`, and this gaps push.

| Review item | Ask | Status after this push |
| --- | --- | --- |
| R8 certificate delivery | Ship `round8_pair_bernstein_certificate.json`; clean `certificate()` | **Shipped** under `artifacts/ex/all/` (+ `artifacts/checkers/` copy). |
| R13 coefficients | Ship JSON or deterministic generator | **Shipped** `round13_pair_certificate.json`. |
| R16 reproduce docs | Document two-step generate + Fraction verify | **Documented** in `HOW_TO_REPRODUCE.md` / `artifacts/REPRODUCE.md`. |
| R6 tangency typo | `d0>0` → `d0≥0`; use `c(1−α)+sβ≥μ>1` | **Fixed** in `artifacts/long_proof/S6_full_proof.md`. |
| Normalisation protocol | One primary story; closed quadrant; W identity | **Primary = short-paper stepwise reclassification (Prop. 3.3).** Strong M1 = optional / **deferred**; migration proof still open. |
| g3 / REPRODUCE hygiene | R38/R39 paths; drop “ex/all not shipped” | **Addressed.** |
| Lean Major 3 API | Faithful k / F∋O / sixth tile / pullback | **API + partial faithfulness module shipped**; end-to-end geometric faithfulness still **open**. |
| Π quantifier | ∃ε | Fixed earlier. |
| Lean Bool metadata | Honesty | Fixed earlier. |

## Still open

1. **Unconditional Lean principal claim + end-to-end faithfulness.** Reduction spine + G5 algebraic R2 spine + **geom-export⇒bridge⇒G5Exclusion composition** proved; **`G5Exclusion` still conditional** on open `G5k*GeomExport` (rotated corner≤2 / CF / cover ineq from `PointwiseCover`). G3/G4 reduced to `G3SideGapBudgetBridge`/`G4BudgetBridge` (open). G1/G2: 7/24 near-end leaves table-excluded; 17 living open. Faithfulness of every informal M3.0 covering to `flagsOfTarget*` still open.
2. **Independent external human referee** rebuild of critical reductions (esp. early G5 geometry → algebraic premises). Internal rebuild note only: `artifacts/closure/INTERNAL_G5_rebuild.md` (+ `_zh.md`) — does **not** close this item.
3. **Full premise-migration proof** if the optional strong normalisation candidate (M1.1–M1.3) is ever elevated to primary. Currently **deferred**; primary remains stepwise reclassification (`M1_module_migration.md`).
4. **Remaining (S)-tier** dual-solver queries (~151 unique after Item3 ledger). Inventory: `artifacts/closure/S_tier_inventory.md` (+ JSON). No claim that leftovers are machine-independent.
5. Short paper §§5–7 now cite concrete module tables; further page-length expansions may still help referees.

## Advanced this round (vs `8d5dee0`)

- Lean **AxisGridContribution / G5GeometryBridge**: axis SW outer=2, corners≤8 package, `RigidSquareGridExport→G5GridHyp→False`; `G5k*GeomExport⇒G5k*Bridge⇒G5Exclusion` composition proved. Rotated chord-measure exports still **open**.
- Near-end: 7 impossible leaves ⇒ `LivingLeafExcluded`; 17 living open.
- G3/G4: `G3SideGapBudgetBridge`/`G4BudgetBridge` ⇒ exclusions; M7.1 budget algebra wired. Metric packing export still **open**.
- `principalClaimProvedUnconditionally` remains `false`.

## Prior (vs `634f591`)

- Lean **G5Budget / G5ExclusionFrag / G3G4Fragments / BernsteinGridLift**: `d+B<2`, R2 grid contradictions, conditional `G5Exclusion_of_bridges`, G3/G4 mid-split+M7.1, E-tier Bernstein coeff nonneg + `g2_alg` bridge lemma. G5 geometric bridges still **open**.

## Prior (vs `9fb5ade`)

- Lean **MainTheorem / CoveringGeometry / NearEndGeometry**: principal claim as Prop;
  conditional closure; pairwise-far outer mids; five-role theorem; near-end Props;
  `RoleSelection.hF_ne_corners`. `formalization.yaml` → `partial_formalization_reduction_spine`.
- Prior (`9fb5ade`): Faithfulness fragments, internal G5 notes, M1 deferred, S-tier inventory,
  short-paper §§5–7 module tables.
