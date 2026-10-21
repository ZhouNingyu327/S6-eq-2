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

1. **Unconditional Lean principal claim + end-to-end faithfulness.** Reduction spine + G5 algebraic R2 spine + **geom-export⇒bridge⇒G5Exclusion composition** proved; axis `AxisG5k0Roles`/`AxisG5k0CoverBridge` packing closed under roles; **`G5Exclusion` still conditional** on inhabiting `AxisG5k0CoverBridge` / `RotatedG5k0ChordExport` / `G5k*GeomExport` from `PointwiseCover`. G3/G4 reduced to budget bridges (open realisation). G1/G2: 7/24 near-end leaves table-excluded; 17 living open. Faithfulness of every informal M3.0 covering to `flagsOfTarget*` still open.
2. **Independent external human referee** rebuild of critical reductions (esp. early G5 geometry → algebraic premises). Internal rebuild note only: `artifacts/closure/INTERNAL_G5_rebuild.md` (+ `_zh.md`) — does **not** close this item.
3. **Full premise-migration proof** if the optional strong normalisation candidate (M1.1–M1.3) is ever elevated to primary. Currently **deferred**; primary remains stepwise reclassification (`M1_module_migration.md`).
4. **Remaining (S)-tier** dual-solver queries (~91 unique after Item3 ledger). Inventory: `artifacts/closure/S_tier_inventory.md` (+ JSON). No claim that leftovers are machine-independent.
5. Short paper §§5–7 now cite concrete module tables; further page-length expansions may still help referees.

## Advanced this round (vs `86656b3`)

- **OnlyOwners/OnlyFillers from axis roles**: corner-owner mid=0 + interior-filler outer=0 ⇒ `AxisG5k0Roles` ⇒ packing ⇒ axis G5k0 False; `AxisG5k0CoverBridge` ⇒ `G5k0Bridge`/`G5k0GeomExport`.
- RotatedChordMeasure: `RotatedG5k0ChordExport` ⇒ GeomExport/Bridge; CF_strict_of_le_four; inhabiting export from PointwiseCover **open**.
- Living-leaf: `impossible_cases` + seven-list; 17 living still open.
- G3SideOrOppBridge packaging; G3/G4 realisation from covers still **open**.
- `principalClaimProvedUnconditionally=false`.

## Advanced this round (vs `c89464f`)

- **Role packing proved**: `OnlyOwnersTouchOuter`/`OnlyFillersTouchMid` ⇒ ∑ contrib = outer₄+mid₂; axis G5k0 discharge under role geometry; interior⇒outer=0.
- RotatedChordMeasure: chord distSq≤2; g2_alg<2; PointwiseCover measure export **open**.
- G3EitherBudgetBridge; bothGap living-excluded family.
- `principalClaimProvedUnconditionally=false`.

## Advanced this round (vs `c41b03f`)

- **`Icc_subset_of_closed_of_rats`** proved (clamp non-expansive + dense ℚ); six-line ℚ→`AxisGridLineCover` lift closed; ∑ contrib ≥ 12μ from ℚ covers.
- Axis G5k0 model discharge under outer₄+mid₂ packing hyp; packing from roles still **open**.
- Rotated chord export / 17 living leaves / G3G4 realisation still **open**.
- `principalClaimProvedUnconditionally=false`.

## Advanced this round (vs `58571e1`)

- Lean **IntervalCover1D / AxisGridCover**: 1D Lebesgue cover ⇒ sum lengths; **`AxisGridLineCover` ⇒ ∑ axisGridContrib ≥ 12μ**; + corners≤8+CF≤4 ⇒ False. Lift from ℚ PointwiseCover → real line cover still **open**.
- **RotatedGridBound**: diameter + `g2_alg<2` re-exports; chord-measure G5 export **open**.
- **G1G2Fragments**: 7 impossible leaves excluded; G1/G2 living bridges named; 17 living **open**.
- `principalClaimProvedUnconditionally` remains `false`.

## Prior (vs `8d5dee0`)

- Lean **AxisGridContribution / G5GeometryBridge**: axis corner-owner outer≤2; GeomExport⇒Bridge⇒G5Exclusion; CF≤4 algebra. Grid-cover ineq / rotated contrib were open (now partially closed for axis real-line covers).
- Near-end 7/24; G3/G4 budget bridges.

## Prior (vs `634f591`)

- Lean **G5Budget / G5ExclusionFrag / G3G4Fragments / BernsteinGridLift**: `d+B<2`, R2 grid contradictions, conditional `G5Exclusion_of_bridges`, G3/G4 mid-split+M7.1, E-tier Bernstein coeff nonneg + `g2_alg` bridge lemma. G5 geometric bridges still **open**.

## Prior (vs `9fb5ade`)

- Lean **MainTheorem / CoveringGeometry / NearEndGeometry**: principal claim as Prop;
  conditional closure; pairwise-far outer mids; five-role theorem; near-end Props;
  `RoleSelection.hF_ne_corners`. `formalization.yaml` → `partial_formalization_reduction_spine`.
- Prior (`9fb5ade`): Faithfulness fragments, internal G5 notes, M1 deferred, S-tier inventory,
  short-paper §§5–7 module tables.


## 2026-10-22 batch24 (S)→(E) slice

Converted **60** previously (S) dual-solver rows to checkable Bernstein/IBB/hand-identity certificates
(`artifacts/closure/item3_certs/exact_certs_batch24/`, checker PASS).
**Remaining (S): 125.** This does not close the gap; leftover (S) are still not machine-independent.


## 2026-10-22 batch25 continuation

Checkable cert family total **60** (PASS). **Remaining (S): 91.** Not a theorem claim.


## Batch24–26e certificate track (2026-10-22 Asia/Shanghai)

Machine-checkable exact/hand certs in `artifacts/closure/item3_certs/exact_certs_batch24/`: **144** (checker PASS 144/144). Remaining dual-solver (S) from the post-batch25 set of 91: **7**. Does **not** close the theorem; Lean/lake remains a separate gap.
