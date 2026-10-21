# Continuation plan — toward openai/math formalized bar

## Done

- `PrincipalClaim : Prop` + `principal_of_class_exclusions`
- Outer-mid pairwise far + five roles + `hF_ne_corners`
- `AxisClassConstraints` (k=2 mid split)
- **`G5Budget`**: `d+B(d)<2`, opposite/adjacent/grid hyps ⇒ False, wire from `ParallelBudgetData`
- **`G5ExclusionFrag`**: `G5Exclusion_of_bridges` (conditional); bridges open
- **`G3G4Fragments`**: mid-split + M7.1 re-exports; G3/G4 bridges open
- **`BernsteinGridLift`**: **`g2_alg_lt_two` unconditional** (Weierstrass identity proved); E-tier short-cap coeff nonneg
- **`AxisGridContribution`**: clamp lengths, SW outer contrib = 2, four-corners ≤8, abstract grid cover impossible;
  **any** axis square containing a target corner has outer contrib ≤2; four corner-owners ⇒ ≤8
- **`G5GeometryBridge`**: `RigidSquareGridExport → G5GridHyp → False`;
  `G5k*GeomExport ⇒ G5k*Bridge ⇒ G5Exclusion` (proved composition);
  axis outer/corner fragments closed; rotated chord-measure exports still open
- **`NearEndGeometry`**: 7 table-impossible leaves ⇒ `LivingLeafExcluded` (vacuous); 17 living open
- **`G3G4Fragments` budget reduction**: `G3SideGapBudgetBridge` / `G4BudgetBridge` ⇒ exclusions;
  M7.1 sideGap/noSideGap algebraic discharge wired

## Next (priority)

1. **Discharge `G5k0/k1/k2GeomExport`** from `PointwiseCover` — axis corners≤8+CF≤4 algebra closed; need grid-cover ineq from covers + rotated rigid-square contrib ≤2 — closes `G5Exclusion`.
2. **G1/G2**: exclude the 17 living near-end leaves geometrically / via certificates.
3. **G3/G4**: realise `G3SideGapBudgetBridge` / `G4BudgetBridge` from covers (M7.1 metric packing).
4. Only then attempt unconditional `PrincipalClaim`.

## Honesty

Do **not** set `principalClaimProvedUnconditionally := true` until all
`ClassExclusions` fields are constructed without sorry/axioms/open bridges.
