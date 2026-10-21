# Continuation plan — toward openai/math formalized bar

## Done

- `PrincipalClaim : Prop` + `principal_of_class_exclusions`
- Outer-mid pairwise far + five roles + `hF_ne_corners`
- `AxisClassConstraints` (k=2 mid split)
- **`G5Budget`**: `d+B(d)<2`, opposite/adjacent/grid hyps ⇒ False, wire from `ParallelBudgetData`
- **`G5ExclusionFrag`**: `G5Exclusion_of_bridges` (conditional); bridges open
- **`G3G4Fragments`**: mid-split + M7.1 re-exports; G3/G4 bridges open
- **`BernsteinGridLift`**: `g2_alg_lt_two_of_bridge`; E-tier short-cap coeff nonneg

## Next (priority)

1. **Discharge `G5k2Bridge` / `G5k0Bridge` / `G5k1Bridge`** from `PointwiseCover` geometry
   (export corners≤8, CF bounds, `BudgetHyp` from rigid squares) — this closes `G5Exclusion`.
2. **G1/G2 exclusions** via near-end living-leaf geometry + certificates.
3. **G3/G4**: turn M7.1 boolean exclusions into geometric `False` for covers.
4. Prove `G2AlgBridge` (identify `g2_alg` with Euclidean chord sum).
5. Only then attempt unconditional `PrincipalClaim`.

## Honesty

Do **not** set `principalClaimProvedUnconditionally := true` until all
`ClassExclusions` fields are constructed without sorry/axioms/open bridges.
