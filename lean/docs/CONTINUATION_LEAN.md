# Continuation plan — toward openai/math formalized bar

## Done

- `PrincipalClaim : Prop` + `principal_of_class_exclusions`
- Outer-mid pairwise far + five roles + `hF_ne_corners`
- `AxisClassConstraints` (k=2 mid split)
- **`G5Budget`**: `d+B(d)<2`, opposite/adjacent/grid hyps ⇒ False; `G5GridHypLe` (CF≤4)
- **`G5ExclusionFrag`**: `G5Exclusion_of_bridges` (conditional)
- **`BernsteinGridLift`**: `g2_alg_lt_two` unconditional
- **`AxisGridContribution`**: clamp lengths; corner-owner outer≤2; four⇒≤8; mid/CF≤4
- **`G5GeometryBridge`**: GeomExport⇒Bridge⇒G5Exclusion composition; axis packages
- **`IntervalCover1D`**: finite closed-interval cover ⇒ sum lengths (Lebesgue)
- **`AxisGridCover`**: `AxisGridLineCover` ⇒ `∑ axisGridContrib ≥ 12μ` (six lines);
  + corners≤8 + CF≤4 split ⇒ False;
  ℚ bottom/top point → real interval membership; rats⊆union; bottomUnion closed
- **`NearEndGeometry` / `G1G2Fragments`**: 7 impossible ⇒ LivingLeafExcluded; G1/G2 bridges named
- **`G3G4Fragments`**: SideGap/Budget bridges ⇒ exclusions
- **`RotatedGridBound`**: diameter + g2_alg re-exports; chord-measure export open

## Next (priority)

1. Lift ℚ `PointwiseCover` / axis edge cover → `AxisGridLineCover` (closedness+density), then split contrib into corners/CF from owners → discharge axis `G5k0GeomExport`.
2. Rotated chord-measure API → corner ≤2 / CF export → full `G5k*GeomExport`.
3. 17 living near-end leaves (G1/G2); realise `G3/G4BudgetBridge` from M7.1 metric packing.
4. Only then unconditional `PrincipalClaim`.

## Honesty

Do **not** set `principalClaimProvedUnconditionally := true` until all
`ClassExclusions` fields are constructed without sorry/axioms/open bridges.
