# Continuation plan — toward openai/math formalized bar

## Done

- Axis packing / `AxisG5k0Roles` / `AxisG5k0FromCover` base path
- **`isG5Class ↔ fHasO`**; **`pullback identityPose = id`**; **identity-C + G5 ⇒ world F∋O**
- **`AxisAlignedIdentityCRealisation` ⇒ `AxisAlignedG5k0Realisation` ⇒ bridges/GeomExport/ChordExport**
- Axis-aligned + C=`identityPose` + G5 (+k=0) ⇒ `False` (unconditional on that hyp)
- Rotated: `RotatedG5k0ChordExport_of_axisRealisation` / `_of_identityCRealisation`
- **Body-chart faithfulness:** `pullback_self` (C-chart ⇒ C=`identityPose`); axis pullback preserves alignment;
  pure translation normalises any axis tile to `identityPose`; `bodyChartSquares` / `BodyChartAxisAligned`;
  world-axis ⇒ body identity-C; manuscript F = body-chart F
- **G3/G4:** `classify_eq_G3_iff` / `classify_eq_G4_iff`; cover flag extracts `isG3Class_flags` / `isG4Class_flags`
- Living: S-tier exact complete (151/151) inventory flag; `LivingLeafCertBridge` packaging
- G3/G4: grid implications; `G3CoverBudgetRealisation` ⇒ exclusion

## Next

1. Inhabit `AxisAlignedIdentityCRealisation` **or** `BodyChartAxisG5k0Realisation` for every G5 k=0 cover
   (residual after chart faithfulness), **or** `RotatedChordBoundPackage` cover-ineq from general covers.
2. Geometry for 17 living near-end leaves (`AllLivingClosersDischarged`).
3. Inhabit G3/G4 cover budgets from covers (flags now characterised).
4. Unconditional `PrincipalClaim` only after all ClassExclusions close.

## Honesty

`principalClaimProvedUnconditionally` stays **false** until ClassExclusions are fully constructed.
