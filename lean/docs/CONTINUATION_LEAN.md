# Continuation plan — toward openai/math formalized bar

## Done

- **v0.26.10:** BodyChartAxisAligned ↔ SameDirAsC; BodyChartIdentityC ⇒ AxisAlignedIdentityC /
  Bridge / CoverIneq packaging; clamped line covers + ∑clampedSquareTotal≥12μ; ClampedSquareUb⇒Bridge
- **v0.26.9:** filler centre-tile mid-pack (≤2·projWidth; ≤2 if projWidth≤1); roles skeleton;
  G5+identityC iF pack; SameDir⇒BodyChartAxis packaging
- **v0.26.8 (R14 cert):** NoLeftTip + AngleOrder algebraic unsat; ForcesBridgeJunction still false; SE2⇒pack OPEN
- **v0.26.7:** Lean body — μ²>2 auto corner `clampedSquareTotal`; centre outer clamped=0;
  chord/clamped ≤ projWidth; mid-sum ≤ 2·projWidth; same-dir ⇒ body-chart axis-aligned
  (IdentityC packaging). Cert*/LivingLeaf (other track).
- **v0.26.4:** four-corner `clampedSquareTotal ≤2` under projWidth
- **v0.26.6 (docs):** claimed μ²>2 auto pack / same-dir BodyChart (Lean body deferred)

## Next

1. Inhabit `SameDirG5k0Realisation` / `BodyChartAxisG5k0Realisation` /
   `BodyChartIdentityCG5k0Realisation` / `ClampedSquareUbG5k0Realisation` for every G5 k=0;
   **or** ℚ-export CoverIneq from roles pack.
2. Else G3Sep/Cap — `s*s=2` over ℚ uninhabitable; need ℝ export or B-only side-gap.
3. Unconditional `PrincipalClaim` only after ClassExclusions close.

## Honesty

`principalClaimProvedUnconditionally` stays **false**. PrincipalClaim not claimed proved.
Centre/filler Euclidean mid-sum can exceed 2 at 45°; packing uses roles / projWidth / body chart /
clamped UB inhabit.
