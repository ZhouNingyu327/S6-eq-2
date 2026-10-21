# Continuation plan — toward openai/math formalized bar

## Done (this push)

- `PrincipalClaim : Prop`
- `principal_of_class_exclusions`
- Outer-mid pairwise far + five roles
- Near-end Props
- `hF_ne_corners`

## Next Lean milestones (priority order)

1. **G5Exclusion fragment**: from `fHasO` + centre/far geometry, derive a
   concrete algebraic/BudgetHyp contradiction for a representative G5 cover
   (wire `ParallelBudgetGeometry.B_lt_one` + manuscript R2–R8 chart hypotheses
   as Lean structures; prove implication chart → False for μ>1).
2. **G3/G4 mid-ownership**: use pairwise-far outer mids to force k=2 mids onto
   distinct tiles among C∪F; connect to M7.1 / R29N boolean interface already
   in `M7_1Geometry`.
3. **Lift one (E)-tier Bernstein chart** into Lean as a verified nonneg-coeff
   ⇒ inequality lemma already patterned in `Obligation4M8*` / `Obligation4M9*`.
4. **Axis-aligned special case**: prove `PrincipalClaim` restricted to
   axis-aligned six-covers (may be easier; still open mathematically in Lean).
5. Only after several `G*Exclusion` pieces: attempt unconditional
   `PrincipalClaim` or document remaining named axioms.

## Honesty

Do not set `principalClaimProvedUnconditionally := true` until
`ClassExclusions` is fully constructed without sorry/axioms.
