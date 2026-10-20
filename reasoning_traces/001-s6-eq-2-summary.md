# Reasoning summary (abridged) — Family 001

High-level route used by the AI exploration (not a transcript dump):

1. Reduce covering side \(a>2\) by six unit squares to a finite ownership analysis of the centre and outer midpoints.
2. Normalise surviving configurations to a standard form.
3. Eliminate joining modes via chord / budget / incidence inequalities.
4. Discharge algebraic exclusions with exact identities, Bernstein/interval certificates, and SMT UNSAT queries.
5. Formalise selected geometric interfaces in Lean 4 (`S6Core`); leave many leaf certificates outside the Lean skeleton.

This summary is informational. Trust checks should use `artifacts/` and `lean/`, not this note alone.
