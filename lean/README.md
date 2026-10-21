# Lean formalizations

This directory contains a Lean 4 **partial skeleton** (`S6Core/`) accompanying the single manuscript in this repository.

Boolean flags such as `wholeTheorem_S6_eq_2_closed` / `statusMetadata_candidate_S6_eq_2_flag` are **human-maintained status metadata**. Theorems of the form `flag = true := rfl` are not geometric proofs of \(S(6)=2\).

Ownership / role bridges are **not** yet proved faithful to the manuscript definitions of \(k\), \(F\ni O\), and sixth-tile selection (see FIXMEs in `OwnershipBridge.lean` and `Obligation2Roles.lean`).

See [`docs/001.md`](docs/001.md) for scope, and [`formalization.yaml`](formalization.yaml) for the catalogue entry.

## Build (skeleton)

```bash
cd lean/S6Core
lake build  # fetches mathlib; may take a long time
```

Treat a successful `lake build` of the shipped skeleton as evidence about **that skeleton**, not as a full machine check of every leaf certificate or as confirmation of the geometric theorem.
