# Lean formalizations

This directory contains a Lean 4 skeleton (`S6Core/`) accompanying the single manuscript in this repository.

Not every metric inequality in the long verification narrative is re-proved in Lean. See [`docs/001.md`](docs/001.md) for scope, and [`formalization.yaml`](formalization.yaml) for the catalogue entry.

## Build (skeleton)

```bash
cd lean/S6Core
lake exe  # fetches mathlib; may take a long time
```

Treat a successful `lake build` of the shipped skeleton as evidence about **that skeleton**, not as a full machine check of every leaf certificate omitted from this release.
