# Lean formalizations

Lean 4 partial skeleton (`S6Core/`) accompanying the manuscript in this repository.

Boolean flags such as `wholeTheorem_S6_eq_2_closed` are **human-maintained status metadata**. Theorems of the form `flag = true := rfl` are not geometric proofs of \(S(6)=2\).

## Ownership / classification (2026-10-21)

Default classifiers are manuscript-oriented:

- `flagsOfTarget` / `flagsOfTargetRotated` — four target outer mids; `fHasO` means \(F\ni O\);
- `RoleSelection.ofCover` — `iF` is the sixth tile; free blocks are pulled into the centre body chart by one `pullback`;
- regression: `ClassificationExample.lean` (rereview counterexample → `k=1`, `fHasO=false`).

Legacy MidCandidates wiring remains under `legacyFlagsOf*` for comparison only. An end-to-end proof that every covering reduces with these flags is still open (see `referee_pack/KNOWN_GAPS.md`).

## Build

```bash
cd lean/S6Core
lake build  # fetches mathlib; may take a long time
```

A successful build checks this skeleton, not every leaf certificate and not the geometric theorem.
