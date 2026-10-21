# Lean formalizations

Lean 4 partial skeleton (`S6Core/`) accompanying the manuscript in this repository.

Boolean flags such as `wholeTheorem_S6_eq_2_closed` are **human-maintained status metadata**. Theorems of the form `flag = true := rfl` are not geometric proofs of \(S(6)=2\).

## Ownership / classification (2026-10-21)

Default classifiers are manuscript-oriented:

- `flagsOfTarget` / `flagsOfTargetRotated` — four target outer mids; `fHasO` means \(F\ni O\);
- `RoleSelection.ofCover` — `iF` is the sixth tile; free blocks are pulled into the centre body chart by one `pullback`;
- regressions: `ClassificationExample.lean` (rereview counterexample → `k=1`, `fHasO=false`) and `Faithfulness.lean` (G5 / G1 / centre-G2 sketches + API contracts).

Legacy MidCandidates wiring remains under `legacyFlagsOf*` for comparison only.

### Proved vs open

| Item | Status |
| --- | --- |
| Flag API contracts (`fHasO` ⇔ `F` contains centre; flags ignore transport `mids`) | Proved in `Faithfulness.lean` |
| Role packaging inequalities; sixth-tile existence lemma; pullback = `g⁻¹∘f` | Proved |
| Classification regressions (rereview + G5/G1/centre-G2) | Proved (`native_decide`) |
| End-to-end: every informal M3.0 covering → these flags | **Open** (`endToEndFaithfulnessProvedInLean = false`) |
| Geometric theorem \(S(6)=2\) in Lean | **Open** (not claimed) |

See `referee_pack/KNOWN_GAPS.md` and `lean/docs/001.md`.

## Build

```bash
cd lean/S6Core
lake build  # fetches mathlib; may take a long time
```

A successful build checks this skeleton, not every leaf certificate and not the geometric theorem.
