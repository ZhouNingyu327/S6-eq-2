# Six unit squares cannot cover a square of side greater than 2

## Start here: complete English candidate manuscript

**[Read the complete English manuscript (PDF, 277 pages)](manuscript/english-complete-20261022/S6_Complete_English_Candidate_20261022.pdf)**

**22 October 2026, English review edition 1.0.** The 19-page illustrated core
is followed by 258 pages of detailed English derivations: all 72 modules,
eight diagrams, unified notation, one normalization protocol, and one logical
reading order. PDF bookmarks locate the detailed modules.

[Download the PDF](https://github.com/ZhouNingyu327/S6-eq-2/raw/refs/heads/main/manuscript/english-complete-20261022/S6_Complete_English_Candidate_20261022.pdf)
| [Complete source and certificate package](manuscript/S6_Complete_English_20261022.zip)
| [Reading and rebuild guide](manuscript/english-complete-20261022/README.md)
| [Review ledger](manuscript/english-complete-20261022/REVIEW_LEDGER.md)

**Scope:** the full English narrative is now assembled for substantive review.
Checking the computer-assisted parts also requires the supplied exact
certificates and checking code. Editorial completion and selected successful
replays do not establish correctness of every geometric reduction, independent
peer validation, or an end-to-end Lean proof. The review ledger identifies
applicability obligations and the optional historical routes.

The [earlier 19-page core draft 0.1](manuscript/english-core-20261022/S6_English_Core_20261022.pdf)
is retained unchanged as a historical release.

---

Computer-assisted candidate argument that \(S(6)=2\), equivalently \(\Pi(2)=7\), addressing Conjecture 1.1 of Dósa–Lángi–Tuza (2026).

The proposed theorem asserts that six closed unit squares cannot cover any Euclidean square of side strictly greater than \(2\); side \(2\) is attained by the obvious \(2\times 2\) tiling. Combined with the classical bound \(\Pi(2)\le 7\), this yields \(\Pi(2)=7\).

**Status.** Candidate package under revision. Open mathematical gaps (Lean `G*Exclusion` / unconditional claim; independent peer review; remaining dual-solver steps) are listed in [`referee_pack/KNOWN_GAPS.md`](referee_pack/KNOWN_GAPS.md). Do not treat Lean Boolean flags as a geometric theorem.

## Reading order

1. **Complete English candidate manuscript (PDF)** - [core and all 72 detailed modules](manuscript/english-complete-20261022/S6_Complete_English_Candidate_20261022.pdf). Start here; the [companion package](manuscript/S6_Complete_English_20261022.zip) includes the exact certificate inputs.
2. **Earlier short paper (PDF)** — [`preprints/.../paper.pdf`](preprints/Six-unit-squares-cannot-cover-a-square-of-side-greater-than-2-October-21-2026/paper.pdf)
   Definitions, normalisation honesty, top-level classes, Hyp⇒Concl propositions with module IDs, appendices M1–M4.
3. **Earlier detailed source manuscript (historical)** — [`artifacts/long_proof/`](artifacts/long_proof/) (`S6_full_proof.pdf` / `.md`)
4. **Certificates and spot checks** — [`artifacts/checkers/`](artifacts/checkers/), [`artifacts/closure/`](artifacts/closure/), [`artifacts/ex_all.tar.gz`](artifacts/ex_all.tar.gz)
   See [`referee_pack/HOW_TO_REPRODUCE.md`](referee_pack/HOW_TO_REPRODUCE.md).
5. **Lean 4 formalization (partial)** — [`lean/S6Core/`](lean/S6Core/): principal claim as Prop + proved reduction spine; class exclusions open (see [`lean/README.md`](lean/README.md))

For timed reading paths (30 min / 2 h / full day), start at [`referee_pack/`](referee_pack/).

## Repository layout

| Path | Contents |
| --- | --- |
| [`manuscript/english-complete-20261022/`](manuscript/english-complete-20261022/) | Complete English review edition, 72 modules, diagrams, certificates and sources |
| [`preprints/`](preprints/) | TeX sources and short paper PDF |
| [`artifacts/long_proof/`](artifacts/long_proof/) | Full verification narrative |
| [`artifacts/checkers/`](artifacts/checkers/) | Spot-check scripts and companion JSON |
| [`artifacts/closure/`](artifacts/closure/) | Closure notes M1–M4 and branch checker |
| [`artifacts/certs/`](artifacts/certs/) | Certificate registries and inventories |
| [`artifacts/ex/all/`](artifacts/ex/all/), `ex_all.tar.gz` | Historical verification tree and hashes (`SHA256SUMS.txt`) |
| [`artifacts/still_S/`](artifacts/still_S/), [`artifacts/audit/`](artifacts/audit/) | Residual audits |
| [`lean/`](lean/) | Lean 4: Prop main claim + reduction spine (exclusions open) |
| [`referee_pack/`](referee_pack/) | Guide for mathematicians and referees |
| [`history.md`](history.md) | Factual repository timeline |

## Quick reproduce

```bash
git clone https://github.com/ZhouNingyu327/S6-eq-2.git
cd S6-eq-2/artifacts/checkers
python3 check_round64.py && python3 check_round63.py
cd ../closure && python3 m3_branch_checker.py
```

## Citation

See the BibTeX in [`preprints/.../README.md`](preprints/Six-unit-squares-cannot-cover-a-square-of-side-greater-than-2-October-21-2026/README.md) and [`CITATION.cff`](CITATION.cff).

## License and disclosure

[LICENSE](LICENSE). Release ethics (computer-assisted production; releaser role): [DISCLOSURE.md](DISCLOSURE.md).
