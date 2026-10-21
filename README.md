# Six unit squares cannot cover a square of side greater than 2

Computer-assisted candidate argument that \(S(6)=2\), equivalently \(\Pi(2)=7\), addressing Conjecture 1.1 of Dósa–Lángi–Tuza (2026).

Six closed unit squares cannot cover any Euclidean square of side strictly greater than \(2\); side \(2\) is attained by the obvious \(2\times 2\) tiling. Combined with the classical bound \(\Pi(2)\le 7\), this yields \(\Pi(2)=7\).

**Status.** Candidate package under revision. Open mathematical gaps (Lean `G*Exclusion` / unconditional claim; independent peer review; remaining dual-solver steps) are listed in [`referee_pack/KNOWN_GAPS.md`](referee_pack/KNOWN_GAPS.md). Do not treat Lean Boolean flags as a geometric theorem.

## Reading order

1. **Short paper (PDF)** — [`preprints/.../paper.pdf`](preprints/Six-unit-squares-cannot-cover-a-square-of-side-greater-than-2-October-21-2026/paper.pdf)  
   Definitions, normalisation honesty, top-level classes, Hyp⇒Concl propositions with module IDs, appendices M1–M4.
2. **Long verification manuscript** — [`artifacts/long_proof/`](artifacts/long_proof/) (`S6_full_proof.pdf` / `.md`)
3. **Certificates and spot checks** — [`artifacts/checkers/`](artifacts/checkers/), [`artifacts/closure/`](artifacts/closure/), [`artifacts/ex_all.tar.gz`](artifacts/ex_all.tar.gz)  
   See [`referee_pack/HOW_TO_REPRODUCE.md`](referee_pack/HOW_TO_REPRODUCE.md).
4. **Lean 4 formalization (partial)** — [`lean/S6Core/`](lean/S6Core/): principal claim as Prop + proved reduction spine; class exclusions open (see [`lean/README.md`](lean/README.md))

For timed reading paths (30 min / 2 h / full day), start at [`referee_pack/`](referee_pack/).

## Repository layout

| Path | Contents |
| --- | --- |
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
