# Six unit squares: English core review draft

**Edition:** 0.1, 22 October 2026
**Source snapshot:** 99408eed4ddf3e42bef727e64fae22971e8bc768
**Status:** 19-page English core; the full English technical appendix is pending.

Read `S6_English_Core_20261022.pdf`. The draft supplies eight diagrams, a
global notation register, one normalization protocol, and a dependency order.
Its text and figures are English throughout.

**This is not the completed full English proof.** Propositions citing detailed
R-module derivations still require those derivations. Their English editing
must be completed before this is a self-contained English review edition.
The original detailed source remains in the public repository for provenance;
it is not an English appendix included in this package.

## Reading order

The core proceeds through roles and midpoint classification; G5; G1 and
centre-owned midpoint cases; adjacent/opposite midpoint cases; near-end G2;
the far-end standard form; actual seam points; joining modes and rotations.
Short local proofs expand host selection, the central box, axial caps,
same-tile bottom budgets, and P1 inside the original C. Other module citations
do not replace the corresponding detailed proofs.

## Protocol and notation

Only stepwise cover-dominating replacement is active. After each replacement,
account for resulting hosts, gaps, and empty/nonempty sections explicitly.
The unused one-shot global-clamping scheme supplies no premise.

The core's register and NOTATION.md fix global meanings. Auxiliary symbols in
source R-modules remain scoped to their definitions. The correspondence notes
do not permit transferring hypotheses across modules.

## Checks and scope

The core compiled with Tectonic 0.17.0. All 19 pages were rendered and viewed
in contact sheets; selected diagram and formula pages were also inspected at
larger scale. The build has no unresolved references or overfull boxes.
Selected replays passed R63, R64, the M3 branch checker, and the 151-entry
exact/hand-certificate batch. These do not certify all geometric reductions
or establish translation fidelity. Historical status strings in checker logs
describe those modules, not a new global validation result.

See verification.json and REVIEW_OBLIGATIONS.md for the precise scope.
The main theorem is not claimed to have independent peer validation or an
end-to-end Lean proof.

## Files and rebuild

- main.tex, sections/, refs.bib: editable English core.
- figures/: eight diagrams in vector PDF and SVG, with a manifest.
- tools/draw_figures.py: figure generator.
- evidence/: the four selected replay logs.
- verification.json, MANIFEST.json: build scope and integrity.

From this directory, using a supported TeX installation:

    tectonic --keep-logs --outdir build main.tex

The included build/main.bbl also allows reading the resolved bibliography.
See tools/README.md for rebuilding details.

## Next editorial gate

Initial automatic appendix translations were rejected because they omitted
or distorted some qualifications even while formulas were preserved. They
are excluded from this release. The next stage is module-by-module English
mathematical editing with hypothesis and conclusion checks. No completion
percentage for the full edition is claimed. This is an English core draft; the complete English technical appendix will
be issued separately. Publication of this draft is not a claim of peer endorsement.
