# Six unit squares: complete English candidate manuscript

**English review edition 1.0 - 22 October 2026.**

Read **S6_Complete_English_Candidate_20261022.pdf** first. It has 277 pages:
a 19-page core with eight geometric figures, followed by 258 pages of detailed
English derivations covering all 72 modules. PDF bookmarks locate every module.
The original core draft 0.1 remains a separate historical release.

## Scope of completion

The English presentation is assembled for substantive external review. The
core and appendix use one normalization protocol, a notation register and
one logical family order. No Chinese proof narrative is required along this
reading route. Source-local auxiliary symbols are explicitly scoped; equality
of a letter alone is never permission to transfer a hypothesis.

This is a **candidate argument**, not a claim of independent validation or
confirmed resolution of S(6)=2. The present editing and selected cross-checks
do not replace a full geometric review. Read REVIEW_LEDGER.md for the precise
scope and the supplementary R11 normalization-transfer qualification.

## How to review

The PDF contains the geometric reasoning and case reductions. The large
finite arithmetic records are supplied in certificate_data/ rather than all
being printed as thousands of coefficients. To check those computational
steps, use the companion records/checkers and verify their geometric inputs.
The PDF alone does not constitute a rerun of those certificates.

Start with the core's definitions, host classification and normalization
protocol, then follow the cited modules in the appendix. Review actual point
membership and domain/denominator conditions before accepting a scalar
certificate. REVIEW_OBLIGATIONS.md lists the main gates.

## Editable text and evidence

- main.tex, sections/, refs.bib: core source.
- technical_modules/: all 72 English modules.
- technical_appendix.md: assembled detailed text.
- technical_appendix.html: portable offline version of the detailed text.
- figures/: eight vector PDF/SVG figures.
- NOTATION.md: global register and source-local correspondence.
- certificate_data/: frozen checking code and numeric inputs, preserved verbatim.
- review_records/: internal editing/cross-check records and selected replays.
- verification.json, pdf_layout_audit.json, MANIFEST.json: actual checks and hashes.

## Rebuild

For the core, use standard LaTeX/BibTeX or Tectonic 0.17.0:

    tectonic --keep-logs --outdir build main.tex

For the appendix, install the pinned Node packages in tools/, set CHROME_PATH
if necessary, and run from the manuscript root:

    python tools/assemble_appendix.py
    node tools/render_appendix.cjs
    python tools/combine_pdf.py

The PDF combiner requires pypdf. Diagram regeneration is optional and uses
matplotlib/numpy; prebuilt vector diagrams are supplied. The offline HTML
can be read without installing the rendering tools.

The public source snapshot for the technical derivations is
99408eed4ddf3e42bef727e64fae22971e8bc768. Source and input hashes are recorded.
No new email or claim of peer endorsement accompanies this edition.
