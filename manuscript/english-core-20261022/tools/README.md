# Rebuilding the English core

The core is standard LaTeX, compiled locally with Tectonic 0.17.0.
An editor compilation timed out; the successful build recorded here used
local Tectonic. The prebuilt figures are vector PDF and SVG.

From the manuscript directory:

    tectonic --keep-logs --outdir build main.tex

Alternatively run LaTeX, BibTeX, and LaTeX twice with the listed packages.
Check the resulting log for unresolved references and layout errors.

From this tools directory, to regenerate figures:

    python draw_figures.py

Dependencies: Python, matplotlib, and numpy. Regenerating figures is optional
because prebuilt vector versions are included. The figures are statement or
incidence illustrations, not six-tile covering configurations.

The complete English technical appendix and its renderer are not part of this
core draft. No automatic translation is needed to read or rebuild this core.
