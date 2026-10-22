# Exact arithmetic and certificate data

This directory contains the numeric certificate records and checking code
from the pinned public source, plus two previously reconstructed R16 tree
files whose hashes match the historical manuscript. The frozen numeric and
script payload is preserved verbatim; its archived comments and identifiers
are provenance, not part of the English proof reading route. No historical
Chinese proof narrative is needed to read the new English manuscript.

The file manifest identifies exact inputs. This package does not claim that
every archived checker has been rerun for this edition, or that a successful
arithmetic check proves geometric applicability. Some archival entries check
the structure of a hand-proof record rather than prove its prose.

## Selected checks

Use Python with sympy and z3-solver for the main checkers. From this directory:

    cd artifacts/checkers
    python check_round64.py
    python check_round63.py
    python check_round42.py

For the branch checker and the 151-entry exact/hand batch:

    cd ../closure
    python m3_branch_checker.py
    python scripts/check_exact_certs_batch24.py

For the R16 trees, the independent verifier uses exact Fraction arithmetic:

    cd ../ex/all
    python verify_round16_fraction_certificate.py

It checks the existing 249-leaf and 924-leaf trees; it does not build a new
subdivision tree. The positive and negative tree hashes are listed in the
manifest. Generate no new tree merely to replace a failed verification.

The same covering, actual endpoints, nonempty intersections, rotation sign,
q-domain and denominator signs must be verified in the English geometric
argument before an arithmetic exclusion can be applied. See the manuscript's
review ledger and the edition's verification record for checks actually run.
