# Downloads / omitted archives

**Date:** 2026-10-21 (Asia/Shanghai)

## Shipped in this package

| Path | Contents |
| --- | --- |
| [`../long_proof/S6_full_proof.md`](../long_proof/S6_full_proof.md) | Long verification manuscript (Markdown) |
| [`../long_proof/S6_full_proof.pdf`](../long_proof/S6_full_proof.pdf) | Same manuscript (PDF, ~5.7 MB) |
| [`../long_proof/SHA256SUMS.json`](../long_proof/SHA256SUMS.json) | Hashes for long-proof files |
| [`../checkers/round{42,54,55,64}_*.json`](../checkers/) | Companion certificates for shipped spot-check scripts |
| [`ex_all_SHA256_manifest.json`](ex_all_SHA256_manifest.json) | SHA-256 inventory of the private `ex/all/` snapshot (sources/JSON only) |

## Intentionally omitted (size)

The full historical `ex/all/` checker/certificate tree (~2.8 MB of sources/JSON in the private snapshot; larger with verification zips) is **not** copied into the public dump. Spot-check companions for R29 / R38 / R42 / R54–55 / R64 are included under `artifacts/checkers/`.

To audit omitted files without the blob tree, use `ex_all_SHA256_manifest.json`.
