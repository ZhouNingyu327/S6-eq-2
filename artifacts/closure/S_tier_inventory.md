# Remaining (S)-tier dual-solver inventory

**As of:** 2026-10-21 (Asia/Shanghai).
**Sources:** `artifacts/closure/item3_certs/` (queue + upgrade_results_*), `certificate_counts.json`, `M4_unsat_inventory.md`.

Status labels: **(E)** exact rational/Bernstein/CAD certificate; **(H)** hand + solver cross-check; **(S)** dual-solver UNSAT only (not machine-independent).

## Headline counts

| Quantity | Value |
| --- | --- |
| Item3 queue unique keys (deduped upgrades) | 264 |
| Exact upgrades from Item3 (unique) | 113 |
| Still (S) / cvc5-only (unique) | **151** |
| First-route exact harness (M4) | 121 |
| Hand / Bernstein supplement (M4) | 10 |
| Tracked unique total (M4) | 391 |
| Approx. (E)/(H) share of tracked unique | ~61% |
| Approx. (S) share | ~39% |

Historical script-level sum **403** differs from unique tracked **391** because of duplicate queue keys / cross-script double counts — see M4.

## Remaining (S) by check file

| Check file | Remaining (S) | Already exact in Item3 |
| --- | ---: | ---: |
| `check_round34_left_negative` | 15 | 6 |
| `check_round38_empty_right_negative` | 15 | 7 |
| `check_round26_g2_top` | 13 | 7 |
| `check_round28_g2_near_complete` | 12 | 3 |
| `check_round32_right_positive` | 12 | 1 |
| `check_round36_nonempty_closed` | 12 | 4 |
| `check_round27_g2_two_branches` | 11 | 19 |
| `check_round25_g3_complete` | 10 | 13 |
| `check_round35_positive_H` | 9 | 4 |
| `check_round24_g3_fside` | 8 | 8 |
| `check_round30_corrected_geometry` | 8 | 4 |
| `check_round33_right_nonempty` | 8 | 5 |
| `check_round39_single_contact` | 8 | 16 |
| `check_round29_no_top_structure` | 5 | 1 |
| `check_round29_far_top_complete` | 2 | 9 |
| `check_round41_geometry` | 2 | 1 |
| `check_round24_g3_cside` | 1 | 5 |

Machine-readable: `S_tier_remaining.json`.

## Conversions this push

No new (S)→(E)/(H) leaf certificates were generated in this push beyond packaging the existing Item3 upgrade ledger into the public tree (`item3_certs/`).
Leftover (S) queries remain dual-solver only.

## How to attempt further upgrades

```bash
# From a full certs checkout (scripts live under historical item3_certs):
# python upgrade_batch*.py   # Bernstein / rational IBB / Or-split
# Then record results in upgrade_results_*.jsonl and refresh this inventory.
```

Do **not** describe leftover (S) rows as machine-independent proofs.
