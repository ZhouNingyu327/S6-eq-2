# Remaining (S)-tier dual-solver inventory

**As of:** 2026-10-22 (Asia/Shanghai).
**Sources:** `artifacts/closure/item3_certs/` (queue + upgrade_results_* + batch24 family), `certificate_counts.json`, `M4_unsat_inventory.md`.

Status labels: **(E)** exact rational/Bernstein/CAD certificate; **(H)** hand + solver cross-check; **(S)** dual-solver UNSAT only (not machine-independent).

## Headline counts

| Quantity | Value |
| --- | --- |
| Item3 queue unique keys (deduped upgrades) | 264 |
| Exact upgrades from Item3 batches 1–6 (unique) | 113 |
| **New exact from batch24 family (checkable certs)** | **26** |
| Exact Item3+batch24 unique | 139 |
| Still (S) / cvc5-only (unique) | **125** |
| First-route exact harness (M4) | 121 |
| Hand / Bernstein supplement (M4) | 10 |
| Tracked unique total (M4) | 391 |
| Approx. (E)/(H) share of tracked unique | ~69% |
| Approx. (S) share | ~32% |

## Conversions this push (batch24 family)

Emitted **26** machine-checkable certificates under
`item3_certs/exact_certs_batch24/` with checker
`artifacts/closure/scripts/check_exact_certs_batch24.py` (**PASS 26/26**).

Methods:
- `exact-IBB-triangle3`: 8
- `exact-Bernstein-minw`: 3
- `exact-Bernstein-raw`: 3
- `exact-hand-halfangle-contain`: 3
- `exact-Bernstein-tt-square-gap-endpoint`: 3
- `exact-Bernstein-halfangle-square`: 2
- `exact-hand-Or-endpoint`: 1
- `exact-Bernstein-cleared`: 1
- `exact-IBB-r28-hw-maxw`: 1
- `exact-Bernstein-tt-2w`: 1

Do **not** describe leftover (S) rows as machine-independent proofs.
Private pattern-match “exact-hand” labels without payloads were **not** counted.

## Remaining (S) by check file

| Check file | Remaining (S) |
| --- | ---: |
| `check_round26_g2_top` | 13 |
| `check_round38_empty_right_negative` | 13 |
| `check_round36_nonempty_closed` | 12 |
| `check_round34_left_negative` | 11 |
| `check_round27_g2_two_branches` | 10 |
| `check_round32_right_positive` | 9 |
| `check_round25_g3_complete` | 8 |
| `check_round30_corrected_geometry` | 8 |
| `check_round28_g2_near_complete` | 7 |
| `check_round35_positive_H` | 7 |
| `check_round24_g3_fside` | 6 |
| `check_round33_right_nonempty` | 6 |
| `check_round39_single_contact` | 5 |
| `check_round29_no_top_structure` | 5 |
| `check_round41_geometry` | 2 |
| `check_round29_far_top_complete` | 2 |
| `check_round24_g3_cside` | 1 |

Machine-readable: `S_tier_remaining.json`.
Still-open ledger: `item3_certs/still_S_after_batch24e.jsonl`.

## How to attempt further upgrades

```bash
python artifacts/closure/scripts/upgrade_batch24_exact.py
python artifacts/closure/scripts/check_exact_certs_batch24.py
```
