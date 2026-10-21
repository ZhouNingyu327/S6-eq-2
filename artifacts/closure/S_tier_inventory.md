# Remaining (S)-tier dual-solver inventory

**As of:** 2026-10-22 (Asia/Shanghai).
**Sources:** `artifacts/closure/item3_certs/` (queue + upgrade_results_* + batch24/25 family), `certificate_counts.json`.

Status labels: **(E)** exact rational/Bernstein/CAD certificate; **(H)** hand + checkable identity; **(S)** dual-solver UNSAT only (not machine-independent).

## Headline counts

| Quantity | Value |
| --- | --- |
| Item3 queue unique keys (deduped) | 264 |
| Exact from Item3 batches 1–6 (unique) | 113 |
| **New exact from batch24/25 family (checkable)** | **60** |
| Exact Item3+batch24/25 unique | 173 |
| Still (S) / cvc5-only (unique) | **91** |
| Tracked unique total (M4) | 391 |

## Conversions this push family

Emitted **60** machine-checkable certificates under
`item3_certs/exact_certs_batch24/` with checker
`artifacts/closure/scripts/check_exact_certs_batch24.py` (**PASS 60/60**).

Methods:
- `exact-Bernstein-raw`: 10
- `exact-IBB-triangle3`: 8
- `exact-hand-halfangle-contain`: 4
- `exact-Bernstein-tt-square-gap-endpoint`: 3
- `exact-Bernstein-minw`: 3
- `exact-Bernstein-r26-ld`: 2
- `exact-Bernstein-halfangle-square`: 2
- `exact-hand-r41-proj-min`: 2
- `exact-hand-g25-hx-identity`: 2
- `exact-IBB-raw`: 1
- `exact-IBB-r28-hw-maxw`: 1
- `exact-Bernstein-Sigma-gap`: 1
- `exact-Bernstein-A-L2`: 1
- `exact-Bernstein-lKu-phi`: 1
- `exact-hand-Or-endpoint`: 1
- `exact-hand-r28-ld-2w`: 1
- `exact-hand-r28-ld-6_5w`: 1
- `exact-hand-AMGM-ud`: 1
- `exact-hand-g25-S2E3`: 1
- `exact-Bernstein-or-t-budget`: 1
- `exact-hand-eps-sum`: 1
- `exact-Bernstein-or-eta-d`: 1
- `exact-hand-cl-su-half`: 1
- `exact-hand-rpp-disc`: 1
- `exact-Bernstein-r26-L3U2`: 1
- `exact-hand-ru-lt-mu`: 1
- `exact-hand-swA-endpoint`: 1
- `exact-Bernstein-g25-S4U`: 1
- `exact-Bernstein-r36-halfangle`: 1
- `exact-hand-strict-interval-d`: 1
- `exact-hand-rr-ud`: 1
- `exact-Bernstein-cleared`: 1
- `exact-Bernstein-tt-2w`: 1

Do **not** describe leftover (S) rows as machine-independent proofs.

## Remaining (S) by check file

| Check file | Remaining (S) |
| --- | ---: |
| `check_round26_g2_top` | 10 |
| `check_round34_left_negative` | 10 |
| `check_round27_g2_two_branches` | 10 |
| `check_round38_empty_right_negative` | 9 |
| `check_round36_nonempty_closed` | 9 |
| `check_round32_right_positive` | 8 |
| `check_round30_corrected_geometry` | 6 |
| `check_round25_g3_complete` | 5 |
| `check_round28_g2_near_complete` | 4 |
| `check_round24_g3_fside` | 4 |
| `check_round35_positive_H` | 4 |
| `check_round39_single_contact` | 3 |
| `check_round33_right_nonempty` | 3 |
| `check_round29_no_top_structure` | 3 |
| `check_round29_far_top_complete` | 2 |
| `check_round24_g3_cside` | 1 |

Machine-readable: `S_tier_remaining.json`.
Still-open ledger: `item3_certs/still_S_after_batch25d.jsonl`.
