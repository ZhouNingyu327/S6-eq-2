# Remaining (S)-tier dual-solver inventory

**As of:** 2026-10-22 (Asia/Shanghai).
**Sources:** `artifacts/closure/item3_certs/` (queue + upgrade_results_* + batch24–26e family), `certificate_counts.json`.

Status labels: **(E)** exact rational/Bernstein/CAD certificate; **(H)** hand + checkable identity; **(S)** dual-solver UNSAT only (not machine-independent).

## Headline counts

| Quantity | Value |
| --- | --- |
| Item3 queue unique keys (deduped) | 264 |
| Exact from Item3 batches 1–6 (unique) | 113 |
| **New exact from batch24–26e family (checkable)** | **144** |
| Exact Item3+batch24–26e unique | 257 |
| Still (S) / cvc5-only (unique) | **7** |
| Tracked unique total (M4) | 391 |

Baseline after batch25 / tip `006fb96`: 60 exact family / **91** (S). This push converts **84** of those 91 → **7** (S) left.

## Conversions this push family

Emitted **144** machine-checkable certificates under
`item3_certs/exact_certs_batch24/` with checker
`artifacts/closure/scripts/check_exact_certs_batch24.py` (**PASS 144/144**).

Methods:
- `exact-hand-tip-d-G`: 13
- `exact-Bernstein-raw`: 10
- `exact-IBB-triangle3`: 8
- `exact-hand-opposite-strict`: 7
- `exact-hand-tip-T-u`: 6
- `exact-hand-tip-e-h`: 6
- `exact-hand-diag-AJ`: 4
- `exact-hand-halfangle-contain`: 4
- `exact-Bernstein-bvv`: 3
- `exact-Bernstein-tt-square-gap-endpoint`: 3
- `exact-hand-Or-h-cascade`: 3
- `exact-hand-S1S2-phi`: 3
- `exact-Bernstein-minw`: 3
- `exact-hand-AMGM-ud`: 3
- `exact-hand-A-k-eta-cascade`: 3
- `exact-Bernstein-S1S2-rho`: 2
- `exact-hand-swA-endpoint`: 2
- `exact-hand-both-axis-disc`: 2
- `exact-hand-e-G-budget`: 2
- `exact-Bernstein-r26-ld`: 2
- `exact-hand-DL4-mu-budget`: 2
- `exact-Bernstein-halfangle-square`: 2
- `exact-hand-r41-proj-min`: 2
- `exact-hand-S1S2-phi-rho`: 2
- `exact-hand-Sigma-f-h0`: 2
- `exact-hand-eps-sum`: 2
- `exact-hand-g25-hx-identity`: 2
- `exact-IBB-raw`: 1
- `exact-hand-lrd-mu`: 1
- `exact-hand-A-U-l`: 1
- `exact-IBB-r28-hw-maxw`: 1
- `exact-Bernstein-Sigma-gap`: 1
- `exact-Bernstein-A-L2`: 1
- `exact-hand-tip-H-mu`: 1
- `exact-Bernstein-lKu-phi`: 1
- `exact-hand-ud-from-c`: 1
- `exact-hand-tip-d-hh`: 1
- `exact-Bernstein-eta-z-r`: 1
- `exact-hand-tip-lT-h`: 1
- `exact-hand-Or-endpoint`: 1
- `exact-hand-r28-ld-2w`: 1
- `exact-hand-r28-ld-6_5w`: 1
- `exact-Bernstein-hw11`: 1
- `exact-hand-hc-8mu`: 1
- `exact-hand-g25-S2E3`: 1
- `exact-hand-loss-Y`: 1
- `exact-Bernstein-or-t-budget`: 1
- `exact-Bernstein-or-eta-d`: 1
- `exact-Bernstein-z-d-eta`: 1
- `exact-hand-z-ll`: 1
- `exact-hand-L-E-w`: 1
- `exact-hand-hc-4mu`: 1
- `exact-hand-cl-su-half`: 1
- `exact-hand-tip-ed-h`: 1
- `exact-hand-rpp-disc`: 1
- `exact-Bernstein-r26-L3U2`: 1
- `exact-hand-ru-lt-mu`: 1
- `exact-hand-neg-sum`: 1
- `exact-hand-Kr-vs-Ku`: 1
- `exact-Bernstein-g25-S4U`: 1
- `exact-Bernstein-r36-halfangle`: 1
- `exact-hand-triangle-area`: 1
- `exact-hand-strict-interval-d`: 1
- `exact-hand-rr-ud`: 1
- `exact-Bernstein-bv-product`: 1
- `exact-Bernstein-ru-cwsw`: 1
- `exact-Bernstein-cleared`: 1
- `exact-Bernstein-tt-2w`: 1

## Still (S) after batch26e (7)

- `check_round25_g3_complete`: 3
- `check_round38_empty_right_negative`: 2
- `check_round30_corrected_geometry`: 1
- `check_round32_right_positive`: 1

Hard leftovers: g25 chord / H≥K / double-cover, η-z numeric IBB, corrected-geometry cover, and a few α/β diseq Or arms. No theorem-proved claim; lake/Lean is a separate track.

## Batch trail

| Batch | New exact (approx) | (S) left |
| --- | --- | --- |
| 24–25d | 60 | 91 |
| 26 / 26b / 26c | +61 → 121 | 30 |
| 26d | +21 → 142 | 9 |
| 26e | +2 → 144 | 7 |
