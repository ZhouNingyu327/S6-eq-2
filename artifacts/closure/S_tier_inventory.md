# Remaining (S)-tier dual-solver inventory

**As of:** 2026-10-22 (Asia/Shanghai).
**Sources:** `artifacts/closure/item3_certs/` (queue + upgrade_results_* + batch24–26f family), `certificate_counts.json`.

Status labels: **(E)** exact rational/Bernstein/CAD certificate; **(H)** hand + checkable identity; **(S)** dual-solver UNSAT only (not machine-independent).

## Headline counts

| Quantity | Value |
| --- | --- |
| Item3 queue unique keys (deduped) | 264 |
| Exact from Item3 batches 1–6 (unique) | 113 |
| **New exact from batch24–26f family (checkable)** | **151** |
| Exact Item3+batch24–26f unique | 264 |
| Still (S) / cvc5-only (unique) | **0** |
| Tracked unique total (M4) | 391 |

Baseline after batch25 / tip `006fb96`: 60 exact family / **91** (S).
Tip `f493430`: 144 exact / **7** (S).
**This push converts the last 7 → remaining (S) = 0.**

## Conversions this push family

Emitted **151** machine-checkable certificates under
`item3_certs/exact_certs_batch24/` with checker
`artifacts/closure/scripts/check_exact_certs_batch24.py` (**PASS 151/151**).

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
- `exact-Bernstein-g25-chord`: 1
- `exact-hand-geometry-sr-beta`: 1
- `exact-IBB-raw`: 1
- `exact-hand-lrd-mu`: 1
- `exact-hand-A-U-l`: 1
- `exact-IBB-r28-hw-maxw`: 1
- `exact-Bernstein-Sigma-gap`: 1
- `exact-Bernstein-A-L2`: 1
- `exact-hand-tip-H-mu`: 1
- `exact-Bernstein-lKu-phi`: 1
- `exact-hand-tip-HK-L`: 1
- `exact-hand-tip-ud-ratio`: 1
- `exact-hand-ud-from-c`: 1
- `exact-hand-tip-d-hh`: 1
- `exact-Bernstein-eta-z-r`: 1
- `exact-hand-tip-lT-h`: 1
- `exact-hand-Or-endpoint`: 1
- `exact-hand-r28-ld-2w`: 1
- `exact-hand-r28-ld-6_5w`: 1
- `exact-Bernstein-hw11`: 1
- `exact-hand-hc-8mu`: 1
- `exact-hand-geometry-sl-ud`: 1
- `exact-hand-g25-S2E3`: 1
- `exact-hand-loss-Y`: 1
- `exact-hand-g25-U-t-casesplit`: 1
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
- `exact-hand-eta-u-budget-G`: 1
- `exact-hand-rr-ud`: 1
- `exact-Bernstein-bv-product`: 1
- `exact-Bernstein-ru-cwsw`: 1
- `exact-Bernstein-cleared`: 1
- `exact-Bernstein-tt-2w`: 1

## Still (S) after batch26f

**None.** The post-batch25 set of 91 dual-solver (S) rows now all have recomputable (E)/(H) certificates.

Last-7 methods (batch26f):
- `check_round25_g3_complete#8` → Bernstein g25-chord (squared gap on Weierstrass arc)
- `check_round25_g3_complete#11` → tip identity H≥K ⇒ L≤(3H+1)/(H+1), covering=1 at μ=1
- `check_round25_g3_complete#12` → case-split t vs 1−h on μ_A/μ_B caps (Bernstein 4−5h−h²)
- `check_round38_empty_right_negative#8` → G=2η/(1+η)>8η/5 + budget vs u/(2−u)
- `check_round38_empty_right_negative#12` → ratio+covering equality at d_min, strict α+1<cμ
- `check_round30_corrected_geometry#14` → max ℓ(1−s/c)+r =1/c−s²/(2c²)<1<μ
- `check_round32_right_positive#22` → r=(c/s)d & c(μ+ℓ)<1 ⇒ ℓ+r−d<μ (cases μs≷1)

No theorem-proved claim; lake/Lean is a separate track.

## Batch trail

| Batch | Exact family | (S) left |
| --- | --- | --- |
| 24–25d (`006fb96`) | 60 | 91 |
| 26–26e (`f493430`) | 144 | 7 |
| 26f (current) | 151 | **0** |
