# Cert → Lean handoff (Bernstein / identity lifts)

**As of:** 2026-10-22 (Asia/Shanghai).  
**Cert tip:** `80e8ee0` (batch26f; family **151/151** PASS).  
**Checker:** `artifacts/closure/scripts/check_exact_certs_batch24.py`.  
**Cert dir:** `artifacts/closure/item3_certs/exact_certs_batch24/`.

Honest scope: these JSON certificates clear the dual-solver **(S)** inventory to recomputable **(E)/(H)**.
They are **inputs for Lean porting**, not a substitute for `principalClaimProvedUnconditionally` or end-to-end faithfulness.
Do **not** treat this handoff as theorem closure.

Existing Lean foothold: `BernsteinGridLift` (E-tier coeff nonneg + `g2_alg` bridge). Prefer lifting
**Bernstein / IBB** payloads first; tip/hand identities second (often need geometric lemmas already in
`G1G2Fragments` / tip-style modules).

## Priority order

### P1 — `exact-Bernstein-raw` (low-dim coeff lists; best first Lean targets)

- `artifacts/closure/item3_certs/exact_certs_batch24/check_round24_g3_fside__n4__a82de007c0.json` — `check_round24_g3_fside` n=4 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round27_g2_two_branches__n4__ba4d19a580.json` — `check_round27_g2_two_branches` n=4 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round29_no_top_structure__n6__5f3dda6861.json` — `check_round29_no_top_structure` n=6 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round29_no_top_structure__n6__866f1cfbe2.json` — `check_round29_no_top_structure` n=6 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round30_corrected_geometry__n3__81b6979c71.json` — `check_round30_corrected_geometry` n=3 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round30_corrected_geometry__n9__c76afaaaf1.json` — `check_round30_corrected_geometry` n=9 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round33_right_nonempty__n8__9f08d30032.json` — `check_round33_right_nonempty` n=8 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round35_positive_H__n4__c5807376e0.json` — `check_round35_positive_H` n=4 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round35_positive_H__n8__622d8fa357.json` — `check_round35_positive_H` n=8 (`exact-Bernstein-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round35_positive_H__n9__e2db3fea8c.json` — `check_round35_positive_H` n=9 (`exact-Bernstein-raw`)

**Count:** 10. Round IDs heavily in R24/R27/R29/R30/R33.

### P2 — Named 1-variable Bernstein families (reuse `bernstein_coeffs` pattern)

Representative (full list under cert dir by `method`):
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round24_g3_fside__n5__cbecdd171f.json` — `check_round24_g3_fside` n=5 (`exact-Bernstein-minw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round24_g3_fside__n7__ce41334842.json` — `check_round24_g3_fside` n=7 (`exact-Bernstein-bvv`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round25_g3_complete__n5__d1f1497dfb.json` — `check_round25_g3_complete` n=5 (`exact-Bernstein-minw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round25_g3_complete__n5__e43d6cfe6c.json` — `check_round25_g3_complete` n=5 (`exact-Bernstein-minw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round25_g3_complete__n8__12ea6e3a3d.json` — `check_round25_g3_complete` n=8 (`exact-Bernstein-g25-chord`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round25_g3_complete__n8__aa4c338fcf.json` — `check_round25_g3_complete` n=8 (`exact-Bernstein-g25-S4U`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round26_g2_top__n7__44d9df748d.json` — `check_round26_g2_top` n=7 (`exact-Bernstein-r26-ld`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round26_g2_top__n7__69e7323738.json` — `check_round26_g2_top` n=7 (`exact-Bernstein-bvv`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round26_g2_top__n7__7905cebf07.json` — `check_round26_g2_top` n=7 (`exact-Bernstein-r26-ld`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round26_g2_top__n7__9b6f03fd30.json` — `check_round26_g2_top` n=7 (`exact-Bernstein-r26-L3U2`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round27_g2_two_branches__n9__a80fbdcce8.json` — `check_round27_g2_two_branches` n=9 (`exact-Bernstein-hw11`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round28_g2_near_complete__n5__023bbe2fb6.json` — `check_round28_g2_near_complete` n=5 (`exact-Bernstein-tt-2w`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round28_g2_near_complete__n5__81d4ac97a5.json` — `check_round28_g2_near_complete` n=5 (`exact-Bernstein-tt-square-gap-endpoint`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round28_g2_near_complete__n5__b4013f035d.json` — `check_round28_g2_near_complete` n=5 (`exact-Bernstein-tt-square-gap-endpoint`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round28_g2_near_complete__n5__e725afebfd.json` — `check_round28_g2_near_complete` n=5 (`exact-Bernstein-tt-square-gap-endpoint`)
- …
**Count:** 31. Standouts for Lean:
- `exact-Bernstein-g25-chord` — R25 n=8 (squared Weierstrass gap; no √ in final poly)
- `exact-Bernstein-bvv` / `minw` / `tt-square-gap-endpoint` — R24/R25/R28
- `exact-Bernstein-r26-ld` / `r26-L3U2` — R26
- `exact-Bernstein-S1S2-rho` / `Sigma-gap` / `r36-halfangle` — R33/R35/R36
- `exact-Bernstein-eta-z-r` / `z-d-eta` / `or-eta-d` / `lKu-phi` — R34/R38

### P3 — Rational IBB leaf boxes

- `artifacts/closure/item3_certs/exact_certs_batch24/check_round28_g2_near_complete__n5__9855fce607.json` — `check_round28_g2_near_complete` n=5 (`exact-IBB-r28-hw-maxw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round32_right_positive__n8__78a5a46ff1.json` — `check_round32_right_positive` n=8 (`exact-IBB-triangle3`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round33_right_nonempty__n12__05c3f3a323.json` — `check_round33_right_nonempty` n=12 (`exact-IBB-triangle3`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round33_right_nonempty__n13__46bade99ee.json` — `check_round33_right_nonempty` n=13 (`exact-IBB-triangle3`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round34_left_negative__n8__5e19d78058.json` — `check_round34_left_negative` n=8 (`exact-IBB-triangle3`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round35_positive_H__n12__c23d75b876.json` — `check_round35_positive_H` n=12 (`exact-IBB-triangle3`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round38_empty_right_negative__n7__bd26f7b647.json` — `check_round38_empty_right_negative` n=7 (`exact-IBB-raw`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round38_empty_right_negative__n8__93e5a9a520.json` — `check_round38_empty_right_negative` n=8 (`exact-IBB-triangle3`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round39_single_contact__n7__93f5a6f026.json` — `check_round39_single_contact` n=7 (`exact-IBB-triangle3`)
- `artifacts/closure/item3_certs/exact_certs_batch24/check_round39_single_contact__n9__14f5e26215.json` — `check_round39_single_contact` n=9 (`exact-IBB-triangle3`)

**Count:** 10 (`exact-IBB-triangle3`, `exact-IBB-raw`, `exact-IBB-r28-hw-maxw`).
Lean path: port leaf-box sign checks (already rational endpoints in JSON).

### P4 — Tip / Weierstrass identities (hand, structurally checkable)

**Count:** 33. Dominant methods: `exact-hand-tip-d-G`, `tip-T-u`, `tip-e-h`, `tip-HK-L`, `tip-ud-ratio`.
Round IDs: R26/R27/R28/R34/R38. Best after a shared Lean Weierstrass/`h(1+p)=s` lemma.

### P5 — Budget / Or / opposite / cascade hands

**Count:** 67. Includes AM-GM `ud`, Or-cascades, opposite-strict, η-u budget, geometry `sl-ud` / `sr-beta`.
Usually need case-split lemmas more than Bernstein machinery.

## Bernstein/IBB density by round ID

| Round | # Bernstein/IBB certs in family |
| --- | --- |
| R24 | 3 |
| R25 | 4 |
| R26 | 4 |
| R27 | 2 |
| R28 | 5 |
| R29 | 2 |
| R30 | 2 |
| R32 | 1 |
| R33 | 4 |
| R34 | 5 |
| R35 | 6 |
| R36 | 2 |
| R38 | 6 |
| R39 | 5 |

## Suggested Lean work order

1. Generalize `BernsteinGridLift` to consume JSON `numer_coeffs` on a stated box (P1).
2. Add one lemma per named 1D family in P2 (start: `g25-chord`, `bvv`, `tt-square-gap-endpoint`).
3. IBB triangle leaves (P3) as Finset/box induction.
4. Shared tip identity (P4) once; instantiate per round.
5. Defer P5 until the geometric bridges those budgets feed are inhabited.

## Non-goals

- Editing `lean/S6Core` theorem files from the cert track without coordinating the Lean executor.
- Claiming principal claim / external review closed because (S)=0.


## Lean lift status (BernsteinExactP1–P3)

Committed modules (payload-side `native_decide` only; **not** PrincipalClaim):

| Module | Scope | Status |
| --- | --- | --- |
| `lean/S6Core/S6Core/BernsteinExactP1.lean` | all 10 `exact-Bernstein-raw` numer/denom | lake-green |
| `lean/S6Core/S6Core/BernsteinExactP2.lean` | 28/31 named Bernstein coeff lists (nonneg/nonpos); 3 claim-only skipped | lake-green |
| `lean/S6Core/S6Core/BernsteinExactP3.lean` | all 10 IBB handoff certs; 195 leaf range theorems | lake-green |

Wired in `lean/S6Core/S6Core.lean` next to `BernsteinGridLift` only. Manifest: `artifacts/closure/item3_certs/bernstein_lean_lift_manifest.json`.


## Lean lift status (BernsteinExactP4–P5 + Extra)

| Module | Scope | Status |
| --- | --- | --- |
| `BernsteinExactP4.lean` | tip e-h / d-G / half-angle numer; catalog 40 | lake-green |
| `BernsteinExactP5.lean` | budget/Or catalog 60 + 4 numeric coeff lists + AM-GM cleared | lake-green |
| `BernsteinExactExtra.lean` | tip branch A/B/C rational samples + count checks | lake-green |

Still honest: these lifts verify certificate algebra / payloads — **not** PrincipalClaim unconditional.

## Near-end / R13–R28 Lean lifts (openai/math track)

| Module | Content | Status |
|--------|---------|--------|
| `S6Core.Round13PairBernstein` | ~46 R13 pair Bernstein row nonneg | lake-green |
| `S6Core.NearEndExactR24_28` | 20 uniform-sign ℚ payloads R24–28 | lake-green |
| `S6Core.NearEndExactR24_28Extra` | +35 more R24–28 payloads | lake-green |
| `S6Core.LivingLeafStrengthen` | 17-living list, closer multiplicities, bothGap/rightGap inventory | lake-green |

Honest: these lifts ≠ geometric `LivingLeafExcluded` for the 17 living leaves ≠ `PrincipalClaim`.
Forbidden (bridge executor): `MainTheorem`, `G5ExclusionFrag`, `AxisG5k0FromCover` — not edited.
| `S6Core.NearEndAdjacentExact` | +48 R29–R32/R41 + R13 leftover payloads | lake-green |

