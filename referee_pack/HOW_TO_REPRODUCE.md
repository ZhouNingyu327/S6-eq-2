# How to reproduce (clean clone)

```bash
git clone https://github.com/ZhouNingyu327/S6-eq-2.git
cd S6-eq-2
```

## Required spot checks (no Lean)

```bash
cd artifacts/checkers
python3 check_round64.py    # companion JSON shipped → expect PASS
python3 check_round63.py    # self-contained → expect PASS
cd ../closure
python3 m3_branch_checker.py  # Boolean M3.1 grid → PASS
```

## Early G5 certificates (R8 / R13 / R16)

Requires `pip install z3-solver sympy` (scripts import `z3` even when verifying the shipped rational certificate).

```bash
cd artifacts/ex/all
python3 check_round8_two_corners.py   # needs round8_pair_bernstein_certificate.json (shipped)
python3 check_round13_pair.py         # needs round13_pair_certificate.json (shipped)

# R16: generate trees, then verify
python3 check_round16_interval_cover.py --sign 1
python3 check_round16_interval_cover.py --sign -1
python3 verify_round16_fraction_certificate.py
```

## Certificate archive

```bash
cd artifacts
sha256sum -c SHA256SUMS.txt --ignore-missing
ls ex/all | head
```

## Optional Lean skeleton

```bash
cd lean/S6Core
lake update   # first time
lake build    # skeleton only; Bool flags are metadata; Major 3 still open
```

## Optional heavier checkers

```bash
cd artifacts/checkers
python3 check_round55_final.py
python3 check_round42.py         # may need `pip install z3-solver`
cd ..
python3 audit/g3_alignment_check.py
```

Full narrative: [../artifacts/REPRODUCE.md](../artifacts/REPRODUCE.md).
