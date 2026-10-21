# How to reproduce (clean clone)

```bash
git clone https://github.com/ZhouNingyu327/S6-eq-2.git
cd S6-eq-2
```

## Required spot checks (no Lean / no SMT install)

```bash
cd artifacts/checkers
python3 check_round64.py    # needs round64_certificate.json (shipped) → passed
python3 check_round63.py    # self-contained → passed
cd ../closure
python3 m3_branch_checker.py  # Boolean M3.1 grid → PASS
```

## Certificate archive

```bash
cd artifacts
sha256sum -c SHA256SUMS.txt --ignore-missing   # or verify ex_all.tar.gz line
tar -tzf ex_all.tar.gz | head
# unpacked mirror:
ls ex/all | head
```

## Optional Lean skeleton

```bash
cd lean/S6Core
lake update   # first time
lake build    # skeleton only; Bool flags are metadata
```

## Optional heavier checkers

```bash
cd artifacts/checkers
python3 check_round55_final.py   # needs round55 + round54 JSON (shipped)
python3 check_round42.py         # may need `pip install z3-solver`
```

Full narrative: [../artifacts/REPRODUCE.md](../artifacts/REPRODUCE.md).
