"""Verify the analytic scalar checks and replay the required round13 input."""
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys
import tempfile
import time
import zipfile

import sympy
import z3


def run(script, cwd):
    process = subprocess.run([sys.executable, str(script)], cwd=cwd,
        capture_output=True, text=True, encoding="utf-8", errors="replace")
    (cwd/(script.name+".log")).write_text(process.stdout+process.stderr, encoding="utf-8")
    assert process.returncode == 0, (script.name, process.stdout, process.stderr)


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root/"manifest.json").read_text(encoding="utf-8"))
    for name, expected in manifest["files"].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest() == expected, name
    print("Immutable file hashes PASS", flush=True)
    start = time.perf_counter()
    run(root/"check_round17_analytic_negative.py", root)
    scalar = json.loads((root/"round17_analytic_negative_checks.json").read_text(encoding="utf-8"))
    assert scalar["all_queries_unsat"] and scalar["query_count"] == 9
    assert scalar["NRA_queries"] == 7 and scalar["LRA_queries"] == 2
    assert len(scalar["symbolic_checks"]) == 7 and len(scalar["rational_checks"]) == 6
    print("Nine analytic-step queries and exact identities PASS", flush=True)
    # The archived dependency is extracted afresh; its own manifest and entry
    # are checked, not merely the enclosing ZIP hash.
    with tempfile.TemporaryDirectory(prefix="round17_input_", dir=root) as folder:
        dependency_root = Path(folder).resolve()
        with zipfile.ZipFile(root/"S6_round13_verification.zip") as archive:
            for name in archive.namelist():
                candidate = (dependency_root/name).resolve()
                assert candidate.is_relative_to(dependency_root), name
            archive.extractall(dependency_root)
        run(dependency_root/"verify_round13.py", dependency_root)
        dependency = json.loads((dependency_root/"verification_result.json").read_text(encoding="utf-8"))
        assert dependency["status"] == "all exact checks passed"
        assert dependency["total_recomputed_queries"] == 13
        assert sum(r["coefficients"] for r in dependency["pair_certificate"]["records"]) == 266
        (root/"round13_input_verification_result.json").write_text(
            json.dumps(dependency, ensure_ascii=False, indent=2), encoding="utf-8")
    print("Required round13 input: 266 coefficients and 13 queries PASS", flush=True)
    result = {
        "status": "all exact checks passed",
        "scope": "near G2 right/top corner meeting and F negative horizontal nonempty excluded",
        "new_scalar_queries": 9, "new_NRA_queries": 7, "new_LRA_queries": 2,
        "symbolic_checks": 7, "exact_constant_comparisons": 6,
        "required_round13_recomputed_queries": 13, "required_round13_coefficients": 266,
        "proof_method": "hand inequalities, gap-endpoint diameter and shared-midpoint union; no new subdivision certificate",
        "geometric_premise_review": "see S6_round17_geometric_review.md; solver checks do not establish point ownership",
        "not_proved": "positive horizontal phase; entire G2; G3/G4; S(6)=2",
        "python": platform.python_version(), "sympy": sympy.__version__,
        "z3": z3.get_version_string(), "seconds": time.perf_counter()-start,
    }
    (root/"verification_result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(result, ensure_ascii=False, indent=2), flush=True)


if __name__ == "__main__":
    main()
