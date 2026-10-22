"""Recompute exact small checks and the pair input; preserve round19 packet."""
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys
import time
import zipfile

import sympy
import z3


def run(script, root):
    process=subprocess.run([sys.executable,str(script)],cwd=root,capture_output=True,
        text=True,encoding="utf-8",errors="replace")
    (root/(script.name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
    assert process.returncode==0,(script.name,process.stdout,process.stderr)


def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/"manifest.json").read_text(encoding="utf-8"))
    for name,expected in manifest["files"].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
    print("Fixed proof inputs and preserved round19 packet PASS",flush=True)
    start=time.perf_counter()
    run(root/"check_round20_g3_g4.py",root)
    data=json.loads((root/"round20_g3_g4_checks.json").read_text(encoding="utf-8"))
    assert data["status"]=="exact checks passed" and data["query_count"]==13
    assert data["NRA_queries"]==5 and data["LRA_queries"]==8
    assert data["new_scalar_consequence_queries"]==6
    assert data["historical_applicability_and_input_queries"]==7
    assert len(data["G3_host_orbits"])==3
    assert data["G4_ordered_host_representatives"]==[[3,2],[4,2],[4,3]]
    counter=json.loads((root/"round20_G3_local_counterexample.json").read_text(encoding="utf-8"))
    assert counter==data["exact_counterexample"]
    assert counter["union_grid_length_approx"]>4
    print("Thirteen scalar/input checks, two host classifications, exact local counterexample PASS",flush=True)
    run(root/"check_round13_pair.py",root)
    pair=json.loads((root/"round13_pair_checks.json").read_text(encoding="utf-8"))
    assert pair["certificate"]["parameter_rectangles"]==2
    assert pair["certificate"]["polynomial_identities"]==4
    assert sum(row["coefficients"] for row in pair["certificate"]["records"])==266
    assert len(pair["queries"])==1 and pair["queries"][0]["result"]=="unsat"
    print("Required pair input: 266 exact coefficients and one NRA query PASS",flush=True)
    archive=root/"S6_round19_verification.zip"
    with zipfile.ZipFile(archive) as old:
        assert old.testzip() is None
    historical={"archive":archive.name,
        "sha256":hashlib.sha256(archive.read_bytes()).hexdigest(),
        "archive_integrity":"passed","own_entry_replayed_in_this_round":False}
    assert historical["sha256"]=="bd745def7e1b561f9dd417d07aa8228ecb4d36c9d5f168e2d7ff329903de84ea"
    result={
        "status":"all exact checks passed",
        "scope":"new G3 top/bottom gap necessity; G4 diagonal positive exclusion; G4 T8 negative exclusion",
        "scalar_checks":13,"new_consequence_checks":6,"applicability_and_input_checks":7,
        "NRA_scalar_checks":5,"LRA_scalar_checks":8,
        "pair_input_recomputed_queries":1,"pair_input_coefficients":266,
        "pair_input_rectangles":2,"pair_input_polynomial_identities":4,
        "total_recomputed_queries":14,
        "host_classification_checks":2,
        "exact_counterexample":"G3 two anchored blocks can have grid union length 4 sqrt(2)-157/100 >4; this is not a target covering",
        "historical_input":historical,
        "geometry_review":"S6_round20_geometric_review.md",
        "proof_method":"quarter-boundary budgets, long chords, actual gap endpoints and historical lemma applicability",
        "computer_assisted_scope":"T8 negative exclusion and diagonal J>0 use the freshly reverified round13 pair certificate",
        "not_proved":"entire G3/G4; remaining G2; S(6)=2",
        "global_bound":"2 <= S(6) <2.03",
        "python":platform.python_version(),"sympy":sympy.__version__,"z3":z3.get_version_string(),
        "seconds":time.perf_counter()-start,
    }
    (root/"verification_result.json").write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)


if __name__=="__main__":
    main()
