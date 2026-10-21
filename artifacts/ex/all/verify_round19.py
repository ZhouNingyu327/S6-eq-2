"""Replay new hand-proof checks and the precise round13 pair input.

The round18 ZIP is preserved and checked for identity/integrity, not replayed.
"""
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
    print("Fixed proof inputs and preserved round18 packet PASS",flush=True)
    start=time.perf_counter()
    run(root/"check_round19_top_gap.py",root)
    scalar=json.loads((root/"round19_top_gap_checks.json").read_text(encoding="utf-8"))
    assert scalar["all_queries_unsat"] and scalar["query_count"]==13
    assert scalar["NRA_queries"]==10 and scalar["LRA_queries"]==3
    assert len(scalar["symbolic_checks"])==8 and len(scalar["constant_checks"])==7
    print("Thirteen new scalar queries, eight symbolic checks, seven constants PASS",flush=True)
    run(root/"check_round13_pair.py",root)
    pair=json.loads((root/"round13_pair_checks.json").read_text(encoding="utf-8"))
    assert pair["certificate"]["parameter_rectangles"]==2
    assert pair["certificate"]["polynomial_identities"]==4
    assert sum(row["coefficients"] for row in pair["certificate"]["records"])==266
    assert len(pair["queries"])==1 and pair["queries"][0]["result"]=="unsat"
    print("Required pair input: 266 exact coefficients and one NRA query PASS",flush=True)
    archive=root/"S6_round18_verification.zip"
    with zipfile.ZipFile(archive) as old:
        assert old.testzip() is None
    historical={"archive":archive.name,
        "sha256":hashlib.sha256(archive.read_bytes()).hexdigest(),
        "archive_integrity":"passed","own_entry_replayed_in_this_round":False}
    assert historical["sha256"]=="5a36a07631662a322771b78adffdd974bd41a7c638d423873c08f2c262d038d5"
    result={
        "status":"all exact checks passed",
        "new_scope":"near G2 C top gap and right meeting: left gap excluded for all horizontal types",
        "combined_scope":"near G2 C top gap requires left/right meeting and F horizontal completely empty",
        "new_queries":13,"new_NRA_queries":10,"new_LRA_queries":3,
        "symbolic_checks":8,"constant_checks":7,
        "pair_input_recomputed_queries":1,"pair_input_coefficients":266,
        "pair_input_rectangles":2,"pair_input_polynomial_identities":4,
        "total_recomputed_queries":14,
        "historical_input":historical,
        "geometry_review":"S6_round19_geometric_review.md",
        "proof_method":"new top-endpoint diameter constraint, gap endpoints, shared-midpoint union, concave quadratic",
        "certificate_scope":"the round13 certificate is used only for extra necessary conditions of the still-open empty-horizontal top-gap case",
        "not_proved":"final empty-horizontal top-gap case; right-gap near case; far G2; all G2; G3/G4; S(6)=2",
        "python":platform.python_version(),"sympy":sympy.__version__,"z3":z3.get_version_string(),
        "seconds":time.perf_counter()-start,
    }
    (root/"verification_result.json").write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)


if __name__=="__main__":
    main()
