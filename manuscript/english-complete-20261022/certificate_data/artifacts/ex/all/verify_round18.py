"""Replay the new analytic checks; identify historical inputs by hashes.

The historical packets are preserved inputs, not newly recomputed by this
entry.  Their own verification entries can be run separately.
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


def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/"manifest.json").read_text(encoding="utf-8"))
    for name,expected in manifest["files"].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
    print("Fixed new proof inputs and preserved historical packets PASS",flush=True)
    start=time.perf_counter()
    script=root/"check_round18_positive_projection.py"
    p=subprocess.run([sys.executable,str(script)],cwd=root,capture_output=True,
        text=True,encoding="utf-8",errors="replace")
    (root/(script.name+".log")).write_text(p.stdout+p.stderr,encoding="utf-8")
    assert p.returncode==0,(p.stdout,p.stderr)
    data=json.loads((root/"round18_positive_projection_checks.json").read_text(encoding="utf-8"))
    assert data["all_queries_unsat"] and data["query_count"]==9
    assert data["NRA_queries"]==7 and data["LRA_queries"]==2
    assert len(data["symbolic_checks"])==7 and len(data["constant_checks"])==3
    rejected=json.loads((root/"round18_draft_relaxed_axis_check.json").read_text(encoding="utf-8"))
    assert rejected["queries"][0]["result"]=="sat"
    assert sum(row["result"]=="unsat" for row in rejected["queries"])==8
    historical={}
    for name in ["S6_round16_verification.zip","S6_round17_verification.zip"]:
        path=root/name
        with zipfile.ZipFile(path) as archive:
            assert archive.testzip() is None
        historical[name]={"sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                         "archive_integrity":"passed",
                         "own_entry_replayed_in_this_round":False}
    result={
        "status":"all new exact checks passed",
        "new_scope":"near G2 right/top meeting and F positive horizontal nonempty excluded",
        "combined_scope":"with audited rounds16/17: all near G2 right/top meeting excluded",
        "remaining_classification":"near right/top exactly one gap, entirely C; any left gap entirely F",
        "new_queries":9,"new_NRA_queries":7,"new_LRA_queries":2,
        "symbolic_checks":7,"constant_checks":3,
        "retained_draft_counterexample":"relaxed non-strict C projection admits the axis; actual strict geometry excludes it",
        "historical_inputs":historical,
        "geometric_review":"S6_round18_geometric_review.md",
        "proof_method":"hand projection inequalities and two nonempty parallel-trace budgets",
        "not_proved":"other near meeting patterns; remaining far G2; entire G2; G3/G4; S(6)=2",
        "python":platform.python_version(),"sympy":sympy.__version__,"z3":z3.get_version_string(),
        "seconds":time.perf_counter()-start,
    }
    (root/"verification_result.json").write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)


if __name__=="__main__":
    main()
