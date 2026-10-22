"""Entry for the flat frozen round24 packet. Does not replay old full entries."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import zipfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    base=Path(__file__).resolve().parent
    manifest=json.loads((base/"manifest.json").read_text(encoding="utf-8"))
    for name,expected in manifest["files"].items():
        assert sha(base/name)==expected, name
    old=base/"S6_round23_verification.zip"
    assert sha(old)=="e659a86ecd6e683345be337acc2567072fca2e510566cd58db7ae1dc9dd0dc96"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
    scripts=["check_round24_g3_fside.py","review_round24_diagnostics.py"]
    for name in scripts:
        process=subprocess.run([sys.executable,str(base/name)],cwd=base,
            capture_output=True,text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (base/(name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
        assert process.returncode==0,(name,process.stdout,process.stderr)
    checks=json.loads((base/"round24_g3_fside_checks.json").read_text(encoding="utf-8"))
    diagnostic=json.loads((base/"round24_diagnostic_review.json").read_text(encoding="utf-8"))
    assert checks["totals"]=={"UNSAT":32,"NRA":29,"LRA":3,
                             "symbolic_identities":30,"constants":15}
    assert all(x["result"]=="unsat" for x in checks["queries"])
    assert diagnostic["counts_excluded_from_formal_UNSAT"]
    exploratory=json.loads((base/"round24_g3_bridge_exploration.json").read_text(encoding="utf-8"))
    assert [x["result"] for x in exploratory]==["unsat","unknown","unknown","unknown"]
    result={
        "status":"round24 exact entry passed",
        "scope":"Entire G3 TOP V3 / BOTTOM V2 representative impossible for every mu>1",
        "new_formal_checks":checks["totals"],
        "geometric_review_items":26,
        "geometric_review":"separate human-readable premise and case audit; not solver queries",
        "diagnostics":{"exact_local_witnesses_replayed":2,
                       "covering_counterexamples":0,
                       "included_in_formal_UNSAT_total":False},
        "exploratory":{"saved_UNSAT":1,"saved_timeouts":3,
                       "replayed":False,"used_as_proof":False},
        "historical_round23":{"sha256":sha(old),"crc":"passed",
                              "own_complete_entry_replayed":False,
                              "historical_sources_preserved":True},
        "not_proved":"Other two G3 host representatives; remaining G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
