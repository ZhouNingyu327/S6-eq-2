"""Standalone exact entry for far three meetings with nonempty F horizontal."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import zipfile


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    base=Path(__file__).resolve().parent
    manifest=json.loads((base/"manifest.json").read_text(encoding="utf-8"))
    for name,digest in manifest["files"].items():
        assert sha(base/name)==digest,name
    old=base/"S6_round30_verification.zip"
    assert sha(old)=="933414f95a5623ec4fe86cc5798ca994022000a404ab68538dc824c3b1479e7b"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        assert archive.read("S6_attack_round30.md")==(base/"S6_attack_round30.md").read_bytes()
        assert archive.read("S6_round29_continuation_notes.md")==(base/"S6_round29_continuation_notes.md").read_bytes()
    def run(script):
        proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
            capture_output=True,text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
        assert proc.returncode==0,(proc.stdout,proc.stderr)
    run("check_round31_three_nonempty.py")
    geometry=json.loads((base/"round31_three_nonempty_checks.json").read_text(encoding="utf-8"))
    assert geometry["totals"]=={"UNSAT":18,"NRA":17,"LRA":1,"symbolic_identities":6,"constants":8}
    assert all(row["result"]=="unsat" for row in geometry["queries"])
    run("check_round31_extended_pair.py")
    new=json.loads((base/"round31_extended_pair_checks.json").read_text(encoding="utf-8"))
    assert new["coefficients"]==162 and new["polynomial_identities"]==4
    # Explicitly replay only the old exact polynomial certificate, not its NRA query.
    spec=importlib.util.spec_from_file_location("old13_pair",base/"check_round13_pair.py")
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    legacy=module.certificate()
    assert legacy["polynomial_identities"]==4
    assert sum(row["coefficients"] for row in legacy["records"])==266
    (base/"round31_old13_certificate_checks.json").write_text(
        json.dumps(legacy,ensure_ascii=False,indent=2),encoding="utf-8")
    review=(base/"S6_round31_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==36
    result={"status":"round31 standalone exact entry passed",
        "scope":"Entire far three-meeting family with every nonempty F horizontal trace excluded",
        "geometry_queries":geometry["totals"],"geometric_review_items":36,
        "new_local_pair_certificate":new,
        "legacy_round13_certificate_only":{
            "polynomial_identities":4,"coefficients":266,"old_NRA_query_replayed":False},
        "totals":{"UNSAT":18,"NRA":17,"LRA":1,"symbolic_identities":14,
                  "constants":8,"nonnegative_rational_coefficients":428},
        "historical_round30":{"sha256":sha(old),"crc":"passed","own_full_entry_replayed":False},
        "early_UNKNOWN_or_withdrawn_checks_counted":False,
        "not_proved":"LEFT gap, RIGHT gap, three meetings with F horizontal empty; entire G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=True,indent=2))


if __name__=="__main__":
    main()
