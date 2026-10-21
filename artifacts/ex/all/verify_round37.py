"""Standalone root-cap and two empty-F orientation exclusions."""
from pathlib import Path
import hashlib
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
    old=base/"S6_round36_verification.zip"
    assert sha(old)=="cae171bb519027b2b69c4f05d8da92995c3f8eaff404ce05ef5be4d62dca574f"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round32.md","S6_attack_round36.md"]:
            assert archive.read(name)==(base/name).read_bytes(),name
    script="check_round37_empty_left_negative.py"
    proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
        capture_output=True,text=True,encoding="utf-8",errors="replace",
        env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
    assert proc.returncode==0,(proc.stdout,proc.stderr)
    data=json.loads((base/"round37_empty_left_negative_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":37,"NRA":34,"LRA":3,"symbolic_identities":10,"constants":15}
    assert all(t["result"]=="unsat" for t in data["queries"])
    review=(base/"S6_round37_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==40
    result={"status":"round37 standalone exact entry passed",
        "scope":data["scope"],"also_proved":data["also_proved"],
        "totals":data["totals"],"geometric_review_items":40,
        "historical_round36":{"sha256":sha(old),"crc":"passed","cited_source_bytes":"matched",
                             "own_full_entry_replayed":False},
        "global_root_cap_inputs":"round9 exclusive box and rounds12/23/25 C-mid exclusions, not re-proved by the local solver",
        "withdrawn_double_bridge_claim_counted":False,
        "old_UNKNOWN_queries_replayed_or_counted":False,
        "not_proved":data["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=True,indent=2))


if __name__=="__main__":
    main()
