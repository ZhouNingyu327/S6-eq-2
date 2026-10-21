"""Standalone LEFT-negative exclusion entry; historical entries not replayed."""
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
    old=base/"S6_round33_verification.zip"
    assert sha(old)=="78efb81af41ecf8d8a367523557ab1fb63a2d6be1b70be31192a9d4afd8213ef"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round32.md","S6_attack_round33.md","S6_round33_continuation_notes.md"]:
            assert archive.read(name)==(base/name).read_bytes(),name
    script="check_round34_left_negative.py"
    proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
        capture_output=True,text=True,encoding="utf-8",errors="replace",
        env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
    assert proc.returncode==0,(proc.stdout,proc.stderr)
    data=json.loads((base/"round34_left_negative_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":23,"NRA":21,"LRA":2,"symbolic_identities":7,"constants":9}
    assert all(row["result"]=="unsat" for row in data["queries"])
    review=(base/"S6_round34_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==26
    result={"status":"round34 standalone entry passed",
        "scope":data["scope"],"also_proved":data["also_proved"],
        "totals":data["totals"],"geometric_review_items":26,
        "historical_round33":{"sha256":sha(old),"crc":"passed","cited_source_bytes":"matched",
                              "own_full_entry_replayed":False},
        "not_proved":data["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=True,indent=2))


if __name__=="__main__":
    main()
