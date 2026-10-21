"""Standalone scalar and integrity entry for complete standardized far TOP G2."""
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
    old=base/"S6_round28_verification.zip"
    assert sha(old)=="3ad18733f9d6c11d8fee7c46a8558c5d2b27485729e345696b66c18c8ab207f0"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        assert archive.read("S6_attack_round28.md")==(base/"S6_attack_round28.md").read_bytes()
    script="check_round29_far_top_complete.py"
    proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
        capture_output=True,text=True,encoding="utf-8",errors="replace",
        env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
    assert proc.returncode==0,(proc.stdout,proc.stderr)
    data=json.loads((base/"round29_far_top_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":17,"NRA":15,"LRA":2,"symbolic_identities":12,"constants":31}
    assert all(row["result"]=="unsat" for row in data["queries"])
    review=(base/"S6_round29_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==32
    result={"status":"round29 exact entry passed",
        "scope":["Far TOP positive C excluded for direct right join and original-W bridge",
                 "Combined rounds27 and29 exclude standardized far TOP real-gap family",
                 "All near G2 remains excluded by unchanged round28"],
        "totals":data["totals"],"geometric_review_items":32,
        "historical_round28":{"sha256":sha(old),"crc":"passed","own_full_entry_replayed":False},
        "research_diagnostics_replayed":False,
        "not_proved":"Far no-TOP real-gap residuals; entire G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03",
        "not_used":"round13 266-coefficient adjacent-corner certificate in new chains; "
                   "layout optimization; fixed-point coverage search; angle samples; interval tree"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
