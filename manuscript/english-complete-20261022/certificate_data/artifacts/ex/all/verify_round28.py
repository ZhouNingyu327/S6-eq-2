"""Standalone scalar and integrity entry for complete near G2."""
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
    old=base/"S6_round27_verification.zip"
    assert sha(old)=="4c5634291e96abe05268b52e19a30035dd6ec3a4480080ac7ff641946cea4f66"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        assert archive.read("S6_attack_round27.md")==(base/"S6_attack_round27.md").read_bytes()
    script="check_round28_g2_near_complete.py"
    proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
        capture_output=True,text=True,encoding="utf-8",errors="replace",
        env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
    assert proc.returncode==0,(proc.stdout,proc.stderr)
    data=json.loads((base/"round28_g2_near_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":25,"NRA":23,"LRA":2,"symbolic_identities":14,"constants":10}
    assert all(row["result"]=="unsat" for row in data["queries"])
    review=(base/"S6_round28_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==40
    result={"status":"round28 exact entry passed",
        "scope":["Near RIGHT negative C excluded for every F horizontal type and LEFT status",
                 "Combined rounds26-28 exclude the entire near G2 family",
                 "Original far free TR square cannot contain RIGHTmid"],
        "totals":data["totals"],"geometric_review_items":40,
        "historical_round27":{"sha256":sha(old),"crc":"passed","own_full_entry_replayed":False},
        "research_diagnostics_replayed":False,
        "not_proved":"Far TOP positive C and far non-TOP residuals; entire G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03",
        "not_used":"round13 266-coefficient adjacent-corner certificate in new chains; "
                   "layout optimization; fixed-point coverage search; angle samples; interval tree"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
