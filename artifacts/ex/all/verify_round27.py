"""Flat exact entry for the two round27 G2 branch exclusions."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import zipfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    base=Path(__file__).resolve().parent
    manifest=json.loads((base/"manifest.json").read_text(encoding="utf-8"))
    for name,digest in manifest["files"].items():
        assert sha(base/name)==digest,name
    old=base/"S6_round26_verification.zip"
    assert sha(old)=="7c5f942d564c1e569f2f180b33bc05a4a5756d870986cc06189c50d52ce9c25a"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        assert archive.read("S6_attack_round26.md")==(base/"S6_attack_round26.md").read_bytes()
    script="check_round27_g2_two_branches.py"
    proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
        capture_output=True,text=True,encoding="utf-8",errors="replace",
        env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
    assert proc.returncode==0,(proc.stdout,proc.stderr)
    data=json.loads((base/"round27_g2_two_branch_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":38,"NRA":36,"LRA":2,"symbolic_identities":13,"constants":24}
    assert all(row["result"]=="unsat" for row in data["queries"])
    review=(base/"S6_round27_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==40
    result={"status":"round27 exact entry passed",
        "scope":["Near RIGHT real gap with positive C: every F horizontal type and LEFT status excluded",
                 "Far TOP real gap with negative C: direct right join and original-corner bridge excluded",
                 "Exact actual endpoint min identities proved for both residual C rotations"],
        "totals":data["totals"],"geometric_review_items":40,
        "historical_round26":{"sha256":sha(old),"crc":"passed","own_full_entry_replayed":False},
        "research_diagnostics_replayed":False,
        "not_proved":"Near RIGHT negative C; far TOP positive C; far non-TOP residuals; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03",
        "not_used":"round13 adjacent-corner 266-coefficient certificate in the new chains; "
                   "layout optimization; target-point search; angle samples; interval tree"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
