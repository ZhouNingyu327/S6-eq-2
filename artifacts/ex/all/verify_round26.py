"""Recheck round26 local proof from a flat, hash-checked release."""
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
    old=base/"S6_round25_verification.zip"
    assert sha(old)=="9cfdc699ff61c590869ff7ba4703b1a07e2e43291a1e5e17e74b4f90104e9f5e"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
    name="check_round26_g2_top.py"
    process=subprocess.run([sys.executable,str(base/name)],cwd=base,
        capture_output=True,text=True,encoding="utf-8",errors="replace",
        env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
    assert process.returncode==0,(process.stdout,process.stderr)
    data=json.loads((base/"round26_g2_top_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":34,"NRA":32,"LRA":2,"symbolic_identities":21,"constants":25}
    assert all(row["result"]=="unsat" for row in data["queries"])
    review=(base/"S6_round26_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==42
    result={
        "status":"round26 exact entry passed",
        "scope":"G2 near C-TOP gap / empty F horizontal residual excluded; together "
                "with round19, entire near C-TOP gap representative excluded for every mu>1",
        "totals":data["totals"],"geometric_review_items":42,
        "historical_round25":{"sha256":sha(old),"crc":"passed",
                              "own_full_entry_replayed":False},
        "research_diagnostics_replayed":False,
        "not_proved":"G2 near C-RIGHT gap and far G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03",
        "not_used_in_new_chain":"round13 adjacent-corner 266-coefficient certificate; "
            "layout optimization; target-point coverage search; angle samples; interval tree",
    }
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
