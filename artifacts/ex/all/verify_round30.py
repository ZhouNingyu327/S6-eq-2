"""Standalone corrected local geometry entry; no entire G2 family claimed."""
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
    old=base/"S6_round29_verification.zip"
    assert sha(old)=="311fe3e300860fbd3deb8bac8a7949f8312179840cfa3970883d53d6b8dfbca2"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        assert archive.read("S6_attack_round29.md")==(base/"S6_attack_round29.md").read_bytes()
        assert archive.read("S6_attack_round28.md")==(base/"S6_attack_round28.md").read_bytes()
        assert hashlib.sha256(archive.read("S6_round28_verification.zip")).hexdigest()==\
            "3ad18733f9d6c11d8fee7c46a8558c5d2b27485729e345696b66c18c8ab207f0"
    expected=[
        ("check_round30_corrected_geometry.py","round30_corrected_geometry_checks.json",
         {"UNSAT":21,"NRA":15,"LRA":6,"symbolic_identities":5,"constants":11}),
        ("check_round29_no_top_structure.py","round29_no_top_structure_checks.json",
         {"UNSAT":9,"NRA":6,"LRA":3,"identities":2})]
    details=[]
    for script,result_name,totals in expected:
        proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
            capture_output=True,text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
        assert proc.returncode==0,(proc.stdout,proc.stderr)
        data=json.loads((base/result_name).read_text(encoding="utf-8"))
        assert data["totals"]==totals,(script,data["totals"])
        assert all(row["result"]=="unsat" for row in data["queries"])
        details.append({"script":script,"totals":totals})
    review=(base/"S6_round30_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==34
    report=(base/"S6_attack_round30.md").read_text(encoding="utf-8")
    assert "本轮没有排除整个远端三相接" in report
    assert "RIGHT相接才给J<δ(x)" in report
    result={"status":"round30 corrected exact entry passed",
        "scope":["Corrected TOP/H and RIGHT/V pair directions; false cap has an exact local counterexample",
                 "Nonempty-F side contacts imply hC-d>mu and u<1/2",
                 "Nonempty-F three meetings imply z<1/7, 9J²>z, u>41/70 and C avoiding all external sides"],
        "checks":details,
        "totals":{"UNSAT":30,"NRA":21,"LRA":9,"symbolic_identities":7,"constants":11},
        "geometric_review_items":34,
        "historical_round29":{"sha256":sha(old),"crc":"passed",
            "round28_round29_main_report_bytes":"unchanged","own_full_entry_replayed":False},
        "withdrawn_candidate_checks_replayed":False,
        "withdrawn_candidate_checks_counted_as_proof":False,
        "historical_round13_adjacent_lemma":"266-coefficient certificate assumed, not replayed",
        "not_proved":"Entire LEFT-gap, RIGHT-gap, three-meeting families; entire G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
