"""Standalone round32/33 entry. Historical round31 is checked, not replayed."""
from pathlib import Path
from io import BytesIO
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
    old=base/"S6_round31_verification.zip"
    assert sha(old)=="c169325104276908c529b8f897dd95befbff00e802a693ee41f23685277052a0"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round31.md","S6_attack_round30.md","S6_attack_round3.md"]:
            assert archive.read(name)==(base/name).read_bytes(),name
        previous=archive.read("S6_round30_verification.zip")
        assert hashlib.sha256(previous).hexdigest()==\
            "933414f95a5623ec4fe86cc5798ca994022000a404ab68538dc824c3b1479e7b"
        with zipfile.ZipFile(BytesIO(previous)) as inner:
            assert inner.testzip() is None
            assert inner.read("S6_attack_round28.md")==(base/"S6_attack_round28.md").read_bytes()
    def run(script):
        proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
            capture_output=True,text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
        assert proc.returncode==0,(proc.stdout,proc.stderr)
    run("check_round32_right_positive.py")
    positive=json.loads((base/"round32_right_positive_checks.json").read_text(encoding="utf-8"))
    assert positive["totals"]=={"UNSAT":28,"NRA":25,"LRA":3,"symbolic_identities":6,"constants":5}
    run("check_round33_right_nonempty.py")
    whole=json.loads((base/"round33_right_nonempty_checks.json").read_text(encoding="utf-8"))
    assert whole["totals"]=={"UNSAT":26,"NRA":25,"LRA":1,"symbolic_identities":12,"constants":11}
    for data in [positive,whole]:
        assert all(row["result"]=="unsat" for row in data["queries"])
    for n,count in [(32,34),(33,32)]:
        review=(base/f"S6_round{n}_geometric_review.md").read_text(encoding="utf-8")
        assert len(re.findall(r"^\d+\.",review,re.M))==count
    totals={key:positive["totals"][key]+whole["totals"][key] for key in positive["totals"]}
    result={"status":"round33 standalone entry passed",
        "scope":"Entire far RIGHT real gap with nonempty F horizontal excluded, including tangency",
        "explicit_round32_replay":positive["totals"],"round33_new":whole["totals"],
        "totals":totals,"geometric_review_items":{"round32":34,"round33":32},
        "historical_round31":{"sha256":sha(old),"crc":"passed","own_full_entry_replayed":False},
        "historical_round30_inside31":{"sha256":hashlib.sha256(previous).hexdigest(),
            "crc":"passed","round28_Phi_source_bytes":"matched","own_full_entry_replayed":False},
        "historical_coefficient_certificates_replayed":False,
        "malformed_query_or_earlier_exploration_counted":False,
        "not_proved":"LEFT with nonempty F H; LEFT/RIGHT/three meetings with empty F H; entire G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=True,indent=2))


if __name__=="__main__":
    main()
