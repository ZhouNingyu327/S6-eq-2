"""Standalone combined round35/36 verification; historical entries not replayed."""
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
    old=base/"S6_round34_verification.zip"
    assert sha(old)=="4c4ce7e30446f2f9dbb9a614471ed5cf63cf54605e3772df57c4091e518ee286"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round32.md","S6_attack_round33.md","S6_attack_round34.md"]:
            assert archive.read(name)==(base/name).read_bytes(),name
    def run(script):
        proc=subprocess.run([sys.executable,str(base/script)],cwd=base,
            capture_output=True,text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
        assert proc.returncode==0,(proc.stdout,proc.stderr)
    run("check_round35_positive_H.py")
    p35=json.loads((base/"round35_positive_H_checks.json").read_text(encoding="utf-8"))
    assert p35["totals"]=={"UNSAT":20,"NRA":19,"LRA":1,"symbolic_identities":7,"constants":9}
    run("check_round36_nonempty_closed.py")
    p36=json.loads((base/"round36_nonempty_closed_checks.json").read_text(encoding="utf-8"))
    assert p36["totals"]=={"UNSAT":19,"NRA":18,"LRA":1,"symbolic_identities":13,"constants":7}
    assert all(t["result"]=="unsat" for data in [p35,p36] for t in data["queries"])
    for n,count in [(35,26),(36,36)]:
        text=(base/f"S6_round{n}_geometric_review.md").read_text(encoding="utf-8")
        assert len(re.findall(r"^\d+\.",text,re.M))==count
    totals={key:p35["totals"][key]+p36["totals"][key] for key in p35["totals"]}
    result={"status":"round36 standalone combined entry passed",
        "scope":p36["scope"],"also_proved":p36["also_proved"],
        "explicit_round35_replay":p35["totals"],"round36_new":p36["totals"],
        "totals":totals,"geometric_review_items":{"round35":26,"round36":36},
        "historical_round34":{"sha256":sha(old),"crc":"passed","cited_source_bytes":"matched",
                             "own_full_entry_replayed":False},
        "round37_UNKNOWN_probes_replayed_or_counted":False,
        "not_proved":p36["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=True,indent=2))


if __name__=="__main__":
    main()
