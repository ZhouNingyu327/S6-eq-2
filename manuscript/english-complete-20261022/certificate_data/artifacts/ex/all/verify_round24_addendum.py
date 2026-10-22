"""Flat packet entry: explicit two small scripts, not the historical full entry."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import zipfile


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    base=Path(__file__).resolve().parent
    manifest=json.loads((base/"manifest.json").read_text(encoding="utf-8"))
    for name,expected in manifest["files"].items():
        assert sha(base/name)==expected,name
    old=base/"S6_round24_verification.zip"
    assert sha(old)=="120231314e44fc70ae717a359ea4908f3714db557a04671cbe01f2bee0663932"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        assert archive.read("check_round24_g3_fside.py")==(
            base/"check_round24_g3_fside.py").read_bytes()
        assert archive.read("S6_attack_round24.md")==(
            base/"S6_attack_round24.md").read_bytes()
    scripts=["check_round24_g3_fside.py","check_round24_g3_cside.py"]
    for name in scripts:
        process=subprocess.run([sys.executable,str(base/name)],cwd=base,
            capture_output=True,text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (base/(name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
        assert process.returncode==0,(name,process.stdout,process.stderr)
    main_checks=json.loads((base/"round24_g3_fside_checks.json").read_text(encoding="utf-8"))
    new_checks=json.loads((base/"round24_g3_cside_checks.json").read_text(encoding="utf-8"))
    assert new_checks["totals"]=={"UNSAT":11,"NRA":6,"LRA":5,
                                  "symbolic_identities":6,"constants":0}
    totals={key:main_checks["totals"][key]+new_checks["totals"][key]
            for key in new_checks["totals"]}
    assert totals=={"UNSAT":43,"NRA":35,"LRA":8,"symbolic_identities":36,"constants":15}
    result={"status":"round24 addendum exact entry passed",
            "scope":"C-side G3 F vertical empty excluded; nonempty F forces TOP gap, "
                    "RIGHT meeting and duplicate R host after reflection",
            "totals":totals,"new_checks":new_checks["totals"],
            "geometric_review_items":21,
            "conditional_side_bound":"a <= (5*sqrt(26)-sqrt(2))/12 for remaining C-side G3 only",
            "historical_round24":{"sha256":sha(old),"crc":"passed",
                                  "own_full_entry_replayed":False,
                                  "explicit_small_script_replayed":True,
                                  "diagnostics_and_timeouts_replayed":False},
            "not_proved":"Remaining nonempty C-side G3; diagonal G3; G2; S(6)=2",
            "global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
