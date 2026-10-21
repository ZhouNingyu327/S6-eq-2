"""Flat independent entry for the entire G3 exclusion, with explicit inputs."""
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
    for name,digest in manifest["files"].items():
        assert sha(base/name)==digest,name
    old=base/"S6_round24_addendum_verification.zip"
    assert sha(old)=="b611534e902255656ec05ccf994a4ec01f594999eb73834bffd1ad6642eda98b"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        for name in ["check_round24_g3_fside.py","check_round24_g3_cside.py",
                     "S6_attack_round24.md","S6_attack_round24_addendum.md"]:
            assert archive.read(name)==(base/name).read_bytes(),name
    scripts=["check_round24_g3_fside.py","check_round24_g3_cside.py",
             "check_round25_g3_complete.py"]
    for name in scripts:
        process=subprocess.run([sys.executable,str(base/name)],cwd=base,
            capture_output=True,text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (base/(name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
        assert process.returncode==0,(name,process.stdout,process.stderr)
    data=[json.loads((base/name).read_text(encoding="utf-8")) for name in [
        "round24_g3_fside_checks.json","round24_g3_cside_checks.json",
        "round25_g3_complete_checks.json"]]
    totals={key:sum(item["totals"][key] for item in data)
            for key in data[-1]["totals"]}
    assert data[-1]["totals"]=={"UNSAT":33,"NRA":28,"LRA":5,
                               "symbolic_identities":13,"constants":18}
    assert totals=={"UNSAT":76,"NRA":63,"LRA":13,"symbolic_identities":49,"constants":33}
    assert all(row["result"]=="unsat" for item in data for row in item["queries"])
    result={
        "status":"round25 exact entry passed",
        "scope":"Entire G3 excluded for every mu>1; all three midpoint-host "
                "representatives and empty/nonempty F vertical traces",
        "totals":totals,"new_checks":data[-1]["totals"],
        "geometric_review_items":43,
        "geometric_review":"Separate actual endpoint/nonempty/host/closedness audit, not solver queries",
        "historical_round24_addendum":{
            "sha256":sha(old),"crc":"passed","own_full_entry_replayed":False,
            "explicit_small_scripts_replayed":scripts[:2],
            "diagnostics_and_timeouts_replayed":False},
        "not_proved":"Remaining near and far G2; S(6)=2",
        "global_bound":"2 <= S(6) < 2.03",
        "not_used":"Whole-layout optimization, fixed target-point search, angle samples, "
                   "interval tree, or round13 adjacent-corner certificate in the new G3 chain"}
    (base/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
