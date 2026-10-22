"""Replay new scalar checks and verify immutable historical packets."""
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys
import time
import zipfile
import sympy
import z3


def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/"manifest.json").read_text(encoding="utf-8"))
    for name,expected in manifest["files"].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
    start=time.perf_counter()
    script=root/"check_round21_joint_chords.py"
    process=subprocess.run([sys.executable,str(script)],cwd=root,capture_output=True,
        text=True,encoding="utf-8",errors="replace")
    (root/(script.name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
    assert process.returncode==0,(process.stdout,process.stderr)
    checks=json.loads((root/"round21_joint_chord_checks.json").read_text(encoding="utf-8"))
    assert checks["status"]=="all exact checks passed" and checks["query_count"]==26
    assert checks["NRA_queries"]==15 and checks["LRA_queries"]==11
    assert checks["symbolic_checks"]==4 and len(checks["constant_checks"])==8
    assert checks["four_midpoint_corner_matchings"]==[[1,2,3,4],[2,3,4,1]]
    old={
        "S6_round20_verification.zip":
            "fbf00fcc7588a922df043a2564fa43d1bd8783303045da28123baaaacab29689",
        "S6_round20_addendum_verification.zip":
            "4ad142c6435d78c9135ce4f446f976d54279c03894dfb59d959fff4ce126d6b2"}
    historical={}
    for name,expected in old.items():
        packet=root/name
        with zipfile.ZipFile(packet) as archive:
            assert archive.testzip() is None,name
        digest=hashlib.sha256(packet.read_bytes()).hexdigest()
        assert digest==expected,name
        historical[name]={"sha256":digest,"archive_integrity":"passed","own_entry_replayed":False}
    with zipfile.ZipFile(root/"S6_round20_addendum_verification.zip") as archive:
        assert archive.read("S6_round20_verification.zip")==(
            root/"S6_round20_verification.zip").read_bytes()
    result={"status":"all exact checks passed","scope":checks["new_scope"],
        "new_queries":26,"NRA_queries":15,"LRA_queries":11,
        "symbolic_checks":4,"constant_checks":8,"corner_midpoint_matchings":2,
        "proof_method":checks["proof_method"],
        "historical_packets":historical,
        "T8_new_proof_uses_round13_pair_certificate":False,
        "geometric_premises":"Read S6_round21_geometric_review.md; UNSAT does not replace geometric ownership.",
        "not_proved":checks["not_proved"],"global_bound":"2 <= S(6) <2.03",
        "python":platform.python_version(),"sympy":sympy.__version__,"z3":z3.get_version_string(),
        "seconds":time.perf_counter()-start}
    (root/"verification_result.json").write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)


if __name__=="__main__":
    main()
