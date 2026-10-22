"""Replay the new floating-length bound, preserving the round21 main release."""
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
    script=root/"check_round21_floating_lower.py"
    process=subprocess.run([sys.executable,str(script)],cwd=root,capture_output=True,
        text=True,encoding="utf-8",errors="replace")
    (root/(script.name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
    assert process.returncode==0,(process.stdout,process.stderr)
    checks=json.loads((root/"round21_floating_lower_checks.json").read_text(encoding="utf-8"))
    assert checks["status"]=="all exact checks passed" and checks["query_count"]==11
    assert checks["NRA_queries"]==9 and checks["LRA_queries"]==2
    assert checks["symbolic_identity_checks"]==2 and len(checks["constant_checks"])==4
    previous=root/"S6_round21_verification.zip"
    with zipfile.ZipFile(previous) as archive:
        assert archive.testzip() is None
    digest=hashlib.sha256(previous.read_bytes()).hexdigest()
    assert digest=="b0d85d27183256e2f978c3fbc970a529701331e32c637be43310934600126581"
    result={"status":"all exact checks passed","scope":checks["scope"],
        "new_queries":11,"NRA_queries":9,"LRA_queries":2,
        "symbolic_identity_checks":2,"constant_checks":4,
        "positive_margin":checks["positive_margin"],
        "proof_method":"hand real grid budgets, floating length cancellation and parabolic chord bound",
        "historical_main_packet":{"sha256":digest,"archive_integrity":"passed","own_entry_replayed":False},
        "round13_pair_certificate_needed_for_new_bound":False,
        "not_proved":checks["not_proved"],"global_bound":"2 <= S(6) <2.03",
        "python":platform.python_version(),"sympy":sympy.__version__,"z3":z3.get_version_string(),
        "seconds":time.perf_counter()-start}
    (root/"verification_result.json").write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)


if __name__=="__main__":
    main()
