"""Replay the new endpoint proof and the explicitly listed small input lemmas."""
from pathlib import Path
import hashlib
import io
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
    specs=[
        ("check_round22_diagonal_bridge.py","round22_diagonal_bridge_checks.json"),
        ("check_round21_floating_lower.py","round21_floating_lower_checks.json"),
        ("check_round21_continuation_lemmas.py","round21_continuation_lemma_checks.json")]
    results=[]
    for script_name,result_name in specs:
        process=subprocess.run([sys.executable,str(root/script_name)],cwd=root,
            capture_output=True,text=True,encoding="utf-8",errors="replace")
        (root/(script_name+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
        assert process.returncode==0,(script_name,process.stdout,process.stderr)
        checks=json.loads((root/result_name).read_text(encoding="utf-8"))
        assert checks["status"]=="all exact checks passed",script_name
        results.append(checks)
    new,prior,g3=results
    assert (new["query_count"],new["NRA_queries"],new["LRA_queries"],
        new["symbolic_identity_checks"],len(new["constant_checks"]))==(16,10,6,4,6)
    assert (prior["query_count"],prior["NRA_queries"],prior["LRA_queries"],
        prior["symbolic_identity_checks"],len(prior["constant_checks"]))==(11,9,2,2,4)
    assert len(g3["new_queries"])==1 and g3["new_queries"][0]["result"]=="unsat"
    assert g3["symbolic_identities"]==4
    historical=root/"S6_round21_addendum_verification.zip"
    historical_sha=hashlib.sha256(historical.read_bytes()).hexdigest()
    assert historical_sha=="1208d7992f69a1902d60f55703e76466b2e7fd6d20392c7d26f56a9d28408ab8"
    with zipfile.ZipFile(historical) as archive:
        assert archive.testzip() is None
        main_bytes=archive.read("S6_round21_verification.zip")
        for name in ["check_round21_floating_lower.py","S6_attack_round21_addendum.md"]:
            assert archive.read(name)==(root/name).read_bytes(),name
    main_sha=hashlib.sha256(main_bytes).hexdigest()
    assert main_sha=="b0d85d27183256e2f978c3fbc970a529701331e32c637be43310934600126581"
    with zipfile.ZipFile(io.BytesIO(main_bytes)) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round21.md","S6_round21_geometric_review.md"]:
            assert archive.read(name)==(root/name).read_bytes(),name
    result={"status":"all exact checks passed","scope":new["scope"],
        "new_queries":16,"recomputed_J_lower_queries":11,
        "recomputed_G3_continuation_queries":1,"total_recomputed_queries":28,
        "NRA_queries":19,"LRA_queries":9,"symbolic_identity_checks":10,"constant_checks":10,
        "new_core_round13_pair_certificate_needed":False,
        "free_corner_standardization_needed":False,
        "geometric_review":"S6_round22_geometric_review.md; solver queries do not establish endpoint ownership.",
        "proof_method":new["proof_method"],
        "historical_packets":{
            "S6_round21_addendum_verification.zip":{"sha256":historical_sha,"archive_integrity":"passed",
                "own_entry_replayed":False,"J_lower_script_replayed":True},
            "nested S6_round21_verification.zip":{"sha256":main_sha,"archive_integrity":"passed",
                "own_entry_replayed":False}},
        "G3_previous_unfrozen_lemmas_first_included_here":True,
        "G4_remaining":"same-side top TR/right BR, corner BL may repeat left or bottom midpoint or neither",
        "not_proved":new["not_proved"],"global_bound":"2 <= S(6) <2.03",
        "python":platform.python_version(),"sympy":sympy.__version__,"z3":z3.get_version_string(),
        "seconds":time.perf_counter()-start}
    (root/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)


if __name__=="__main__":
    main()
