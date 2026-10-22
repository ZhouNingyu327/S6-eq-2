"""Replay the entire hand G4 chain's small checks; separate relaxed diagnostics."""
from pathlib import Path
import hashlib
import io
import json
import os
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
        ("check_round20_g4_duplicate.py","round20_g4_duplicate_checks.json",10,8,2,3,5),
        ("check_round21_joint_chords.py","round21_joint_chord_checks.json",26,15,11,4,8),
        ("check_round21_floating_lower.py","round21_floating_lower_checks.json",11,9,2,2,4),
        ("check_round22_diagonal_bridge.py","round22_diagonal_bridge_checks.json",16,10,6,4,6),
        ("check_round22_same_side.py","round22_same_side_checks.json",29,24,5,6,10),
        ("check_round23_g4_residual.py","round23_g4_residual_checks.json",20,16,4,7,14)]
    replayed={}
    for script,result_file,count,nra,lra,symbolic,constants in specs:
        process=subprocess.run([sys.executable,str(root/script)],cwd=root,capture_output=True,
            text=True,encoding="utf-8",errors="replace",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (root/(script+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
        assert process.returncode==0,(script,process.stdout,process.stderr)
        checks=json.loads((root/result_file).read_text(encoding="utf-8"))
        symbols=checks.get("symbolic_identity_checks",checks.get("symbolic_checks"))
        assert checks["status"]=="all exact checks passed",script
        assert (checks["query_count"],checks["NRA_queries"],checks["LRA_queries"],
            symbols,len(checks["constant_checks"]))==(count,nra,lra,symbolic,constants),script
        assert all(row["result"]=="unsat" for row in checks["queries"]),script
        replayed[script]={"UNSAT_queries":count,"NRA":nra,"LRA":lra,
            "symbolic_checks":symbolic,"constant_checks":constants}
    diagnostic="review_round23_relaxed_queries.py"
    process=subprocess.run([sys.executable,str(root/diagnostic)],cwd=root,capture_output=True,
        text=True,encoding="utf-8",errors="replace",
        env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (root/(diagnostic+".log")).write_text(process.stdout+process.stderr,encoding="utf-8")
    assert process.returncode==0,(process.stdout,process.stderr)
    diagnosis=json.loads((root/"round23_relaxed_query_review.json").read_text(encoding="utf-8"))
    assert diagnosis["relaxed_SAT_checks"]==2
    assert diagnosis["pinned_models_with_restored_condition_UNSAT"]==2
    assert diagnosis["not_actual_six_square_coverings"] is True
    prior=root/"S6_round22_verification.zip"
    assert hashlib.sha256(prior.read_bytes()).hexdigest()==(
        "8fa101a3315608bdf17c4d41c9abbbb62d1b686859e325ff4b5570222a833cd1")
    with zipfile.ZipFile(prior) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round22.md","S6_round22_geometric_review.md","S6_attack_round22_working.md"]:
            assert archive.read(name)==(root/name).read_bytes(),name
        addendum_bytes=archive.read("S6_round21_addendum_verification.zip")
    assert hashlib.sha256(addendum_bytes).hexdigest()==(
        "1208d7992f69a1902d60f55703e76466b2e7fd6d20392c7d26f56a9d28408ab8")
    with zipfile.ZipFile(io.BytesIO(addendum_bytes)) as archive:
        assert archive.testzip() is None
        main_bytes=archive.read("S6_round21_verification.zip")
    assert hashlib.sha256(main_bytes).hexdigest()==(
        "b0d85d27183256e2f978c3fbc970a529701331e32c637be43310934600126581")
    with zipfile.ZipFile(io.BytesIO(main_bytes)) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round21.md","S6_round21_geometric_review.md","S6_attack_round20_addendum.md"]:
            assert archive.read(name)==(root/name).read_bytes(),name
        early_bytes=archive.read("S6_round20_addendum_verification.zip")
    assert hashlib.sha256(early_bytes).hexdigest()==(
        "4ad142c6435d78c9135ce4f446f976d54279c03894dfb59d959fff4ce126d6b2")
    with zipfile.ZipFile(io.BytesIO(early_bytes)) as archive:
        assert archive.testzip() is None
        assert archive.read("check_round20_g4_duplicate.py")==(root/"check_round20_g4_duplicate.py").read_bytes()
    totals={key:sum(row[key] for row in replayed.values()) for key in
        ["UNSAT_queries","NRA","LRA","symbolic_checks","constant_checks"]}
    assert totals=={"UNSAT_queries":112,"NRA":82,"LRA":30,"symbolic_checks":26,"constant_checks":47}
    result={"status":"all exact checks passed","scope":"Entire G4 excluded for every a>2, with all midpoint duplicates and horizontal trace types.",
        "replayed_scripts":replayed,"totals":totals,
        "relaxed_diagnostics":{"SAT_queries":2,"restored_conditions_reject_pinned_models":2,
            "included_in_formal_UNSAT_total":False},
        "proof_method":"hand continuous geometry: actual endpoints, nonempty parallel traces, support projections and half-angle feedback",
        "round13_pair_certificate_used_by_G4_chain":False,
        "second_round_2_03_point_search_replayed":False,
        "historical_round22":{"sha256":hashlib.sha256(prior.read_bytes()).hexdigest(),
            "archive_integrity":"passed","own_complete_entry_replayed":False,
            "explicit_G4_scripts_replayed":True},
        "round22_addendum_first_frozen_here":True,
        "geometric_premises":"See S6_round23_geometric_review.md; exact scalar checks do not prove endpoint ownership.",
        "not_proved":"Remaining G2/G3; S(6)=2","global_bound":"2 <= S(6) <2.03",
        "python":platform.python_version(),"sympy":sympy.__version__,"z3":z3.get_version_string(),
        "seconds":time.perf_counter()-start}
    (root/"verification_result.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2),flush=True)


if __name__=="__main__":
    main()
