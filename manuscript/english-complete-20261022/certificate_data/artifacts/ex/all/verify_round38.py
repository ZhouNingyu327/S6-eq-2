"""Standalone new checks and byte-integrity checks, without replaying old entries."""
from pathlib import Path
import hashlib,io,json,os,re,subprocess,sys,zipfile

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    base=Path(__file__).resolve().parent
    manifest=json.loads((base/"manifest.json").read_text(encoding="utf-8"))
    for name,digest in manifest["files"].items():
        assert sha(base/name)==digest,name
    old=base/"S6_round37_verification.zip"
    assert sha(old)=="3b940704c2566bcddfe6ab4093b3d5691d69107c2ddbe0e1ea27cc77e5c94fcf"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round32.md","S6_attack_round37.md"]:
            assert archive.read(name)==(base/name).read_bytes(),name
        nested=archive.read("S6_round36_verification.zip")
    assert hashlib.sha256(nested).hexdigest()=="cae171bb519027b2b69c4f05d8da92995c3f8eaff404ce05ef5be4d62dca574f"
    with zipfile.ZipFile(io.BytesIO(nested)) as archive:
        assert archive.testzip() is None
        assert archive.read("S6_attack_round33.md")==(base/"S6_attack_round33.md").read_bytes()
    script="check_round38_empty_right_negative.py"
    proc=subprocess.run([sys.executable,str(base/script)],cwd=base,capture_output=True,
        text=True,encoding="utf-8",errors="replace",env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
    assert proc.returncode==0,(proc.stdout,proc.stderr)
    data=json.loads((base/"round38_empty_right_negative_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":30,"NRA":26,"LRA":4,"symbolic_identities":6,"constants":11}
    assert all(row["result"]=="unsat" for row in data["queries"])
    review=(base/"S6_round38_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==38
    for name in ["round38_scalar_exploration.json","round38_linear_loss_exploration.json"]:
        assert json.loads((base/name).read_text(encoding="utf-8"))["result"]=="unknown"
    result={"status":"round38 standalone exact entry passed","scope":data["scope"],
        "also_proved":data["also_proved"],"totals":data["totals"],"geometric_review_items":38,
        "historical_round37":{"sha256":sha(old),"crc":"passed","cited_source_bytes":"matched",
                              "own_full_entry_replayed":False},
        "historical_round36":{"sha256":hashlib.sha256(nested).hexdigest(),
            "crc":"passed","cited_source_bytes":"matched","own_full_entry_replayed":False},
        "exploratory_UNKNOWN_replayed_or_counted":False,
        "withdrawn_round37_missing_one_candidate_counted":False,
        "not_proved":data["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=True,indent=2))

if __name__=="__main__":
    main()
