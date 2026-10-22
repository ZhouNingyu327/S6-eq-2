"""Independent round40 entry; no implicit replay of old mathematics."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,zipfile

def sha(data):return hashlib.sha256(data).hexdigest()
def main():
    cwd=Path.cwd();src=Path(__file__).resolve().parent
    out=cwd/"outputs" if (cwd/"outputs").is_dir() else cwd
    manifest=cwd/"manifest.json"
    if manifest.exists():
        for name,digest in json.loads(manifest.read_text(encoding="utf-8"))["files"].items():
            assert sha((cwd/name).read_bytes())==digest,name
    old=out/"S6_round39_verification.zip"
    digest="51d380cf4efd52f2295366df97dd1afba46eca5ba098d2459caf55ba52119a17"
    assert sha(old.read_bytes())==digest
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        assert archive.read("S6_attack_round39.md")==(out/"S6_attack_round39.md").read_bytes()
        for name,h in json.loads(archive.read("manifest.json"))["files"].items():
            assert sha(archive.read(name))==h,name
    for name in ("verify_round40_seam.py","verify_round40_grid_counterexample.py"):
        proc=subprocess.run([sys.executable,str(src/name)],cwd=cwd,
            capture_output=True,text=True,encoding="utf-8",errors="strict",
            env={**os.environ,"PYTHONIOENCODING":"utf-8"})
        (out/(name+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
        assert proc.returncode==0,(name,proc.stdout,proc.stderr)
    seam=json.loads((out/"S6_round40_seam_verification.json").read_text(encoding="utf-8"))
    example=json.loads((out/"S6_round40_grid_counterexample_verification.json").read_text(encoding="utf-8"))
    assert seam["query_count"]==10 and all(x["result"]=="unsat" for x in seam["queries"])
    assert seam["identity_count"]==6 and seam["constant_count"]==3
    assert example["check_count"]==67
    report=(out/"S6_attack_round40.md").read_text(encoding="utf-8")
    review=(out/"S6_round40_geometric_review.md").read_text(encoding="utf-8")
    assert "整个 G2、S(6)=2 仍开放" in report
    assert "36. " in review
    result={
        "result":"passed",
        "scope":"Forced interior seam point; exact counterexample to sufficiency of the six-line grid",
        "totals":{"UNSAT":10,"NRA":10,"LRA":0,"symbolic_identities":6,
                  "constants":3,"exact_example_checks":67,"geometric_review_items":36},
        "historical_round39":{"sha256":digest,"crc":"passed","manifest":"passed",
                              "cited_source_bytes":"matched","own_full_entry_replayed":False},
        "not_proved":"Any complete new contact branch, the remaining three-meeting family, G2, or S(6)=2",
        "excluded_from_proof":"two UNKNOWN probes, invalid preliminary W, floating polygon area",
        "global_bound":"2 <= S(6) < 2.03",
    }
    (out/"S6_round40_verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
