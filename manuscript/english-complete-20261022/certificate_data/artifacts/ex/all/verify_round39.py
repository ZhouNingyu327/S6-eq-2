"""Standalone round39 exact checks; historical entries are not replayed."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,zipfile

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    base=Path(__file__).resolve().parent
    manifest=json.loads((base/"manifest.json").read_text(encoding="utf-8"))
    for name,digest in manifest["files"].items():
        assert sha(base/name)==digest,name
    old=base/"S6_round38_verification.zip"
    assert sha(old)=="9f0563c1f3b4b984ba123a0faaa7ecf746d75afaa4e69e893452cd6ccb3cdf13"
    with zipfile.ZipFile(old) as archive:
        assert archive.testzip() is None
        for name in ["S6_attack_round32.md","S6_attack_round37.md","S6_attack_round38.md"]:
            assert archive.read(name)==(base/name).read_bytes(),name
    script="check_round39_single_contact.py"
    proc=subprocess.run([sys.executable,str(base/script)],cwd=base,capture_output=True,
        text=True,encoding="utf-8",errors="replace",env={**os.environ,"PYTHONIOENCODING":"utf-8"})
    (base/(script+".log")).write_text(proc.stdout+proc.stderr,encoding="utf-8")
    assert proc.returncode==0,(proc.stdout,proc.stderr)
    data=json.loads((base/"round39_single_contact_checks.json").read_text(encoding="utf-8"))
    assert data["totals"]=={"UNSAT":29,"NRA":26,"LRA":3,"symbolic_identities":6,"constants":19}
    assert all(row["result"]=="unsat" for row in data["queries"])
    review=(base/"S6_round39_geometric_review.md").read_text(encoding="utf-8")
    assert len(re.findall(r"^\d+\.",review,re.M))==40
    result={"status":"round39 standalone exact entry passed","scope":data["scope"],
        "totals":data["totals"],"geometric_review_items":40,
        "historical_round38":{"sha256":sha(old),"crc":"passed","cited_source_bytes":"matched",
                              "own_full_entry_replayed":False},
        "preliminary_root_query_counted_twice":False,
        "not_proved":data["not_proved"],"global_bound":"2 <= S(6) < 2.03"}
    (base/"verification_result.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=True,indent=2))

if __name__=="__main__":
    main()
