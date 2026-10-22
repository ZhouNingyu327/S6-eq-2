"""Small exact checks for continuation lemmas; outside the frozen packets."""
from pathlib import Path
import json
import sympy as sp
import z3

mu,B,ell,v,S1,S4,U1,U4,J=z3.Reals("n_mu n_B n_ell n_v n_S1 n_S4 n_U1 n_U4 n_J")
solver=z3.SolverFor("QF_LRA")
solver.add(mu>1,B<1,J<1,ell>=2*mu-S1-S4,
    v>=2*mu-U1-U4-J,ell+v<=B,S1+U1<=B,S4+U4<=B)
answer=solver.check()
assert answer==z3.unsat
C,S,BE,M=sp.symbols("c s beta mu",positive=True)
AA=BE/S
DD=(1-BE)/C
K=(C+S-M)/(C*S)
lowY=(S*M-BE)/C
highY=(1-C*M)/S
lowX=(C*M-1+BE)/S
highX=(1-S*M)/C
circle_residual=M*(1-C*C-S*S)/(C*S)
assert sp.cancel(highY-lowY-(K-DD)-circle_residual)==0
assert sp.cancel(highX-lowX-(K-AA)-circle_residual)==0
assert sp.cancel(C*DD+S*AA-1)==0
assert sp.cancel(lowX-C*(M-DD)/S)==0
result={"status":"all exact checks passed",
    "new_queries":[{"name":"G3 F right BR duplicate, top TL/bottom BL: empty F vertical impossible",
        "theory":"QF_LRA","result":str(answer)}],
    "symbolic_identities":4,
    "symbolic_circle_condition":"Two trace identities have residual mu*(1-c^2-s^2)/(cs), zero on the unit circle.",
    "geometric_premises":"See S6_round21_continuation_notes.md; free-corner formulas require the stated canonical form and no midpoint.",
    "archive_status":"not included in frozen round21 main or addendum packets",
    "not_proved":"other G3 host patterns; entire remaining G4/G2/G3; S(6)=2"}
Path(__file__).with_name("round21_continuation_lemma_checks.json").write_text(
    json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
print(json.dumps(result,ensure_ascii=False,indent=2))
