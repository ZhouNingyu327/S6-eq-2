"""Local scalar endpoint lemma, not a six-square layout search.

Right-side TOP/BOTTOM hosts, F vertical empty, both left corners avoid L.
Candidate bounds come from original corner traces joining actual endpoints.
All reported SAT models are relaxations, not covering configurations.
"""
from pathlib import Path
import json
import time
import sympy as sp
import z3

HERE = Path(__file__).resolve().parent
results = []
for bottom_bridge, top_bridge in [(False, False), (False, True),
                                  (True, False), (True, True)]:
    h, u, d, r = z3.Reals("h u d r")
    g = lambda t: (1-t)/(1+t)
    q = lambda t: t/(2-t)
    G = g(h)
    k = 2*h/(1-h*h)
    m2 = 1-h+u-q(d) if bottom_bridge else 1-d
    m3 = 1-G+d-q(u) if top_bridge else 1-u
    T = g(m2)+g(m3)
    sol = z3.SolverFor("QF_NRA")
    sol.set(timeout=25000)
    sol.add(h>0, h*h+2*h<=1, u>=0, u<=h, d>=0, d<=G,
            r>=0, r<=k*u, k*r<=d, m2>0, m3>0,
            T>=(1-r)**2, T>=z3.RealVal("4/7"))
    started = time.time()
    answer = sol.check()
    record = {"bottom_bridge":bottom_bridge, "top_bridge":top_bridge,
              "result":str(answer), "seconds":time.time()-started,
              "right_chord_relaxation":"RF <= 10/7; weaker than RF <= sqrt(2)",
              "scope":"Local scalar necessary conditions, not layout search"}
    if answer == z3.sat:
        record["relaxed_model"] = {
            str(v):str(sol.model().eval(v, model_completion=True))
            for v in (h,u,d,r,m2,m3,T)}
    if answer == z3.unknown:
        record["reason_unknown"] = sol.reason_unknown()
    results.append(record)
    (HERE/"round24_g3_bridge_exploration.json").write_text(
        json.dumps(results, ensure_ascii=False, indent=2),encoding="utf-8")
    print(json.dumps(record,ensure_ascii=False), flush=True)
