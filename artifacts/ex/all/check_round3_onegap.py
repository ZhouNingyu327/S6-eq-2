"""Exact linear checks of necessary consequences for three corner meets.
Uses only proved star, coupled-chord, and diameter bounds as geometry input.
"""
from pathlib import Path
import json
import z3
from check_round3_linear import base


def onegap():
    sol,mu,B,L,S,U = base()
    for k in (1,2,3):
        sol.add(L[k]+S[(k+1)%4] >= 2*mu)
    return sol,mu,B,L,S,U


def main():
    records = []
    for k,label in [(2,'bottom-gap block cannot cover top critical tip'),(3,'bottom-gap block cannot cover left critical tip')]:
        sol,mu,B,L,S,U = onegap()
        sol.add((mu-S[1])+(mu-U[k]) <= 1)
        result = sol.check(); assert result == z3.unsat
        records.append({'scope':label,'result':str(result),'geometry_input':'distance forces sum of the indicated legs below 1'})
    sol,mu,B,L,S,U = onegap()
    D = z3.RealVal('10/7')
    sol.add(L[1] <= D,(mu-U[0])+(mu-U[2]) <= D)
    result = sol.check(); assert result == z3.unsat
    records.append({'scope':'top-tip block cannot also cover bottom critical tip','result':str(result),'diameter_upper':'10/7'})
    sol,mu,B,L,S,U = onegap()
    g,hC,hF = z3.Reals('g hC hF')
    sol.add(g > 0,g == 2*mu-L[0]-S[1],g+hC+hF <= 2*B,
            hC+hF+U[1]+U[3] >= 2*mu)
    result = sol.check(); assert result == z3.unsat
    records.append({'scope':'both centre blocks cannot touch the sole gapped outer edge','result':str(result)})
    for record in records:
        print('PASS',record,flush=True)
    Path(__file__).with_name('round3_onegap_checks.json').write_text(json.dumps(records,indent=2))


if __name__ == '__main__':
    main()
