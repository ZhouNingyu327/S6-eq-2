"""Exact length consequence in the residual far-W representative."""
from pathlib import Path
import json
import z3


def C_not_left():
    mu,B,S1,S2,U1,g,h=z3.Reals('mu B S1 S2 U1 g h')
    sol=z3.SolverFor('QF_LRA')
    sol.add(mu>1,B<1,S1>=0,S2>=0,U1>=0,S1+U1<=B,S2<=B,
            g==2*mu-S1-S2,h>=mu-U1,g+h<=B)
    res=sol.check();assert res==z3.unsat,res
    return {'scope':'far W, F avoids bottom: C cannot contain left critical tip; full cover forces it into F',
            'result':str(res),'arithmetic':'exact linear reals'}


if __name__=='__main__':
    records=[C_not_left()]
    for record in records:print('PASS',record,flush=True)
    Path(__file__).with_name('round4_far_checks.json').write_text(json.dumps(records,indent=2))
