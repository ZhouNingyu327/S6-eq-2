"""Replay two exact local diagnostics; neither is a covering configuration."""
from pathlib import Path
import json
import sympy as sp

HERE=Path(__file__).resolve().parent


def main():
    R=sp.Rational
    h=R(21,64)
    r=R(477,2048)
    w=R(351,2240)  # here w is u-d, NOT an anchored corner halfangle
    G=(1-h)/(1+h)
    k=2*h/(1-h*h)
    A=1-h+w
    B=1-G-w
    T=(1-A)/(1+A)+(1-B)/(1+B)
    assertions={
        "h in halfangle domain":0<h and h*h+2*h<=1,
        "r in relaxed projection cap":0<=r<=2*h*h/(1-h*h),
        "w in relaxed C range":r/k-G<=w<=h-k*r,
        "A B positive":A>0 and B>0,
        "length upper budget beats F squared lower":T>=(1-r)**2,
        "length upper budget beats F diameter lower":(2-T)**2<=2,
    }
    assert all(bool(v) for v in assertions.values())
    relaxed={
        "kind":"exact SAT witness for an incomplete scalar length relaxation",
        "h":str(h),"r":str(r),"u_minus_d":str(w),"S_upper":str(T),
        "checks":{name:bool(v) for name,v in assertions.items()},
        "missing":"actual floating corner segment must join C and anchored corner endpoints",
        "not_a_covering":True}

    mu=R(101,100)
    radius=sp.sqrt(2)/2
    C_right=radius-R(1,2)
    F_left=R(9,10)-radius
    left_chord=sp.sqrt(2)-R(51,50)
    central_chord=sp.sqrt(2)-1
    right_chord=sp.sqrt(2)-R(11,50)
    overlap=sp.sqrt(2)-R(7,5)
    grid=3*sp.sqrt(2)-R(11,50)
    checks={
        "C contains O":R(1,2)<=radius,
        "C contains L":mu-R(1,2)<=radius,
        "F contains R":mu-R(9,10)<=radius,
        "F avoids O and central vertical line":R(9,10)>radius,
        "both avoid top bottom":radius<mu,
        "C clipped horizontal reaches L":-R(1,2)-radius<=-mu,
        "F clipped horizontal reaches R":R(9,10)+radius>=mu,
        "horizontal intervals strictly overlap":C_right>F_left,
        "overlap formula":sp.simplify(C_right-F_left-overlap)==0,
        "joint grid formula":sp.simplify(
            2*mu+left_chord+central_chord+right_chord-grid)==0,
        "joint grid greater than four":grid>4,
        "not target covering":radius<mu,
    }
    assert all(bool(v) for v in checks.values())
    connected={
        "kind":"two-unit local counterexample to joint grid<=4 even with horizontal coverage",
        "mu":str(mu),
        "C":"abs(x+1/2)+abs(y)<=sqrt(2)/2",
        "F":"abs(x-9/10)+abs(y)<=sqrt(2)/2",
        "horizontal_overlap":str(overlap),
        "joint_grid":str(grid),
        "checks":{name:bool(v) for name,v in checks.items()},
        "not_a_covering":True,
        "why_not":"the two units miss every target corner and other required regions"}
    result={"status":"two exact diagnostics replayed",
            "incomplete_length_relaxation":relaxed,
            "connected_horizontal_local_counterexample":connected,
            "counts_excluded_from_formal_UNSAT":True}
    (HERE/"round24_diagnostic_review.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":
    main()
