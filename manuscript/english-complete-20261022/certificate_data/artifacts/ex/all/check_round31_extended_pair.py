"""Independent reconstruction of the extended local pair certificate.

No generator import, no subdivision and no cover optimization.
"""
from pathlib import Path
import json
import sympy as sp


def certificate():
    x,y,u,v=sp.symbols("x y u v")
    k=lambda a:2*a/(1-a*a)
    b=lambda a:(1+a*a)/(1-a*a)
    F=(1-k(x)*k(y))+b(x)-2*k(x)+k(x)*b(y)+x+2*y-y*y
    P=sp.Poly(sp.cancel((2-F)*(1-x*x)*(1-y*y)),x,y)
    Q=sp.Poly((1-x*x)*(1-y*y)-4*x*y,x,y)
    saved=json.loads(Path(__file__).with_name(
        "round31_extended_pair_certificate.json").read_text(encoding="utf-8"))
    expected=[]
    for label,xx,Y in [
        ("c",sp.Rational(2,5)*u,sp.Rational(11,10)*x*x/(1-2*x*x)),
        ("s",sp.Rational(2,5)+sp.Rational(3,5)*u,
         sp.Rational(11,10)*(1-x)**2/(6*x-1-x*x))]:
        for polynomial,source in [("objective",P),("coefficient",Q)]:
            expected.append((label,xx,Y,polynomial,source))
    assert len(saved)==len(expected)==4
    rows=[]
    for row,(label,xx,Y,kind,poly) in zip(saved,expected):
        assert row["domain"]==label and row["polynomial"]==kind
        denominator=sp.denom(Y)
        transformed=sp.Poly(sp.expand(sp.cancel(poly.as_expr().subs(y,Y*v)*
            denominator**poly.degree(y)).subs(x,xx)),u,v)
        coeff=[[sp.Rational(a) for a in r] for r in row["coefficients"]]
        nx,ny=transformed.degree_list()
        assert row["degrees"]==[nx,ny]
        assert len(coeff)==nx+1 and all(len(r)==ny+1 for r in coeff)
        assert all(a>=0 for r in coeff for a in r)
        reconstructed=sum(a*sp.binomial(nx,i)*u**i*(1-u)**(nx-i)*
            sp.binomial(ny,j)*v**j*(1-v)**(ny-j)
            for i,r in enumerate(coeff) for j,a in enumerate(r))
        assert sp.Poly(sp.expand(transformed.as_expr()-reconstructed),u,v).is_zero
        rows.append({"domain":label,"polynomial":kind,"degrees":[nx,ny],
            "coefficients":sum(len(r) for r in coeff),
            "minimum":str(min(a for r in coeff for a in r)),
            "whole_rectangle_verified":True})
    result={"parameter_rectangles":2,"polynomial_identities":4,
        "coefficients":sum(r["coefficients"] for r in rows),"records":rows,
        "scope":"D in [23/24,1], anchored RIGHT block, W angle y<=sqrt2-1; "
                "L+A>=2 implies D+S+x+2y-y²<=2",
        "not_used":"angle samples, interval subdivision, layout optimizer"}
    assert result["coefficients"]==162
    Path(__file__).with_name("round31_extended_pair_checks.json").write_text(
        json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
    return result


if __name__=="__main__":
    print(json.dumps(certificate(),ensure_ascii=True,indent=2))
