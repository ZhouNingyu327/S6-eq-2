"""Whole-rectangle rational coefficient test for one extended local pair lemma.

No subdivision or cover-layout search. Coefficients are exact rationals.
"""
from fractions import Fraction
from math import comb
import json
from pathlib import Path
import sympy as sp


def bernstein(poly):
    nx,ny=poly.degree_list()
    return [[sum(coef*sp.Rational(comb(i,p),comb(nx,p))*
                 sp.Rational(comb(j,q),comb(ny,q))
                 for (p,q),coef in poly.terms() if p<=i and q<=j)
             for j in range(ny+1)] for i in range(nx+1)]


def main():
    x,y,u,v=sp.symbols("x y u v")
    k=lambda t:2*t/(1-t*t)
    b=lambda t:(1+t*t)/(1-t*t)
    F=(1-k(x)*k(y))+b(x)-2*k(x)+k(x)*b(y)+x+2*y-y*y
    P=sp.Poly(sp.cancel((2-F)*(1-x*x)*(1-y*y)),x,y)
    Q=sp.Poly((1-x*x)*(1-y*y)-4*x*y,x,y)
    rows=[]
    for name,xx,Y in [
        ("c",sp.Rational(2,5)*u,sp.Rational(11,10)*x*x/(1-2*x*x)),
        ("s",sp.Rational(2,5)+sp.Rational(3,5)*u,
         sp.Rational(11,10)*(1-x)**2/(6*x-1-x*x))]:
        den=sp.denom(Y)
        for label,p in [("objective",P),("coefficient",Q)]:
            transformed=sp.Poly(sp.expand(sp.cancel(p.as_expr().subs(y,Y*v)*
                den**p.degree(y)).subs(x,xx)),u,v)
            coeff=bernstein(transformed)
            minimum=min(a for row in coeff for a in row)
            record={"domain":name,"polynomial":label,"degrees":list(transformed.degree_list()),
                    "minimum":str(minimum),"all_nonnegative":bool(minimum>=0),
                    "coefficients":[[str(a) for a in row] for row in coeff]}
            print(json.dumps({key:value for key,value in record.items() if key!="coefficients"}),flush=True)
            rows.append(record)
    Path(__file__).with_name("round31_pair_candidate_certificate.json").write_text(
        json.dumps(rows,indent=2),encoding="utf-8")


if __name__=="__main__":
    main()
