"""Three analytical parameter charts for one local projection lemma.

Exact rational Bernstein coefficients on complete rectangles.
There is no adaptive subdivision and no angle or layout sampling.
"""
import json
from math import comb
from pathlib import Path
import sympy as sp

def bernstein(poly):
    nx,ny=poly.degree_list()
    return [[sum(coef*sp.Rational(comb(i,p),comb(nx,p))*
                 sp.Rational(comb(j,q),comb(ny,q))
                 for (p,q),coef in poly.terms() if p<=i and q<=j)
             for j in range(ny+1)] for i in range(nx+1)]

def main():
    a,z,u,v=sp.symbols("a z u v")
    b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
    Q=lambda S:S+(h-1)*(b+S-2)/(k-h)
    R1=Q((1-z)/(1+z))-z-sp.Rational(5,12)
    R2=Q(2-(b-sp.Rational(2,7))/k)-z-sp.Rational(5,12)
    P1=sp.Poly(sp.cancel(R1*(a-z)*(1+a*z)),a,z)
    P2=sp.Poly(sp.cancel(R2*28*a*(a-z)*(1+a*z)),a,z)
    Yc=a*a/(1-2*a*a)
    Z=(1-a)*(5-9*a)/(-9*a*a+42*a-5)
    rows=[]
    charts=[
        ("small a, cosine envelope",P1,sp.Rational(1,4),sp.Rational(1,3),Yc),
        ("Ka<=1, short-leg envelope",P1,sp.Rational(1,3),sp.Rational(3,7),Z),
        ("Ka>=1, short-leg envelope",P2,sp.Rational(2,5),sp.Rational(5,9),Z)]
    for name,P,lo,hi,Y in charts:
        den=sp.denom(Y)
        E=sp.cancel(P.as_expr().subs(z,Y*v)*den**P.degree(z))
        transformed=sp.Poly(sp.expand(E.subs(a,lo+(hi-lo)*u)),u,v)
        coeff=bernstein(transformed);minimum=min(x for row in coeff for x in row)
        row={"chart":name,"a_interval":[str(lo),str(hi)],"Y":str(Y),
             "degrees":list(transformed.degree_list()),"minimum":str(minimum),
             "all_nonnegative":bool(minimum>=0),
             "coefficients":[[str(x) for x in line] for line in coeff]}
        rows.append(row)
        print(json.dumps({k:v for k,v in row.items() if k!="coefficients"}),flush=True)
    folder=Path("work") if Path("work").is_dir() else Path(".")
    (folder/"round41_corner_certificate.json").write_text(
        json.dumps(rows,indent=2),encoding="utf-8")
if __name__=="__main__":main()
