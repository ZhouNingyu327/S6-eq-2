"""Independently rebuild full Bernstein polynomials from exact saved coefficients."""
from pathlib import Path
import json
from math import comb
import sympy as sp

def main():
    a,z,u,v=sp.symbols("a z u v")
    b=(1+a*a)/(1-a*a);k=2*a/(1-a*a);h=2*z/(1-z*z)
    Q=lambda S:S+(h-1)*(b+S-2)/(k-h)
    R1=Q((1-z)/(1+z))-z-sp.Rational(5,12)
    R2=Q(2-(b-sp.Rational(2,7))/k)-z-sp.Rational(5,12)
    P1=sp.Poly(sp.cancel(R1*(a-z)*(1+a*z)),a,z)
    P2=sp.Poly(sp.cancel(R2*28*a*(a-z)*(1+a*z)),a,z)
    Yc=a*a/(1-2*a*a);Z=(1-a)*(5-9*a)/(-9*a*a+42*a-5)
    first=[
        (P1,sp.Rational(1,4),sp.Rational(1,3),Yc),
        (P1,sp.Rational(1,3),sp.Rational(3,7),Z),
        (P2,sp.Rational(2,5),sp.Rational(5,9),Z)]
    expected=[]
    for p,lo,hi,Y in first:
        E=sp.cancel(p.as_expr().subs(z,Y*v)*sp.denom(Y)**p.degree(z))
        expected.append(sp.Poly(sp.expand(E.subs(a,lo+(hi-lo)*u)),u,v))
    q=lambda t:t/(2-t)
    T=sp.Rational(7,12)-q(sp.Rational(5,12)+z)
    RR=Q(2-(b-T)/k)-z-sp.Rational(5,12)
    PP=sp.Poly(sp.cancel(RR*24*a*(a-z)*(1+a*z)*(19-12*z)),a,z)
    P=sp.Poly(sp.cancel(R1*12*(a-z)*(1+a*z)),a,z)
    N=sp.Poly(sp.cancel((b-k*(2-(1-z)/(1+z))-T)*
                       12*(1-a*a)*(1+z)*(19-12*z)),a,z)
    A=(27-16*z)/60;am=sp.Rational(155,301)
    second=[
        (PP,sp.Rational(2,5)+(am-sp.Rational(2,5))*u,sp.Rational(3,2)*(am-a)*v),
        (P,sp.Rational(3,7)*u,sp.Rational(1,7)*v),
        (P,sp.Rational(2,5)*u,sp.Rational(1,7)+(sp.Rational(3,16)-sp.Rational(1,7))*v),
        (-N,sp.Rational(2,5)+(sp.Rational(3,7)-sp.Rational(2,5))*u,
         sp.Rational(1,7)+(sp.Rational(3,16)-sp.Rational(1,7))*v),
        (P,A*u,sp.Rational(3,16)+(sp.Rational(2,9)-sp.Rational(3,16))*v),
        (-N,A+(sp.Rational(3,7)-A)*u,sp.Rational(3,16)+(sp.Rational(2,9)-sp.Rational(3,16))*v)]
    for p,aa,zz in second:
        if zz.has(a):
            E=sp.cancel(p.as_expr().subs(z,zz)*sp.denom(sp.cancel(zz))**p.degree(z))
            expected.append(sp.Poly(sp.expand(E.subs(a,aa)),u,v))
        else:
            aa=sp.cancel(aa)
            E=sp.cancel(p.as_expr().subs(a,aa)*sp.denom(aa)**p.degree(a))
            expected.append(sp.Poly(sp.expand(E.subs(z,zz)),u,v))
    folder=Path("work") if Path("work").is_dir() else Path(".")
    saved=(json.loads((folder/"round41_corner_certificate.json").read_text(encoding="utf-8"))+
           json.loads((folder/"round41_direct_certificate.json").read_text(encoding="utf-8")))
    assert len(saved)==len(expected)==9
    count=0;reconstructions=[]
    for row,poly in zip(saved,expected):
        n,m=poly.degree_list();assert row["degrees"]==[n,m]
        values=[[sp.Rational(vv) for vv in line] for line in row["coefficients"]]
        assert len(values)==n+1 and all(len(line)==m+1 for line in values)
        assert all(c>=0 for line in values for c in line)
        expansion=sum(values[i][j]*comb(n,i)*u**i*(1-u)**(n-i)*
                      comb(m,j)*v**j*(1-v)**(m-j)
                      for i in range(n+1) for j in range(m+1))
        assert sp.Poly(sp.expand(expansion-poly.as_expr()),u,v).is_zero
        count+=(n+1)*(m+1)
        reconstructions.append({"chart":row["chart"],"degrees":[n,m],
                                "coefficient_count":(n+1)*(m+1),
                                "minimum":str(min(c for line in values for c in line))})
    assert count==219
    result={"result":"passed","whole_parameter_charts":9,"polynomial_identities":9,
            "nonnegative_rational_coefficients":count,"charts":reconstructions,
            "scope":"two explicit local support inequalities; no target point enumeration or adaptive subdivision"}
    out=Path("outputs") if Path("outputs").is_dir() else Path(".")
    (out/"S6_round41_certificate_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if k!="charts"},indent=2))
if __name__=="__main__":main()
