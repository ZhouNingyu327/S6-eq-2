"""Independent exact algebra audit for the near G2 angle restriction.

No floating arithmetic, finite angle sampling, or certificate-generator imports.
"""
from pathlib import Path
from math import comb
import json
import sympy as s

ROOT = Path(__file__).resolve().parent
x, r, u, v = s.symbols('x rho u v')

def coefficients(poly, variables):
    p = s.Poly(s.expand(poly), *variables)
    degrees = p.degree_list()
    out = []
    import itertools
    for idx in itertools.product(*(range(d + 1) for d in degrees)):
        value = s.S.Zero
        for powers, coefficient in p.terms():
            if all(a <= b for a, b in zip(powers, idx)):
                value += coefficient * s.prod(
                    s.Rational(comb(b, a), comb(d, a))
                    for a, b, d in zip(powers, idx, degrees))
        out.append((idx, s.factor(value)))
    # Reconstruct the complete polynomial independently from the coefficients.
    rebuilt = sum(value * s.prod(
        comb(d, i) * t**i * (1-t)**(d-i)
        for i, t, d in zip(idx, variables, degrees)) for idx, value in out)
    assert s.expand(rebuilt - p.as_expr()) == 0
    return degrees, out

rows = []
Y = x*x/(1-2*x*x)
F = (1-Y)**2*r*(2+r) - (x+r)**2
for name, endpoint, divide in [
    ('small_x_lower_rho', x*(1-x)/5, x),
    ('small_x_upper_rho', s.Rational(5,12), 1),
]:
    original = s.cancel(F.subs(r, endpoint)*(1-2*x*x)**2/divide)
    assert s.denom(original) in s.QQ
    transformed = s.expand(original.subs(x, s.Rational(3,14)*u))
    degrees, bs = coefficients(transformed, (u,))
    assert all(value > 0 for _, value in bs)
    rows.append({'name': name, 'degrees': degrees,
                 'coefficients': [str(value) for _, value in bs],
                 'count': len(bs), 'strictly_positive': True})

# High-angle triangle comparison: at l >= 1-y its twice-area exceeds 1.
Ys = (1-x)**2/(6*x-1-x*x)
comparison = (1-x)*(1-Ys) - 2*Ys + Ys**2
comparison_polynomial = 2*x**4-23*x**3+69*x**2-37*x+5
assert s.cancel(comparison-(1-x)*comparison_polynomial/
                (6*x-1-x*x)**2) == 0
degrees, bs = coefficients(comparison_polynomial.subs(x,(1+u)/2), (u,))
assert all(value > 0 for _, value in bs)
rows.append({'name': 'left_helper_below_upper_helper', 'degrees': degrees,
             'coefficients': [str(value) for _, value in bs],
             'count': len(bs), 'strictly_positive': True})

U = s.Rational(46,47)
L = s.Rational(13228,22063)
large = s.expand(U*U*r*(2+r) - (1+r-L)**2)
assert s.Poly(large, r).nth(2) < 0
large_endpoints = [s.factor(large.subs(r,a))
                   for a in (s.Rational(1,6), s.Rational(5,12))]
assert all(value > 0 for value in large_endpoints)
rows.append({'name': 'large_rho_concave_quadratic',
             'endpoint_values': list(map(str, large_endpoints)), 'count': 2})

B = 1-x+r*(3+x)-2*r*r
P = s.expand(47**2*(U*U*r*(2+r)*(1+x-2*r)**2-B*B))
r0 = x*(1-x)/5
transformed = s.expand(P.subs(r, r0+(s.Rational(1,6)-r0)*v)
                       .subs(x, s.Rational(3,4)+u/4))
data = json.loads((ROOT/'round15_upper_certificate.json').read_text(encoding='utf-8'))
assert s.expand(s.sympify(data['original_polynomial'])-P) == 0
assert s.expand(s.sympify(data['transformed_polynomial'])-transformed) == 0
assert data['leaves'] == [{'path': '', 'minimum': '0'}]
degrees, bs = coefficients(transformed, (u,v))
assert list(degrees) == data['degrees'] == [8,4]
assert len(bs) == 45 and all(value >= 0 for _, value in bs)
rows.append({'name': 'high_x_small_rho_whole_rectangle', 'degrees': degrees,
             'coefficients': [str(value) for _, value in bs],
             'count': len(bs), 'nonnegative': True,
             'minimum': str(min(value for _, value in bs))})

result = {'classification': 'exact rational coefficient verification',
          'checks': rows,
          'bernstein_coefficient_count': sum(row['count'] for row in rows
                                             if 'coefficients' in row),
          'quadratic_endpoint_count': 2,
          'passed': True}
(ROOT/'round15_angle_certificate_checks.json').write_text(
    json.dumps(result, indent=2), encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k != 'checks'}, indent=2))
