"""Exact rational check of the six-open-square construction for finite sets."""
from fractions import Fraction as F
import random


def local(p, k):
    x, y = p
    for _ in range(k):
        x, y = y, 2-x
    return x, y


def construct(points):
    points = [(F(x), F(y)) for x, y in points]
    assert all(0 <= x <= 2 and 0 <= y <= 2 for x, y in points)
    d = F(1)
    cross_distance = F(1)
    for x, y in points:
        if x != 1 and y != 1:
            k = 0 if x < 1 and y < 1 else 1 if x > 1 and y < 1 else 2 if x > 1 and y > 1 else 3
            a, b = local((x, y), k)
            assert 0 <= a < 1 and 0 <= b < 1
            d = min(d, 1-a, 1-b)
        else:
            v = y if x == 1 else x
            if 0 < v < 2:
                cross_distance = min(cross_distance, v, 2-v)
    r = min(F(1, 8), d/8)
    t = min(F(1, 4), cross_distance/4)
    c = (1-r*r)/(1+r*r)
    s = 2*r/(1+r*r)
    e = r*r/(1+r*r)
    assert s+e < d and c*c+s*s == 1
    return r, t, c, s, e


def depth(p, parameters):
    r, t, c, s, e = parameters
    ds = []
    for k in range(4):
        x, y = local(p, k)
        u, v = c*x+s*y, -s*x+c*y
        ds.append(min(u+e, 1-e-u, v+s+e, 1-s-e-v))
    x, y = p
    ds += [min(x-t, 1+t-x, y-t, 1+t-y),
           min(x-1+t, 2-t-x, y-1+t, 2-t-y)]
    return max(ds)


def check(points):
    parameters = construct(points)
    margin = min(depth((F(x), F(y)), parameters) for x, y in points)
    assert margin > 0
    return margin


if __name__ == '__main__':
    grid = [(F(i, 10), F(j, 10)) for i in range(21) for j in range(21)]
    print('21 by 21 grid exact positive margin:', check(grid))
    fixed = (F(1, 1000), F(1, 1000), F(999999, 1000001), F(2000, 1000001), F(1, 1000001))
    margin = min(depth(p, fixed) for p in grid)
    assert margin == F(1, 1000001)
    print('Fixed r=t=1/1000 exact margin:', margin)
    rng = random.Random(20261008)
    for _ in range(100):
        points = [(F(rng.randrange(2001), 1000), F(rng.randrange(2001), 1000)) for _ in range(100)]
        points += [(0,0),(2,0),(2,2),(0,2),(1,0),(2,1),(1,2),(0,1),(1,1)]
        check(points)
    print('PASS: 100 finite rational point sets, with all corners and midpoints')
