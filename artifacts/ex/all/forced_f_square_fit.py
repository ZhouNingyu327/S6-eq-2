"""Exact one-square fitting for geometrically forced rational points.

This is a local inclusion check, not a target-point covering search.
Angles and translations are eliminated by a two-dimensional convex polygon.
"""
from fractions import Fraction as F
from itertools import combinations

def square_fit(points):
 pts=[(F(x),F(y)) for x,y in points]
 span=max(max(x for x,y in pts)-min(x for x,y in pts),
          max(y for x,y in pts)-min(y for x,y in pts))
 assert span>1,"This entry uses the long-chord case to exclude axis vertices."
 rows=set()
 for i,j in combinations(range(len(pts)),2):
  dx=pts[i][0]-pts[j][0];dy=pts[i][1]-pts[j][1]
  rows.update(((dx,dy),(-dx,-dy),(dy,-dx),(-dy,dx)))
 rows.discard((F(0),F(0)));rows=sorted(rows)
 axis=1/span;vertices={(F(0),F(0)),(axis,F(0)),(F(0),axis)}
 tested=0
 for (a,b),(d,e) in combinations(rows,2):
  det=a*e-b*d
  if det==0:continue
  tested+=1
  c=(e-b)/det;s=(a-d)/det
  if c<=0 or s<=0:continue
  if all(aa*c+bb*s<=1 for aa,bb in rows):vertices.add((c,s))
 best=max(vertices,key=lambda z:z[0]**2+z[1]**2)
 n2=best[0]**2+best[1]**2
 return {"fits_unit_square":n2>=1,"maximum_vertex_norm_squared":str(n2),
  "minimum_enclosing_square_side_squared":str(1/n2),
  "witness_vertex":[str(v) for v in best],"row_count":len(rows),
  "nonparallel_row_pairs_tested":tested,"vertex_count":len(vertices),
  "vertices":[[str(c),str(s),str(c*c+s*s)] for c,s in sorted(vertices)],
  "meaning":"If feasible, normalize the witness vertex to unit length and choose projection minima as support origins."}
