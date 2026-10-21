"""One explicit candidate for testing sufficiency of axis/edge budgets.

No layout optimization or finite-point covering search is performed.
Floating polygon difference is diagnostic; exact tests will be separate.
"""
import json, math
from pathlib import Path
import numpy as np
from shapely.geometry import Polygon
from shapely.ops import unary_union

mu=1.0000000001
def cs(t):
    return (1-t*t)/(1+t*t),2*t/(1+t*t)
def strips(n1,n2,lo1,hi1,lo2,hi2):
    mat=np.array([n1,n2])
    return Polygon([np.linalg.solve(mat,[p,q]) for p,q in
                    [(lo1,lo2),(hi1,lo2),(hi1,hi2),(lo1,hi2)]])
def corner(t,L,corner,longdir):
    c,s=cs(t)
    # Inward local coordinates (X,Y), long leg is X.
    local=strips((c,s),(-s,c),0,1,-s*L,1-s*L)
    origin=np.array(corner)
    if longdir=="up": ex,ey=np.array([0,1]),np.array([1,0])
    elif longdir=="left": ex,ey=np.array([-1,0]),np.array([0,-1])
    elif longdir=="right": ex,ey=np.array([1,0]),np.array([0,-1])
    else: raise ValueError(longdir)
    if corner[0]>0 and longdir=="up":ey=np.array([-1,0])
    return Polygon([origin+X*ex+Y*ey for X,Y in local.exterior.coords[:-1]])

a=1/math.sqrt(7); x=.400000002; z=.199999999; t=.00001
L1=4/3;L2=1.00003;L4=mu;D=mu
S1=(1+a*a-2*a*L1)/(1-a*a)
S2=(1+x*x-2*x*L2)/(1-x*x)
S4=(1+z*z-2*z*L4)/(1-z*z)
A=(1+t*t-2*t*D)/(1-t*t)
l=.623;r=.59999999821;u=(1-.6*r)/.8;d=1.25-u
C=strips((.8,.6),(-.6,.8),-.8*l,1-.8*l,.8*u-1,.8*u)
fcx=(S1-S2)/2
F=strips((1/math.sqrt(2),1/math.sqrt(2)),(-1/math.sqrt(2),1/math.sqrt(2)),
         (fcx-mu)/math.sqrt(2)-.5,(fcx-mu)/math.sqrt(2)+.5,
         (-fcx-mu)/math.sqrt(2)-.5,(-fcx-mu)/math.sqrt(2)+.5)
parts={
 "V1":corner(a,L1,(-mu,-mu),"up"),
 "V2":corner(x,L2,(mu,-mu),"up"),
 "V4":corner(z,L4,(-mu,mu),"right"),
 "W":corner(t,D,(mu,mu),"left"),
 "C":C,"F":F}
target=Polygon([(-mu,-mu),(mu,-mu),(mu,mu),(-mu,mu)])
missing=target.difference(unary_union(list(parts.values())))
components=list(missing.geoms) if hasattr(missing,"geoms") else [missing]
result={"meaning":"explicit six-unit-square local-grid candidate; not a covering claim",
 "mu":mu,"S1":S1,"S2":S2,"Sigma":S1+S2,
 "meeting_slacks":[L1+S4-2*mu,L2+A-2*mu,L4+D-2*mu],
 "roots":{"l":l,"r":r,"u":u,"d":d},
 "missing_area_float_diagnostic":missing.area,
 "missing_components":[{"area":p.area,"bounds":p.bounds,
                        "interior_witness":list(p.representative_point().coords)[0],
                        "vertices":list(p.exterior.coords)} for p in components if p.area>0]}
print(json.dumps(result,indent=2))
Path("work/round40_grid_candidate_diagnostic.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
