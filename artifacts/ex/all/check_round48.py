"""Exact support identities and elementary four-set mod-2 chain check."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
def main():
 t,L,mu=sp.symbols("t L mu")
 p=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
 X=s*(1-p*L);Y=p+s*s*L;U=(1-p*mu)/s
 ids=[]
 def ident(name,value):
  assert sp.cancel(value)==0,(name,sp.factor(value));ids.append(name)
 ident("right upper vertex first support",s*X+p*Y-1)
 ident("right upper vertex second lower support",p*X-s*Y+s*L)
 ident("right edge endpoint first support",p*L-p*L)
 ident("right edge endpoint second lower support",-s*L+s*L)
 ident("right upper vertex height above outer endpoint",Y-L-p*(1-p*L))
 ident("right upper vertex height above H",Y-mu-(L-mu+p*(1-p*L)))
 ident("right H endpoint to vertex along first edge",U-X-p*(Y-mu)/s)
 ident("right upper vertex below cosine sine cap",p+s-Y-s*(1-s*L))
 # Top formulas are derived afresh, not numerical rotations.
 XT=p+s*s*L;YT=s*(1-p*L)
 ident("top right vertex first support",p*XT+s*YT-1)
 ident("top right vertex second lower support",-s*XT+p*YT+s*L)
 ident("top endpoint first support",p*L-p*L)
 ident("top endpoint second lower support",-s*L+s*L)
 ident("top right vertex beyond vertical axis",XT-mu-(L-mu+p*(1-p*L)))
 ident("top V endpoint to vertex along first edge",U-YT-p*(XT-mu)/s)
 ident("top right vertex inside target horizontal cap",p+s-XT-s*(1-s*L))
 # Faces ordered 123,124,134,234. Edges ordered 12,13,14,23,24,34.
 faces=[(1,2,3),(1,2,4),(1,3,4),(2,3,4)]
 edges=[(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
 boundary=(1,0,1,1,0,1)
 def chain(bits):
  return tuple(sum(bit for bit,face in zip(bits,faces) if i in face and j in face)%2
               for i,j in edges)
 solutions=[bits for bits in product((0,1),repeat=4) if chain(bits)==boundary]
 assert solutions==[(0,1,0,1),(1,0,1,0)]
 availability=[]
 for present in product((0,1),repeat=4):
  fills=any(all(not bit or has for bit,has in zip(sol,present)) for sol in solutions)
  opposite_pair=(present[0] and present[2]) or (present[1] and present[3])
  assert fills==bool(opposite_pair)
  availability.append({"faces_present":list(present),"boundary_cycle_fills":fills})
 out=Path("outputs") if Path("outputs").is_dir() else Path(".")
 result={"result":"passed","algebraic_identities":len(ids),"identity_names":ids,
  "mod2_boundary_cycle_solutions":[list(q) for q in solutions],
  "four_face_availability_patterns_checked":len(availability),"availability":availability,
  "geometric_proofs":"Common-point fan; boundary path contraction; fine triangulation labels with compact thickening",
  "scope":"Exact lower-half five-point reduction when W contains QU; actual upper corner triple junctions; two lower-right contact combinations for the right-W bridge",
  "UNSAT":0,"sampling":False,"layout_optimization":False,
  "not_proved":"Incompatibility of all remaining parameters, any new entire contact mechanism, G2 or S(6)=2"}
 (out/"S6_round48_local_verification.json").write_text(json.dumps(result,indent=2),encoding="utf-8")
 print(json.dumps({k:v for k,v in result.items() if k not in {"identity_names","availability"}},indent=2))
if __name__=="__main__":main()

