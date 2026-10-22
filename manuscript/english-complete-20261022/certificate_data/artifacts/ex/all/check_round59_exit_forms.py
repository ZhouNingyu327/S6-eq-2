"""Unfrozen algebra for future actual E1/TR/F constraints; no exclusion claim."""
from pathlib import Path
import sympy as s,json
def main():
 a,h,R,S,mu,Sigma=s.symbols('a h R S mu Sigma')
 k=lambda z:2*z/(1-z*z);g=lambda z:(1-z)/(1+z)
 alpha=1-R/k(h)
 vv=2*h*a*(a-alpha)/((a-h)*(1+h*a))
 fmin=1-1/(2-g(a)-S)
 identities={
  'E1_general_support':(R-k(h)*(1-a))/(1-k(h)/k(a))-vv,
  'same_a_height':fmin-(2*a-(1+a)*S)/(1+3*a-(1+a)*S),
  'triangle_mu_monotone':s.diff(mu-1/(2*mu-Sigma),mu)-(1+2/(2*mu-Sigma)**2),
  'V_derivative':s.diff(vv,a)-2*h*((1-h*h+h*alpha)*a*a-2*h*a+h*alpha)/((a-h)**2*(1+h*a)**2)}
 for name,expr in identities.items():assert s.cancel(expr)==0,name
 result={'result':'passed','identities':list(identities),'new_angle_or_mechanism_exclusion':False,
  'required_geometric_guards':['W contains QU; actual T_R lower bounds with mu correlation',
   'same actual E1, C, F and bottom endpoints','a > h before dividing 1-k(h)/k(a)',
   'alpha_R > h before using the old monotone V(A) argument']}
 out=Path(__file__).resolve().parent.parent/'outputs'/'S6_round59_exit_forms_check.json'
 out.write_text(json.dumps(result,indent=2),encoding='utf-8');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
