# Notation and source correspondence

The core fixes the geometric objects once. A technical lemma introduces its
own auxiliary parameters only within its stated scope.

- Target: T_mu = [-mu,mu]^2, mu > 1. The core also writes T for this same set.
- Corner indices: 1 lower-left, 2 lower-right, 3 upper-right, 4 upper-left.
- V_i: the four selected corner hosts.
- C: a selected central tile, proved unique only after G5.
- F: the remaining sixth tile; it may overlap or duplicate an outer host.
- W: the free corner V_i in the current representative, never F.
- H_0 and V_0: the central horizontal and vertical target segments.
- kappa: number of distinct outer midpoints belonging to C union F.
- l,r,u,d: actual axial reaches of C.
- L_C,R_C,U_C,D_C: the corresponding four points.
- a,x,z: final-form half-angles of V_1,V_2,V_4.
- eta: final-form half-angle of C; its rotation sign is separately specified.
- tau: the designated half-angle of W.
- lambda(t) = 2t/(1-t^2): the slope function.
- b(t) = (1+t^2)/(1-t^2), g(t) = (1-t)/(1+t), q(t) = t/(2-t).
- Sigma = S_1 + S_2 in the far final form.
- Q_R,Q_U: inward positive-axis tips of V_2,V_4.

## Correspondence in the protected technical formulae

The protected source expressions retain locally defined auxiliary notation.
The following are semantic correspondences, not permission to substitute
letters outside their domains:

- Source k as a cardinality corresponds to core kappa.
- Source k(t) as a slope function corresponds to core lambda(t).
- Source H,V when they denote sets correspond to core H_0,V_0.
- Source H or J when they denote floating chord lengths remain local lengths,
  not the whole central target segments.
- Source Q2 or Q_2 corresponds to core Q_R.
- Source T_C or the upper axial point T corresponds to core U_C.
- Source B or B_C when it denotes the lower axial point corresponds to D_C.
- Source h or eta describing C's half-angle corresponds to core eta.
- In R42 specifically, the local h is lambda(z), not C's half-angle.
  Its local k is lambda(a), G is g(z), and S is S_4.
- Source t describing W in a specified final case corresponds to core tau;
  source t_i describing an anchored corner is a different variable.

Named lower bounds and algebraic endpoints are not automatically actual
geometric points. In particular, X_G/e_G from an analytic endpoint test do
not define a second placement of C.
