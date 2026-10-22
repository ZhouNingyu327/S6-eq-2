# English Technical Appendix

**Six unit squares: detailed candidate argument. English review edition.**

This appendix contains the detailed derivations cited by the English core.
Read it in the logical family order below, using the core's notation register
and sole normalization protocol. The labels R2--R64 and the nine lettered
supplements are stable source and certificate identifiers, not an instruction
to reconstruct a research chronology.

The English derivations were edited directly from the source. Repetitive
progress announcements are compressed; hypotheses, geometric membership,
case distinctions, boundary qualifications and mathematical evidence must
remain explicit. Editing is not independent validation of the candidate.
Where a statement invokes another module or a finite certificate, that
dependency remains part of its premise chain.

The target is \(T_\mu=[-\mu,\mu]^2\), \(\mu>1\), unless a module explicitly uses its
translated chart \([0,2\mu]^2\). These are coordinate charts of the same target,
not a rescaling of the unit tiles. Auxiliary lengths and parameters have
the scope stated in their module. Original C and F are unchanged within a
geometric implication unless a stated covering replacement is actually made.

Only stepwise target-relative cover-dominating replacement is used as the
normalization protocol. After a replacement, account for every resulting
host, gap and chord state. The optional one-shot clamp from the historical
source is not an active premise. Leaving a local case is not by itself a
contradiction.

Tangency is nonempty with zero chord length. Two-line budgets require both
actual intersections to be nonempty. A floating chord has no assumed common
endpoint with another chord. A normalized necessary point inside C does not
rescale or move C. All q-domains and denominator signs must be checked before
substitution or clearing denominators.

The full claim remains a candidate argument for external review. Formula
rendering, source editing, certificate replay and full geometric correctness
are different questions. The accompanying review record states which checks
were actually run.

<a id="technical-part-A"></a>
# Technical Part A. Foundation and the two-centre cases

Modules: [R2](#R2), [R3](#R3), [R4](#R4), [R5](#R5), [R6](#R6), [R7](#R7), [R8](#R8).

<a id="R2"></a>
## R2. Fundamental grid and chord budgets

**Scope.** This module proves the basic budgets and excludes G5 when the two
central tiles jointly contain two outer midpoints. It does not exclude the
other G5 cases. A normalization is a target-relative covering replacement;
any later use of a host pattern must apply to the resulting configuration.

### 1. Coordinates, roles, and the six-line grid

Use the translated chart \(S=[0,2\mu]^2\), with \(\mu>1\); it is the core's
centred target translated by \((\mu,\mu)\). Label its corners and midpoints
counter-clockwise:

\[
v_1=(0,0),\quad v_2=(2\mu,0),\quad v_3=(2\mu,2\mu),\quad v_4=(0,2\mu),
\]
\[
m_1=(\mu,0),\quad m_2=(2\mu,\mu),\quad m_3=(\mu,2\mu),\quad m_4=(0,\mu),
\qquad o=(\mu,\mu).
\]

The four corners require distinct tiles \(V_i\). Their distance from \(o\)
exceeds the unit-square diameter, so a fifth tile \(C\) contains \(o\); call
the remaining tile \(F\). Each tile contains at most one outer midpoint.
Set

\[
\kappa=|\{m_1,m_2,m_3,m_4\}\cap(C\cup F)|.
\]

G5 means \(o\in C\cap F\). A midpoint shared with a corner tile is still
counted in \(\kappa\). Let \(\mathcal G\) be the six target segments on

\[
x=0,\mu,2\mu,\qquad y=0,\mu,2\mu.
\]

Intersections of these segments have one-dimensional measure zero, so

\[
|\mathcal G|=12\mu>12.
\]

### 2. The sharp bound for two nonempty parallel chords

**Lemma 1.** If a unit square meets two parallel lines at distance \(d>1\),
then \(d\le\sqrt2\), and the sum of its two full chord lengths is at most

\[
B(d)=\begin{cases}
d-\sqrt{d^2-1},&1<d\le3/(2\sqrt2),\\
2(\sqrt2-d),&3/(2\sqrt2)\le d\le\sqrt2.
\end{cases}
\]

The bound is sharp, and \(B(d)<1\).

**Proof.** Make the lines vertical and reflect the square if necessary so
that its side parameters satisfy \(c\ge s>0\), \(c^2+s^2=1\). Its horizontal
width is \(z=c+s\le\sqrt2\). Put its leftmost abscissa at zero and the lines
at \(t,t+d\), with \(0\le t\le z-d\). Since \(d>1\ge c\), the chords lie in
the two triangular end caps. Their total length is

\[
\frac{t}{cs}+\frac{z-t-d}{cs}
=\frac{z-d}{cs}=\frac{2(z-d)}{z^2-1}.
\]

Its derivative with respect to \(z\) is

\[
\frac{2(-z^2+2dz-1)}{(z^2-1)^2}.
\]

On \(d\le z\le\sqrt2\), the maximum occurs at

\[
z=d+\sqrt{d^2-1}
\]

if that point is allowed, and otherwise at \(z=\sqrt2\). The transition is

\[
d=\frac{3}{2\sqrt2}.
\]

Substitution gives the two stated branches. The corresponding square and
any allowed \(t\) attain equality. This argument includes singleton tangent
chords. It does not apply if one of the intersections is empty. At \(d=1\),
an axis-aligned square can have two chords of length one; hence the strict
premise \(d>1\) cannot be dropped. \(\square\)

**Corollary.** Two unit squares cannot cover the entire boundary of a square
of side \(\mu>1\).

If \(\mu>\sqrt2\), even two adjacent corners cannot share a unit tile. For

\[
1<\mu\le\sqrt2,
\]

one tile cannot contain three corners: their triangle has area

\[
\mu^2/2>1/2,
\]

whereas a triangle in a unit square has area at most \(1/2\). Opposite corners
also cannot share a tile. Thus the two tiles must contain adjacent pairs,
say the upper and lower pairs. Both tiles meet the left and right lines;
their total contribution there is at most \(2B(\mu)<2\), less than the
required \(2\mu\). The other pairing is symmetric. This proves the boundary
covering fact used subsequently.

### 3. Corner normalization and the full grid bound

**Lemma 2.** In inward coordinates at a target corner, its tile can be
replaced, without losing any target point, by

\[
0\le cx+sy\le1,\qquad
-\beta\le-sx+cy\le1-\beta,
\quad c,s\ge0,\quad c^2+s^2=1,\quad0\le\beta\le1.
\]

Indeed, choose an oriented normal in the closed first quadrant. The original
projection interval \([L,L+1]\) contains zero. The target has nonnegative
projection, so replacing that interval by \([0,1]\) preserves its previously
covered target points. Keep the orthogonal projection interval unchanged.
This is one local replacement, not a proof that all later clamps are identities.

**Lemma 3.** Every unit tile containing a target corner satisfies

\[
|V\cap\mathcal G|\le2.
\]

The inequality is strict for a non-axis-aligned tile.

**Proof.** Normalize and exchange coordinates so that \(c\ge s>0\). The two
remote outer edges cannot meet the tile. For a vertical line \(x\ge1\) in
the inward quadrant, the lower and upper chord endpoints are

\[
\max(0,(sx-\beta)/c),\qquad(1-cx)/s.
\]

The former is nondecreasing and the latter nonincreasing. The horizontal
calculation is analogous. Moving the two central lines from distance \(\mu\)
to distance one can only increase the relevant chord lengths. Define locally

\[
t=\frac{1-c}{s}=\tan(\theta/2),\qquad q_0=\frac{1-s}{c}.
\]

Here \(q_0\) is an auxiliary length, not the core's function \(q(t)\).
At spacing one, the outer chords are

\[
L_x=\min(1/c,\beta/s),\qquad L_y=(1-\beta)/c,
\]

and the central chords are

\[
q_x=\begin{cases}
0,&\beta\le t,\\
(\beta-t)/c,&t\le\beta\le s,\\
t,&\beta\ge s,
\end{cases}
\qquad
q_y=\begin{cases}
q_0,&\beta\le1-c,\\
(1-q_0-\beta)/s,&1-c\le\beta\le1-q_0,\\
0,&\beta\ge1-q_0.
\end{cases}
\]

The breakpoints obey

\[
0<1-c<t<1-q_0<s\le s/c\le1.
\]

The sum \(L_x+L_y+q_x+q_y\) is piecewise linear in \(\beta\), with successive
slopes

\[
1/s-1/c,\quad-1/c,\quad0,\quad1/s,\quad1/s-1/c,\quad-1/c.
\]

Thus it suffices to compare \(\beta=1-c\) and \(\beta=s/c\), giving

\[
g_1=1+t+q_0=1+\frac{c+s-1}{cs},\qquad
g_2=\frac{2c-s}{c^2}+t.
\]

With

\[
c=\frac{1-t^2}{1+t^2},\quad
s=\frac{2t}{1+t^2},\quad0<t\le\sqrt2-1,
\]

the exact differences are

\[
g_2-g_1=\frac{-2t^2(t^2+2t-1)}{(1-t^2)^2}\ge0,
\]
\[
2-g_2=\frac{t[(1-2t)^2+t^3(4-t)]}{(1-t^2)^2}>0.
\]

This proves the strict bound. An axis-aligned corner tile misses both central
lines and contributes at most one along each adjacent outer edge, giving
the weak bound two. \(\square\)

### 4. A long chord and three connected sections

**Lemma 4.** Suppose a unit square contains \((0,0)\) and \((\mu,0)\), with

\[
\mu>1.
\]

Let \(H\) be its length on the nonnegative horizontal ray, \(L\) its full
chord on \(x=0\), and \(U\) its upward-ray length from \((\mu,0)\). Then

\[
H+L+U<2.
\]

**Proof.** The long chord excludes an axis-aligned square. Choose positive
direction parameters and write the two strips as

\[
-\alpha\le cx+sy\le1-\alpha,\qquad
-\beta\le-sx+cy\le1-\beta.
\]

The anchors imply

\[
0\le\alpha\le1-\mu c,\qquad\mu s\le\beta\le1,
\qquad\mu c\le1,\quad\mu s\le1.
\]

Direct intersection gives

\[
H=\min((1-\alpha)/c,\beta/s),\quad
L=(1-\beta)/c+\alpha/s,\quad
U=(1-\alpha-\mu c)/s.
\]

Consequently

\[
H+L+U=H+\frac{1-\beta}{c}+\frac{1-\mu c}{s}.
\]

Its dependence on \(\alpha\) is nonincreasing, so set \(\alpha=0\) for an
upper bound. If \(c\ge s\), maximization in \(\beta\) occurs at the allowed
point \(\beta=s/c\), whence

\[
H+L+U\le\frac{2c-s}{c^2}+\frac{1-\mu c}{s}
=g_2-\frac{(\mu-1)c}{s}<2.
\]

If \(c<s\), the expression decreases on its allowed \(\beta\)-interval and
is maximal at \(\beta=\mu s\). Hence

\[
H+L+U\le\mu+\frac{c+s-\mu}{cs}<2.
\]

The last step follows from \(c+s\le1+cs\), itself a consequence of

\[
(1-c)(1-s)\ge0,
\]

and \(\mu>1\). \(\square\)

An additional exact real-algebra check negated this conclusion with the
same positive-denominator domain. Its relevant constraints include

\[
Hcs+s(1-\beta)+c(1-\mu c)\ge2cs,
\quad Hc\le1,\quad Hs\le\beta,\quad H\ge\mu.
\]

The source records UNSAT. The hand proof above, rather than sampling or the
solver status alone, supplies the lemma.

### 5. Exclusion of G5 with two owned midpoints

**Theorem 5.** A six-tile covering in G5 cannot satisfy \(\kappa=2\).

A unit square containing \(m_4,o\) can meet only the left outer edge. A point
on the upper or lower edge would form a triangle of area

\[
\mu^2/2>1/2
\]

with the chord \(m_4o\). A point on the right edge would be at distance at
least \(2\mu>\sqrt2\) from \(m_4\). The same statement holds at other
midpoints by symmetry. The triangle-area bound follows, for example, by
successively maximizing each vertex over the vertices of the unit square.

The corner tiles contribute at most eight to the grid. It remains to bound
the grid contribution of \(C\cup F\) by a number strictly below four.

**Adjacent owned midpoints.** Put \(m_4,o\in C\) and \(m_1,o\in F\). For \(C\),
write \(H_C\) for its horizontal length from \(m_4\), \(E_C\) for its full
left-edge chord, and \(u_C\) for its upward ray from \(o\). For \(F\), rotate
the same three-section construction: \(H_F\) points upward from \(m_1\),

\[
E_F=\text{its full bottom-edge chord},\qquad
r_F=\text{its rightward ray from }o.
\]

Lemma 4 gives

\[
H_C+E_C+u_C<2,\qquad H_F+E_F+r_F<2.
\]

Only the left and bottom outer edges can meet these tiles. Their central
horizontal intervals share \(o\) and cover length at most

\[
\max(H_C,\mu+r_F)\le H_C+r_F,
\]

because \(H_C\ge\mu\). Similarly, the vertical union has length at most

\[
\max(H_F,\mu+u_C)\le H_F+u_C.
\]

These are shared-origin unions in this particular configuration; they are
not formulas for a floating chord. Summing gives

\[
|(C\cup F)\cap\mathcal G|
\le H_C+H_F+E_C+E_F+u_C+r_F<4.
\]

**Opposite owned midpoints.** Put \(m_4,o\in C\) and \(m_2,o\in F\). The
horizontal central union has length \(2\mu\). For each tile, pair its own
outer vertical line with the central vertical line; both intersections
are nonempty. Thus

\[
|(C\cup F)\cap\mathcal G|\le2\mu+2B(\mu)<4.
\]

If \(\mu>\sqrt2\), the anchor chord is already impossible. Otherwise use

\[
B(\mu)\le\mu-\sqrt{\mu^2-1},\qquad
\sqrt{\mu^2-1}>2(\mu-1).
\]

Squaring the second comparison gives the positive difference

\[
(\mu-1)(5-3\mu)>0
\]

for \(1<\mu\le\sqrt2\), proving \(\mu+B(\mu)<2\).
In both cases the grid would have covered length strictly below

\[
8+4=12<12\mu,
\]

a contradiction. \(\square\)

The hypothesis that each central tile contains an outer midpoint is essential
to this module. R3 gives an exact local example preventing its naive extension
to the remaining G5 cases.

<a id="R3"></a>
## R3. Cyclic midpoint hosts and the remaining G5 representatives

**Scope.** Source: `S6_attack_round3.md`, sections 1--9 and 11. This module excludes G5 with no midpoint in the two central tiles, strengthens that exclusion to four midpoint hosts among the corners, and identifies the residual one-midpoint representatives. It is a reconstruction of the supplied argument, with local replacement obligations governed by the protocol.

### 1. Coordinates and actual ownership

Use the translated chart \(S=[0,2\mu]^2\), \(\mu>1\). Let \(v_1=(0,0),v_2=(2\mu,0),v_3=(2\mu,2\mu),v_4=(0,2\mu)\); \(E_i=v_iv_{i+1}\), with cyclic indices, has midpoint \(m_i\), and \(o=(\mu,\mu)\). Four distinct corner tiles \(V_i\) cannot contain \(o\); the other tiles are \(C,F\). In G5, \(o\in C\cap F\). Put
\[
\kappa=|\{m_1,m_2,m_3,m_4\}\cap(C\cup F)|.
\]
Initially assume \(\kappa=0\). Every midpoint has a corner host. Adjacent midpoints are at distance \(\sqrt2\mu>\sqrt2\); a corner tile contains at most one and can host only an adjacent midpoint. The matching is cyclic in one of two directions. Reflect to arrange \(m_i\in V_i\).

### 2. Input bounds and anchored corner parameters

For two nonempty parallel chords at separation \(1<d\le\sqrt2\), R2 proves
\[
B(d)=\begin{cases}d-\sqrt{d^2-1},&d\le3/(2\sqrt2),\\2(\sqrt2-d),&d\ge3/(2\sqrt2),\end{cases}
\qquad B(d)<1,\quad d+B(d)<2.
\]
The last assertion follows from \(B(d)\le d-\sqrt{d^2-1}\) and the squared positive difference \((d-1)(5-3d)>0\). R2 also proves the strict three-section budget for a square containing \((0,0),(\mu,0)\).

A corner tile admits a target-dominating local replacement, in inward coordinates,
\[
0\le cx+sy\le1,\qquad-\beta\le-sx+cy\le1-\beta,
\quad c,s>0,\quad c^2+s^2=1.
\]
The anchored chord of length \(\mu>1\) excludes zero direction parameters. If \(\beta>s/c\), decrease it to \(s/c\): in the first quadrant the first strip already implies \(-sx+cy\ge-s/c\). Thus take \(\beta\le\min(1,s/c)\). This cannot create a second midpoint in this tile, but all other actual predicates must be reclassified after replacement.

Write \(L_i,S_i,U_i\) for the long leg on \(E_i\), the leg on \(E_{i-1}\), and the central segment inward from \(m_i\). Then
\[
L_i=\beta_i/s_i\ge\mu,\quad S_i=(1-s_iL_i)/c_i,\quad
U_i=(1-\mu c_i)/s_i,
\quad c_iL_i,s_iL_i\le1,\quad S_i,U_i\ge0.
\]
The other central line is inaccessible: together with the anchored outer chord, any point there gives a triangle of area \(\mu^2/2>1/2\). Remote outer edges are inaccessible by diameter. Hence its six-line-grid contribution is
\[
T_i=L_i+S_i+U_i<2,
\qquad S_i+U_i\le B(\mu)<1,
\qquad L_i\le\sqrt2.
\]
If \(\mu>\sqrt2\), the anchors already fail. Below assume \(1<\mu\le\sqrt2\), and abbreviate \(B=B(\mu)\).

### 3. At most two outer gaps

The corners join on \(E_i\) precisely when \(L_i+S_{i+1}\ge2\mu\). Otherwise the open gap has length \(g_i=2\mu-L_i-S_{i+1}>0\) and lies in the open half-edge from \(m_i\) toward \(v_{i+1}\), denoted \(H_i\).

A unit tile containing \(o\) meets at most one \(H_i\). Opposite outer edges are \(2\mu>\sqrt2\) apart. For adjacent halves, centered representative points are \(P=(d,-\mu),Q=(\mu,e)\), \(d,e>0\); the triangle \(oPQ\) has area \((\mu^2+de)/2>1/2\). Therefore \(C,F\) can fill at most two gaps. If there are two, each is entirely covered by its own tile, including both endpoints by closedness. There cannot be zero gaps, since summing four joins yields \(\sum(L_i+S_i)\ge8\mu>8>\sum T_i\).

### 4. Two opposite gaps

Let bottom and top gaps \(g_1,g_3\) be covered by \(C,F\). Their full horizontal central chord lengths \(h_C,h_F\) satisfy
\[
h_C+g_1\le B,\quad h_F+g_3\le B,\quad
h_C+h_F+U_2+U_4\ge2\mu.
\]
The outer relations are
\[
L_1+S_2+L_3+S_4=4\mu-g_1-g_3,
\quad L_2+S_3,L_4+S_1\ge2\mu.
\]
Adding yields \(\sum T_i\ge10\mu-2B+U_1+U_3>8\), a contradiction.

### 5. One outer point and two central rays

**Lemma.** A unit square containing \(P=(d,-\mu),Q=(-x,0),R=(0,y)\), where \(d,x,y\ge0,\mu>1\), satisfies \(x+y<1\). Containment of the origin is unnecessary.

Choose orthogonal projections \(u=cX+sY,v=-sX+cY\), \(c,s\ge0,c^2+s^2=1\). The vertical separation \(P,R\) excludes an axis-aligned tile. If \(c\ge s>0\), width conditions give
\[
c\mu+s(d+x)\le1,\quad c(\mu+y)+sd\le1,
\]
and therefore
\[
x+y\le(1-\mu c)/s+1/c-\mu
<(1-c)/s+1/c-1\le2\sqrt2-2<1.
\]
Here \((1-c)/s\le\sqrt2-1\) and \(1/c-1\le\sqrt2-1\). If \(c<s\), multiply \(v(Q)-v(P)\le1\) by \(c\) and \(u(R)-u(P)\le1\) by \(s\), then add:
\[
csx+s^2y\le c+s-\mu<c+s-1<cs.
\]
The last inequality is \((1-c)(1-s)>0\). Thus \(x+(s/c)y<1\), implying the claim.

### 6. Two adjacent gaps

Let bottom and right gaps be covered by \(C,F\), with top and left joined. In centered coordinates put
\[
q_1=(0,-x_1),\ q_2=(x_2,0),\ q_3=(0,x_3),\ q_4=(-x_4,0),
\qquad x_i=\mu-U_i>0.
\]
Each \(q_i\) belongs to \(C\cup F\): approach it through central points beyond the corner segment and use closedness. Its own membership in a corner tile does not remove this necessary condition. A central tile containing \(q_i\) contains \(oq_i\).

First \(q_4\notin F\). The far right-gap endpoint \((\mu,\mu-S_3)\) lies in \(F\); diameter then forces \(U_4\ge2\mu-\sqrt2\). Top joining forces \(S_4\ge2\mu-\sqrt2\). Thus \(S_4+U_4\ge4\mu-2\sqrt2>1>B\). Hence \(q_4\in C\).

If \(q_2\in C\), its full horizontal chord has length at least \(2\mu-U_2-U_4\), so
\[
B\ge4\mu-L_1-S_2-U_2-U_4.
\]
Using \(S_2+U_2,S_4+U_4\le B\), \(S_4\ge2\mu-L_3\), and \(L_1,L_3\le\sqrt2\), obtain \(3B\ge6\mu-2\sqrt2>3\), impossible. Thus \(q_2\in F\).

If \(q_3\in F\), let \(v_F\) be its full vertical central chord and let \(d_C,r_F\le\mu\) be the downward and rightward target-ray lengths. Covering the four central gaps requires
\[
\sum x_i\le h_C+v_F+d_C+r_F.
\]
Since \(h_C+g_1,v_F+g_2\le B\),
\[
g_1+g_2+\sum x_i\le2B+2\mu<4.
\]
Even allowing corner overlap, covering the grid would require \(12\mu\le\sum T_i+g_1+g_2+\sum x_i<12\), impossible.

Otherwise \(q_3\in C\). The tile also contains \(P=(\mu-S_2,-\mu)\), with \(\mu-S_2>0\). Section 5 gives \(x_3+x_4<1\), whereas
\[
U_3<2-L_3-S_3,\quad U_4\le B-S_4\le B-2\mu+L_3
\]
give \(x_3+x_4>4\mu-2-B+S_3>1\). Both adjacent-gap cases fail.

### 7. A weighted three-ray bound

**Lemma.** A unit square containing \(0,(-x,0),(r,0),(0,y)\), \(x,r,y\ge0\), satisfies \(x+y+3r/4\le2\). No upper bound one on these lengths is assumed.

For projection parameters \(p,q\ge0,p^2+q^2=1\), necessary widths are
\[
A:p(x+r)\le1,\quad B_0:q(x+r)\le1,\quad
C_0:px+qy\le1,\quad D:qr+py\le1.
\]
The axial case follows from horizontal total length and vertical length at most one. For \(p\ge q>0\), use
\[
\alpha=q+p/4,\quad\beta=p-q/4,\quad\gamma=1/p-q-p/4\ge0.
\]
Indeed the numerator for \(\gamma\) is \((q-p/2)^2+p^2/2\). The combination \(\alpha C_0+\beta D+\gamma A\) gives the desired left side and right side \(p+1/p-q/4\le2\), since
\[
(1-p)^2/(pq)\le(\sqrt2-1)^2<1/4.
\]
For \(p<q\), put \(v=p/q\). If \(v\ge1/4\), keep \(\alpha,\beta\) and use \(\gamma=(1-\alpha p)/q\ge0\) with \(B_0\). The right side is
\[
\frac{7+v+3v^2}{4\sqrt{1+v^2}}<2;
\]
after squaring, the difference numerator is
\[
9v^4+6v^3-21v^2+14v-15\le-6v^2+14v-15<0.
\]
If \(v<1/4\), combine \(C_0/q+(1-v)B_0/q\):
\[
x+y+(1-v)r\le(2-v)\sqrt{1+v^2}
\le(2-v)(1+v^2/2)\le2.
\]
Since \(1-v>3/4\), the stated bound follows.

### 8. A ratio bound for a corner leg

For \(c,s>0,c^2+s^2=1\), put \(t=(1-c)/s\in(0,1)\). If \(L\le\min(1/c,1/s)\), then
\[
L-1\le\frac{1-t}{\sqrt2}<\frac34(1-t).
\]
Indeed \(c=(1-t^2)/(1+t^2),s=2t/(1+t^2)\). For \(t\le\sqrt2-1\),
\[
(L-1)/(1-t)\le2t^2/((1-t)^2(1+t))\le1/\sqrt2.
\]
The middle expression increases, as its logarithmic derivative is \(2/t+2/(1-t)-1/(1+t)>0\), and has endpoint value \(1/\sqrt2\). For \(t\ge\sqrt2-1\), the upper bound is \((1-t)/(2t)\le1/\sqrt2\), a decreasing function.

### 9. Exactly one gap

Let the only gap be \(g=2\mu-L_1-S_2>0\), on the bottom, and put the local excess \(\epsilon=2\mu-2>0\). The other three joins and \(T_i<2\) yield
\[
L_2-L_1>3\epsilon+U_3+U_4+U_1,
\quad S_1-S_2>3\epsilon+U_2+U_3+U_4.
\]
Thus \(S_2+\sum U_i<1-3\epsilon\).

Only one central tile can meet the bottom edge. Otherwise \(g+h_C+h_F\le2B\), while \(h_C+h_F+U_2+U_4\ge2\mu\), and the outer-leg sum is at least \(8\mu-g\). These imply \(\sum T_i\ge10\mu-2B+U_1+U_3>8\). Name the unique bottom tile \(C\). It contains the entire gap and \(P=(d,-\mu)\), \(d=\mu-S_2>0\).

Now \(d+x_4,d+x_3>1\). The squared distances to \(q_4,q_3\) are respectively
\[
(d+x_4)^2+\mu^2>2,
\quad d^2+(\mu+x_3)^2=(d+x_3)^2+\mu^2+2x_3(\mu-d)>2,
\]
using \(\mu-d=S_2\ge0\). Thus neither point lies in \(C\). If \(q_2\in C\), then \(g+x_2\le B\), hence \(L_1+S_2+U_2\ge3\mu-B\). With \(T_2<2\), this gives \(L_1-L_2>3\mu-B-2>0\), contrary to the long-leg chain. Therefore \(q_4,q_3,q_2\in F\).

Put \(t_2=(1-c_2)/s_2\). The chain gives \(U_3+U_4<L_2-\mu\), so \(x_3+x_4>3\mu-L_2\). Also \(x_2=\mu-U_2>1-t_2\). Section 8 therefore implies
\[
x_4+x_3+3x_2/4>3\mu-L_2+3(1-t_2)/4>3\mu-1>2,
\]
contradicting Section 7. All possible gap counts are excluded, proving the \(\kappa=0\) assertion.

### 11. Stronger exclusion, shared ownership, and the residual case

The argument actually excludes any G5 covering in which all four midpoints have corner hosts, even if central tiles also contain them. The cyclic matching and all Section 2 constraints persist, and Sections 3--9 require only \(o\in C\cap F\); Section 6 used the weak target bounds \(d_C,r_F\le\mu\). The source records UNSAT for the corresponding weakened linear check; this status is supporting evidence, not an independent premise.

The central tiles cannot share a midpoint. If both contain \(o,m_1\), each meets only the bottom outer edge, by the triangle-area and diameter tests. Their bottom plus horizontal-central contributions total at most \(2B\), and their vertical-central union at most \(2\mu\). Thus their grid union is at most \(2B+2\mu<4\), insufficient with the corner budget eight.

Together with R2, the remaining G5 case has \(\kappa=1\), with only \(C\) containing \(m_1\), \(F\) containing no midpoint, and \(m_1\) having no corner host. Choose distinct corner hosts for \(m_2,m_3,m_4\); call the unselected corner tile \(W\). It may still duplicate one of these midpoints. Up to left-right reflection there are two selective representatives:

1. Near: \(W=V_1\), \(m_2\in V_2,m_3\in V_3,m_4\in V_4\).
2. Far: \(W=V_3\), \(m_2\in V_2,m_3\in V_4,m_4\in V_1\).

These representatives may overlap when midpoint hosts are duplicated. Unselected does not mean midpoint-free.

A local counterexample forbids a universal central grid budget four. For \(\mu=1001/1000\), \(X=x-\mu,Y=y-\mu\), take
\[
C:\quad0\le(924X+43Y)/925+1\le1,\quad0\le(43X-924Y)/925\le1,
\]
\[
F:\quad0\le(119X+120Y)/169+1/2\le1,\quad
0\le(-120X+119Y)/169+1/2\le1.
\]
Both contain \(o\); only \(C\) contains the bottom midpoint. Their six-line-grid union length is exactly
\[
161699957/39732000=4.069766359609383\ldots>4.
\]
The source checked orthogonality, ownership, and interval unions with rational arithmetic. This is a two-tile local example, not a six-tile covering. The residual case requires the posture of \(W\) and central overlap to be coupled. All conclusions here concern G5 only.

<a id="R4"></a>
## R4. Central boundary contacts and reductions of the one-midpoint case

**Scope.** Source: `S6_attack_round4.md`, sections 1--9 and 11. The hypotheses are the actual G5 one-midpoint ownership and a chosen near or far host representative. The conclusions are restricted accordingly. Every corner normalization is a local target-dominating replacement followed by complete reclassification.

### 1. Setup, previous exclusions, and repeated hosts

Use the translated target \([0,2\mu]^2\), \(\mu>1\), with corners, midpoints, and center as in R3. R2--R3 exclude G5 with \(\kappa=0,2\), all four midpoints having corner hosts, and a midpoint shared by \(C,F\). Thus take \(o,m_1\in C\), \(o\in F\), no midpoint in \(F\), and no corner tile containing \(m_1\). The tile \(C\) meets only the bottom outer edge: another adjacent-edge point makes a triangle of area \(\mu^2/2>1/2\) with \(o,m_1\), and the top edge violates diameter.

Choose hosts for \(m_2,m_3,m_4\), with unselected corner \(W\). Up to reflection:

1. Near: \(W=V_1\), \(m_2\in V_2,m_3\in V_3,m_4\in V_4\).
2. Far: \(W=V_3\), \(m_4\in V_1,m_2\in V_2,m_3\in V_4\).

These are selective, potentially overlapping representatives; \(W\) may duplicate a midpoint. For each anchored corner, use the local standard form
\[
L+S+U<2,\quad S+U\le B(\mu)<1,\quad\mu\le L\le\sqrt2,
\]
\[
c,s>0,\quad c^2+s^2=1,\quad cL,sL\le1,
\quad cS+sL=1,\quad sU+\mu c=1.
\]
Here the two-nonempty-parallel-chord bound is
\[
B(d)=\begin{cases}d-\sqrt{d^2-1},&1<d\le3/(2\sqrt2),\\2(\sqrt2-d),&3/(2\sqrt2)\le d\le\sqrt2.\end{cases}
\]
Each corner contributes at most two to the six-line grid. Three anchored corners contribute strictly less than six, so the four-corner total is strictly below eight; using the weak bound eight below is legitimate.

### 2. Boundary restrictions for a central tile

Center the chart at \(o\). A unit tile containing \(o\) and \(P=(d,-\mu)\) cannot meet the top edge or the upper halves of the vertical edges, including their midpoints. For \(Q=(\mu,e)\), \(e\ge0\), if \(d\ge0\), the triangle area is \((\mu^2+de)/2>1/2\); if \(d<0\), both coordinate differences from \(P\) to \(Q\) are at least \(\mu\), the horizontal one strictly larger, so distance exceeds \(\sqrt2\).

More strongly, if \(d>0\), the tile cannot meet any left-edge point \(Q=(-\mu,y)\). For \(y\ge0\), use diameter; for \(y<0\), use area \((\mu^2-dy)/2>1/2\). Reflections and rotations give the corresponding statements. Since \(F\) has no midpoint, any outer-edge chord lies in one open half-edge. A bottom-right contact permits only a right-lower additional outer contact; a bottom-left contact permits only a left-lower one.

### 3. The forced-overlap grid lemma

**Lemma.** Suppose \(C,F\) both contain \(o\) and each meets a horizontal outer edge (the same or opposite edges). If all their vertical-outer-edge chords are already covered by corners, these six tiles cannot cover the target.

Let \(b\) be their total new horizontal-outer contribution and \(h\) their horizontal-central union length. Parallel-chord bounds imply \(b+h\le2B<2\). Their vertical-central union is at most \(2\mu\). With corner budget eight, full grid coverage would imply
\[
12\mu\le8+b+h+2\mu<10+2\mu<12\mu,
\]
using \(\mu>1\). Redundancy of the vertical boundary chords is a required hypothesis, not an automatic property of central tiles.

### 4. The far representative: no bottom contact by F

The anchors are \(m_4\in V_1,m_2\in V_2,m_3\in V_4\), \(W=V_3\). If \(F\) meets the bottom, its possible vertical boundary contacts lie in the lower halves, already covered by the long chords of \(V_1,V_2\). The tile \(C\) meets only the bottom. Section 3 excludes this case for every target side \(2\mu>2\), replacing the earlier conditional bound \(2\mu<2.0067403338\). Duplicated midpoint hosts by \(W\) remain allowed.

### 5. The near representative: no bottom contact by F

Here \(W=V_1\), with anchors \(m_2\in V_2,m_3\in V_3,m_4\in V_4\). A bottom-right contact of \(F\) permits only a lower-right vertical boundary chord, already covered by \(V_2\); Section 3 applies.

If \(F\) meets the bottom-left half, it misses the right and top edges. Since \(C\) also misses these edges,
\[
L_2+S_3\ge2\mu,\qquad L_3+S_4\ge2\mu.
\]
Put \(\epsilon=2\mu-2>0\). The corner budgets imply
\[
S_3-S_2>\epsilon+U_2,\quad S_4-S_3>\epsilon+U_3,
\qquad U_2+U_3<1.
\]
The central endpoints \(q_2=(\mu-U_2,0)\), \(q_3=(0,\mu-U_3)\) must lie in \(C\cup F\), by approaching from beyond the corner intervals and using closedness. The lower-left corner \(W\) is farther than \(\sqrt2\) from either positive central endpoint, irrespective of duplicate midpoint ownership.

Because \(W\) misses \(m_1\) and \(F\) misses the bottom-right half, \(C\) covers the entire bottom segment from \(m_1\) to the short leg of \(V_2\); its bottom chord \(l_C\ge\mu-S_2\). If \(q_2\in C\), then its horizontal central chord \(h_C\ge\mu-U_2\), giving
\[
B\ge l_C+h_C\ge2\mu-S_2-U_2\ge2\mu-B,
\]
contradicting \(B<1<\mu\). Thus \(q_2\in F\).

The reflected three-point lemma R3.5 says that a tile containing \((-d,-\mu),(r,0),(0,u)\), \(d,r,u\ge0\), has \(r+u<1\). Hence \(F\) cannot also contain \(q_3\), because \(2\mu-U_2-U_3>1\). But \(q_3\in C\) would force \(U_3\ge2\mu-\sqrt2\) by diameter from \(m_1\), while right joining gives \(S_3\ge2\mu-\sqrt2\). Thus \(S_3+U_3\ge4\mu-2\sqrt2>1\), also impossible. This excludes bottom contact in both representatives.

### 6. Further near-case reductions

Assume now \(F\) misses the bottom. The same bottom-chord argument always gives \(q_2\notin C\), hence \(q_2\in F\), independently of its other contacts.

If \(F\) meets the left-lower half at \((-\mu,-d)\), \(d>0\), it misses right and top. Their corner joins give \(U_2+U_3<1\). The coordinate-exchanged three-point lemma says that its right and upper reaches sum to less than one. Since it contains \(q_2\), it cannot contain \(q_3\); the preceding diameter argument excludes \(q_3\in C\). Therefore \(F\) misses the left-lower half. If \(A,D\) are the bottom and left legs of \(W\), then
\[
A<\mu,\qquad D+L_4\ge2\mu.
\]
The possibility \(D\ge\mu\), a duplicated left midpoint, is retained.

If \(F\) meets the top-left half at \((-d,\mu)\), it misses the right edge by Section 2. It also misses the left-lower half, since a left-lower point \((-\mu,-e)\) would form a center triangle of area \((\mu^2+de)/2>1/2\). Its only possible vertical boundary contribution lies in the left-upper half, already covered by \(V_4\). Section 3 excludes this case. Since \(V_3\) covers the top-right half, any top corner gap lies in the top-left half and could no longer be filled. Therefore \(L_3+S_4\ge2\mu\).

Two near shapes remain: either a right-upper corner gap is entirely filled by \(F\), with top and left joined, or all three top/right/left edges are joined and all other boundary contributions of \(F\) are redundant. In the latter shape, top-right contact also satisfies Section 3, so \(F\) must miss the entire top edge.

### 7. Stronger corner inequalities and exact angle elimination

The standard form with \(L\ge\mu>1\) gives
\[
S<(1-s)/c,\qquad U<(1-c)/s.
\]
The two right sides \(a_0,b_0\) satisfy \(a_0+b_0+a_0b_0=1\): with \(t=(1-c)/s\), \(a_0=(1-t)/(1+t),b_0=t\). Consequently
\[
S+U+SU<1.
\]
R3.8 gives \(L-1\le(1-t)/\sqrt2\), while \(U<t\). Hence
\[
L+U/\sqrt2<1+1/\sqrt2,
\qquad L+3U/4<7/4.
\]
The second follows using \(U<1\). The source records independent nonlinear real checks of both versions. Also \(L\le\mu+U\): if \(c\ge s\), \(cL\le1\) implies \(U\ge(c/s)(L-\mu)\ge L-\mu\); if \(c<s\),
\[
sU-s(L-\mu)=1-sL+\mu(s-c)\ge0.
\]
This last bound was used only in exploratory models.

Define \(D_0=\mu L-SU\). The two exact standard-form equations imply
\[
cD_0=L-U,\quad sD_0=\mu-S,
\quad(\mu L-SU)^2=(L-U)^2+(\mu-S)^2,
\]
and \(L(L-U)\le\mu L-SU\). The quantities \(D_0,L-U,\mu-S\) are positive; recovering \(c=(L-U)/D_0,s=(\mu-S)/D_0\) restores the unit direction. Symbolic identities were checked in the source. The remaining model with these exact constraints was still UNKNOWN; no exclusion follows from that status.

### 8. Linear, parabolic, and optimal weighted three-ray bounds

**Lemma.** A unit square containing \(o,(-l,0),(r,0),(0,u)\), \(l,r,u\ge0\), with \(H=l+r\), satisfies
\[
H+u\le3/\sqrt2,\qquad H+u^2\le2.
\]
The necessary and sufficient width conditions, for some \(p,q\ge0,p^2+q^2=1\), are
\[
pH,qH\le1,\quad pl+qu\le1,\quad qr+pu\le1.
\]
Exchange \(p,q\) and \(l,r\) to assume \(p\ge q\). For \(q=0\), \(H,u\le1\). Otherwise \(p\in[1/\sqrt2,1\)), and dividing the last two inequalities by \(p,q\) gives
\[
H\le\min\{1/p,(p+q-u)/(pq)\},\qquad u\le1/p.
\]
For \(u\le p\), \(H+u\le1/p+p\le3/\sqrt2\); for \(u\ge p\), the other bound makes \(H+u\) decrease with \(u\), giving the same result.

For the parabola, \(u\le p\) yields \(H+u^2\le1/p+p^2\le2\), equivalent to \((p-1)(p^2+p-1)\le0\). For \(p\le u\le1/p\), the expression \((p+q-u)/(pq)+u^2\) is convex, so it suffices to check the endpoints. The \(p\) endpoint was handled. At \(1/p\) its value is \((1+p-q)/p^2\le2\), since
\[
p\le1+q-2q^2,
\]
whose nonnegative sides have squared difference \(2q(1-q)(1-2q^2)\ge0\).

The optimal weighted inequality is
\[
l+u+(2\sqrt2-2)r\le2.
\]
Put \(\delta=3-2\sqrt2\), and name the four widths \(A,B_0,C_0,D_0\) in their displayed order. Axial directions are immediate. For \(p\ge q>0\), the nonnegative combination
\[
(q+\delta p)C_0+(p-\delta q)D_0+(1/p-q-\delta p)A
\]
has the desired left side and right side \(p+1/p-\delta q\le2\), because \((1-p)^2/(pq)\le(\sqrt2-1)^2=\delta\). For \(p<q\), put \(v=p/q\). If \(v\ge\delta\), replace the final term by \((1-(q+\delta p)p)B_0/q\). Its right side is
\[
f(v)=\frac{2-\delta+\delta v+(1-\delta)v^2}{\sqrt{1+v^2}}.
\]
The derivative numerator is \(\delta(1-v)+(1-\delta)v^3\ge0\), so \(f(v)\le f(1)=(3-\delta)/\sqrt2=2\). If \(v<\delta\), the combination \(C_0/q+(1-v)B_0/q\) gives \(l+u+(1-v)r\le(2-v)\sqrt{1+v^2}\le2\), which suffices. Equality at \(p=q,l=r=u=1/\sqrt2\) proves optimality of the coefficient. The source also records an UNSAT counterexample query; the continuous proof is the displayed argument.

### 9. Redundancy of C inside the near three-join shape

Restrict to the second shape of Section 6. Let \(H_W\) be the horizontal-central chord length of \(W\); write \(C_L,C_R,C_U\) and \(F_L,F_R,F_U\) for left, right, and upper central reaches. Then
\[
A+D+H_W\le2,\quad g=2\mu-A-S_2>0,
\quad C_L+C_R+g\le B.
\]
The joins are \(L_2+S_3,L_3+S_4,D+L_4\ge2\mu\). If \(F_L\le C_L\), left-central coverage would require \(C_L+U_4+H_W\ge\mu\). But
\[
\begin{aligned}
C_L+U_4+H_W
&\le B-2\mu+A+S_2+H_W+U_4\\
&\le B-2\mu+2-D+S_2+U_4\\
&\le B-4\mu+2+L_4+S_2+U_4\\
&<B-4\mu+4+S_2-S_4\\
&<B-4\epsilon-U_2-U_3<1<\mu.
\end{aligned}
\]
Here \(S_4-S_2>2\epsilon+U_2+U_3\). Thus \(F_L>C_L\). Section 6 gives \(F_R\ge\mu-U_2>C_R\). Right joining alone excludes \(q_3\in C\), since it would force both \(S_3,U_3\ge2\mu-\sqrt2\); hence \(F_U\ge\mu-U_3>C_U\).

Both central tiles contain \(o\). Therefore the entire horizontal chord and upper ray of \(C\) are contained in \(F\). The downward target half-segment is fully in \(C\), length \(\mu\); any contributions there from \(F,W\) are redundant. The only new grid contributions of \(C\) are its bottom gap \(g\) and that downward half-segment.

### 11. The remaining far-case entrance

In the far representative, \(F\) misses the bottom. Its two corner short legs are \(S_1,S_2\), so \(C\) covers \(g=2\mu-S_1-S_2\). If \(C\) contained the left central endpoint \(q_1=(-(\mu-U_1),0)\), then
\[
B\ge g+h_C\ge3\mu-(S_1+U_1)-S_2\ge3\mu-2B,
\]
forcing \(B\ge\mu\). Neither the upper-right corner \(W\) nor the top-anchored \(V_4\) can cover this endpoint. Closedness forces \(q_1\in F\). This provides a left ray in \(F\); the assistance by \(W\) to right/upper central segments and any duplicate midpoint host remain to be analyzed. No full far-case exclusion is asserted here.

<a id="R5"></a>
## R5. Excluding the near representative with three joined outer edges

**Scope.** Source: `S6_attack_round5.md`, sections 1--7. This excludes the G5 one-midpoint near representative when top, right, and left corner intervals join. The argument retains all possible repeated midpoint ownership by the free corner and uses only the actual post-replacement branch.

### 1. Geometric hypotheses and input lemmas

Use the translated chart \([0,2\mu]^2\), \(\mu>1\), with \(V_1,V_2,V_3,V_4\) in lower-left, lower-right, upper-right, upper-left order. The center belongs to \(C,F\); the actual central midpoint count is \(\kappa=1\). By R2--R4, take \(C\) containing the bottom midpoint, \(F\) containing no midpoint, and no corner containing the bottom midpoint. In the near selective representative, \(V_2,V_3,V_4\) host respectively right, top, left midpoints, and \(W=V_1\) is unselected. It may duplicate a selected midpoint.

R4 proves that \(C\) meets only the bottom outer edge, and \(F\) misses bottom, left-lower, and top-left half-edges. Left and top corners join. Assume right corners join as well. The three anchored corners have
\[
L_i\ge\mu>1,\ L_i\le\sqrt2,\quad c_i,s_i>0,\ c_i^2+s_i^2=1,
\quad c_iL_i,s_iL_i\le1,
\]
\[
c_iS_i+s_iL_i=1,\quad s_iU_i+\mu c_i=1,
\quad L_i+S_i+U_i<2,
\quad S_i+U_i\le B(\mu)<1,
\quad L_i+3U_i/4<7/4.
\]
The parallel-chord function \(B\) is that of R2, for two nonempty lines separated by \(1<d\le\sqrt2\):
\[
B(d)=\begin{cases}
d-\sqrt{d^2-1},&1<d\le3/(2\sqrt2),\\
2(\sqrt2-d),&3/(2\sqrt2)\le d\le\sqrt2.
\end{cases}
\]
Let \(A,D,H\) be the bottom leg, left leg, and actual horizontal-central chord length of \(W\). Then \(A<\mu\), \(A+D+H\le2\). The horizontal chord lies in the left target half but is allowed to float. The joins are
\[
L_2+S_3\ge2\mu,\quad L_3+S_4\ge2\mu,\quad D+L_4\ge2\mu.
\]
Center at \(o\). R4.9 proves that the horizontal chord and upward ray of \(C\) are redundant inside \(F\). Thus the left, right, upper reaches \(l,r,u\ge0\) of \(F\) must satisfy
\[
l\ge\mu-U_4-H,\quad r\ge\mu-U_2,\quad u\ge\mu-U_3.
\]
These are length necessities; \(H\) is not assumed attached to the boundary. R4.8 gives
\[
l+u+3r/4\le2,\qquad l+r+u^2\le2.
\]

### 2. The free corner has bottom leg less than one

Put \(\epsilon=2\mu-2>0\). Top and left joining, with the strict corner budgets, imply
\[
S_4>S_3+U_3+\epsilon,
\quad D>S_4+U_4+\epsilon>S_3+U_3+U_4+2\epsilon.
\]
Consequently
\[
H+U_3+U_4<2-A-S_3-2\epsilon\le L_2-A-3\epsilon.
\]
The rays of \(F\) therefore obey
\[
\begin{aligned}
l+u+3r/4
&\ge11\mu/4-H-U_4-U_3-3U_2/4\\
&>11\mu/4+A+3\epsilon-(L_2+3U_2/4)\\
&>11\mu/4+A+3\epsilon-7/4.
\end{aligned}
\]
If \(A\ge1\), the last expression exceeds two. Thus \(A<1\).

### 3. The central chord of W is shorter than the short bottom leg of V2

The bottom gap is entirely in \(C\), with \(g=2\mu-A-S_2>0\). Since \(C\) meets both bottom and horizontal central lines, \(g\le B<1\); hence \(A+S_2\ge2\mu-B>1\). If \(H=0\), \(A<1\) gives \(S_2>H\). If \(H>0\), the two nonempty parallel chords of \(W\) give \(A+H\le B<1<A+S_2\). Thus always
\[
H<S_2.
\]

### 4. Two cascades of half-angle bounds

Define
\[
t_i=(1-c_i)/s_i\in(0,1),\quad c_i=(1-t_i^2)/(1+t_i^2),
\quad s_i=2t_i/(1+t_i^2).
\]
Since \(\mu,L_i>1\),
\[
U_i<t_i,\quad S_i<\frac{1-t_i}{1+t_i},\quad
L_i\le\min\left\{\frac{1+t_i^2}{1-t_i^2},\frac{1+t_i^2}{2t_i}\right\}.
\]
Set \(L=L_2,t=t_2\). To avoid conflict with the global midpoint count, denote the source's auxiliary ratio by \(\rho\):
\[
\rho=\frac{L-1}{3-L}>0,\qquad L=1+\frac{2\rho}{1+\rho}.
\]
From \(L\le\sqrt2\), \(\rho<4/15\): this is equivalent to \(19\sqrt2<27\), whose squared comparison is \(722<729\). Right joining gives \(t_3<\rho\). Top joining gives \(t_4<(L_3-1)/(3-L_3)\). Since \(t_3<\rho<4/15\), the cosine leg bound yields
\[
\frac{L_3-1}{3-L_3}\le\frac{t_3^2}{1-2t_3^2},
\qquad t_4<\frac{\rho^2}{1-2\rho^2}=:w.
\]
All denominators are positive, and the rational function of \(t_3\) is increasing on this domain.

### 5. Reduction to one inequality on the full physical domain

Sections 3--4 imply
\[
l>1-S_2-w,\quad r>1-t,\quad u>1-\rho>0.
\]
The first lower bound remains valid even if negative; the last is positive and can be squared. Hence
\[
l+r+u^2>2+\Phi(t,\rho),
\]
where
\[
\Phi=1-S_2-t-2\rho+\rho^2-\frac{\rho^2}{1-2\rho^2}.
\]
The exact standard-form identity is \(S_2=(1+t^2-2tL)/(1-t^2)\). Substitution gives
\[
\Phi=\frac{t(1-t)}{1+t}+\frac{4t\rho}{(1-t^2)(1+\rho)}
-2\rho-\frac{2\rho^4}{1-2\rho^2}.
\]

### 6. Concavity and exact polynomial positivity

Define
\[
\Psi=\frac{t(1-t)}{1+t}+\frac{4t\rho}{(1-t^2)(1+\rho)}-2\rho-\rho^2/6.
\]
Because \(0<\rho<4/15\), \(\rho^2<1/14\), and
\[
\Phi-\Psi=\frac{\rho^2(1-14\rho^2)}{6(1-2\rho^2)}>0.
\]
For fixed \(0<t<1\),
\[
\partial_\rho^2\Psi=-\frac{8t}{(1-t^2)(1+\rho)^3}-1/3<0.
\]
It suffices to prove positivity at both ends of any allowed interval \(0\le\rho\le K\). The zero endpoint is \(\Psi(t,0)=t(1-t)/(1+t)>0\).

#### 6.1. Small half-angles and the cosine leg bound

For \(0<t\le5/12\), take \(K_c=t^2/(1-2t^2)\), as supplied by the cosine leg bound. Direct substitution gives
\[
\Psi(t,K_c)=\frac{-tP(t)}{6(1-t)^2(1+t)^2(1-2t^2)^2},
\]
\[
P(t)=24t^8-71t^7-120t^6+154t^5+78t^4-107t^3+24t-6.
\]
On \(0\le x\le1\), the exact Bernstein expansion of \(-P(5x/12)\) has degree eight and coefficients
\[
\left(6,\frac{19}4,\frac72,\frac{231103}{96768},\frac{24503}{16128},
\frac{6477551}{6967296},\frac{1002889}{1741824},
\frac{104107099}{286654464},\frac{7742393}{35831808}\right).
\]
That is, \(-P(5x/12)=\sum_{j=0}^8b_j\binom8j x^j(1-x)^{8-j}\). All \(b_j>0\); the nonnegative basis sums to one, including both endpoints. Thus \(-P>0\), and the displayed denominator is positive.

#### 6.2. Large half-angles and the sine leg bound

For \(2/5\le t<1\), take \(K_s=(1-t)^2/(6t-1-t^2)>0\). Then
\[
\Psi(t,K_s)=\frac{(1-t)Q(t)}{6(t^2-6t+1)^2},
\quad Q(t)=6t^4-83t^3+309t^2-153t+17.
\]
On \([2/5,1]\), \(Q'''=144t-498<0\), so \(Q''\ge Q''(1)=192>0\). Thus \(Q'\) increases and \(Q'(2/5)=6987/125>0\), whence \(Q\) increases and \(Q(2/5)=51/625>0\). Therefore this endpoint is positive too. The two intervals cover \((0,1)\), overlapping on \([2/5,5/12]\), so concavity proves \(\Psi>0\), and hence \(\Phi>0\), throughout the physical domain.

### 7. Contradiction and surviving shape

Now \(l+r+u^2>2+\Phi>2\), contrary to the unit-square parabolic bound. Thus the G5 near representative with top, right, and left joins cannot cover a square of side \(2\mu>2\). No global numerical upper bound such as \(2.03\), nor the earlier conditional \(2.0072358858\), is used.

Any remaining near representative has a right-upper corner gap, entirely covered by \(F\); top and left join, and \(C\) fills the bottom gap. The far representative has \(F\) avoiding bottom but is not yet excluded by this module. No conclusion for G1--G4 is asserted.

<a id="R6"></a>
## R6. Exclusion of every near G5 one-midpoint representative

**Scope.** Source: `S6_attack_round6.md`, sections 1--8. R5 excludes the near three-join shape; this module excludes its remaining right-upper gap. Singleton tangency is included in the new chord lemma. All roles and gaps refer to the actual representative after any local replacement.

### 1. Configuration and inherited inputs

Use the translated target \([0,2\mu]^2\), \(\mu>1\), with corners \(V_1,V_2,V_3,V_4\) in the usual order. In G5 both \(C,F\) contain the center. In the remaining \(\kappa=1\) case, \(C\) contains the bottom midpoint, \(F\) no midpoint, and no corner contains the bottom midpoint. The near selection is \(m_2\in V_2,m_3\in V_3,m_4\in V_4\), \(W=V_1\); duplicate ownership by \(W\) remains allowed.

R4 gives: \(C\) meets only bottom; \(F\) misses bottom, left-lower, and top-left half-edges; top and left corners join. Assume a right-upper gap, since R5 excludes right joining. For \(i=2,3,4\),
\[
\mu\le L_i\le\sqrt2,\ S_i,U_i\ge0,\quad
L_i+S_i+U_i<2,\quad S_i+U_i\le B(\mu)<1.
\]
Here \(B\) is R2's sharp bound for two nonempty parallel chords. Let \(A,D,H\) be the bottom leg, left leg, and actual horizontal-central target chord of \(W\). This chord may float in the left half. Then \(A+D+H\le2,A<\mu\). With local excess \(\epsilon=2\mu-2>0\), the joins \(L_3+S_4,D+L_4\ge2\mu\) imply
\[
S_4>S_3+U_3+\epsilon,\quad D>S_3+U_3+U_4+2\epsilon,
\quad A+H+U_3+U_4<2-S_3-2\epsilon.
\]
The right and bottom gaps are
\[
d=2\mu-L_2-S_3>0,\qquad g=2\mu-A-S_2>0.
\]
They belong entirely to \(F,C\), respectively, including endpoints by closedness. The full right-edge chord of \(F\) lies in its upper half; otherwise convexity would give the right midpoint. Center the chart. Write \(C_L,C_R,C_U\) and \(l,r,u\) for the left, right, upper reaches of \(C,F\). Since these tiles avoid side and top midpoints, these full ray lengths stay within their target half-segments.

### 2. A boundary--central chord lemma

**Lemma.** Let a unit tile \(Q\) contain the origin, meet the positive half of \(x=\mu>1\), and omit \((\mu,0)\). If \(d_0\) is its full chord length there and \(l,r,u\) its left, right, upper reaches, then
\[
l+r+u+d_0<2.
\]
Consequently any gap length \(d\le d_0\) can replace \(d_0\).

#### 2.1. Exact chord formulae, including tangency

Choose \(c,s>0,c^2+s^2=1\), and write
\[
-\alpha\le cx+sy\le1-\alpha,\quad
-\beta\le-sx+cy\le1-\beta,\quad0\le\alpha,\beta\le1.
\]
An axial tile cannot contain zero and reach \(x=\mu>1\). Positive-height right contact gives \(1-\alpha>c\mu\), and omission of the right midpoint is equivalent to \(\beta<s\mu\). Thus \(r=\beta/s<\mu\). The lower endpoint on \(x=\mu\) is \((s\mu-\beta)/c>0\), and the upper endpoint is \((1-\alpha-c\mu)/s\): the other possible upper bound is inactive because
\[
c(1-\alpha)+s\beta-s\le c<\mu.
\]
Hence
\[
d_0=\frac{c(1-\alpha)+s\beta-\mu}{sc}\ge0.
\]
The weak sign is essential: a singleton tangent chord is permitted. Since \(c(1-\alpha)+s\beta\ge\mu>1\ge s\), the upper central ray is \(u=(1-\beta)/c\). Also \(l\le\alpha/c\) and \(l\le(1-\beta)/s\). If \(T=l+r+u+d_0\), then
\[
T=r+1/s+1/c-\mu/(sc)+l-\alpha/s.
\]

#### 2.2. Both direction orders

If \(c\ge s\), \(l-\alpha/s\le0\), so \(T\le r+1/s+1/c-\mu/(sc)\). For \(r\le1\), use \(\mu>1\). For \(r\ge1\), use \(\mu>r\), with the resulting expression decreasing in \(r\) because \(1-1/(sc)<0\). Both give
\[
T<1+(c+s-1)/(sc)<2,
\]
the last step being \((1-c)(1-s)>0\).

If \(c<s\), \(\alpha\ge cl\) and \(l\le(1-\beta)/s\) yield
\[
l-\alpha/s\le(1-sr)(s-c)/s^2,
\quad T\le(c/s)r+2/s+1/c-c/s^2-\mu/(sc).
\]
Split again at \(r=1\), using \(\mu>1\) or \(\mu>r\); in the latter case the coefficient is \(-s/c<0\). Thus \(T<Z=c/s+2/s+1/c-c/s^2-1/(sc)\). Exactly,
\[
(Z-2)s^2c=(1-s)(-c^2+2cs-s)
=-(1-s)((s-c)^2+s(1-s))<0.
\]
This proves the strict inequality throughout the continuous angle domain, with \(d_0=0\) allowed.

### 3. The one-sided long-chord budget of C

Apply R2's three-section lemma with the bottom midpoint as first anchor and the center as second, taking only the left central ray. The bottom chord has length at least \(g\), and the upward anchored ray has length \(\mu+C_U\). Therefore
\[
g+\mu+C_U+C_L<2.
\]
This counts one central side only; adding both sides unconditionally is invalid. Separately, parallel chords give \(g+C_L+C_R\le B\).

### 4. The right central endpoint belongs to F

Closedness and coverage force \(q_2=(\mu-U_2,0)\in C\cup F\); other corners cannot fill the points just beyond its anchored short segment. The bottom chord of \(C\) has length at least \(\mu-S_2\). If \(q_2\in C\), its horizontal chord has length at least \(\mu-U_2\), implying
\[
B\ge2\mu-S_2-U_2\ge2\mu-B,
\]
impossible. Hence \(r\ge\mu-U_2>C_R\).

The upper endpoint \(q_3=(0,\mu-U_3)\) also belongs to \(C\cup F\). The lower-left \(W\) is too far from it; the long anchors of \(V_2,V_4\) exclude the vertical central line; \(V_3\) covers only its upper short segment. Treat \(q_3\in F\) and \(q_3\in C\) separately, allowing simultaneous membership.

### 5. If the upper endpoint is in F, C cannot dominate on the left

Here \(u\ge\mu-U_3\). The right-edge and vertical-central lines are parallel, so \(d+u\le B<1\), hence \(d<U_3\). If \(l\le C_L\), left-central coverage requires \(C_L+U_4+H\ge\mu\), whereas
\[
\begin{aligned}
C_L+U_4+H&\le B-2\mu+A+S_2+U_4+H\\
&<B+S_2-S_3-U_3-3\epsilon.
\end{aligned}
\]
Since \(d=2\mu-L_2-S_3\) and \(L_2+S_2+U_2<2\), we have \(S_3-S_2>\epsilon+U_2-d\). Therefore
\[
C_L+U_4+H<B-4\epsilon-U_2+d-U_3<B<1<\mu,
\]
a contradiction. Thus \(l>C_L\).

### 6. If the upper endpoint is in C, the same dominance fails

Now \(C_U\ge\mu-U_3\). If \(l\le C_L\), coverage gives \(C_L\ge\mu-U_4-H\). Then
\[
\begin{aligned}
2&>g+\mu+C_U+C_L\\
&\ge g+3\mu-U_3-U_4-H\\
&=5\mu-A-S_2-U_3-U_4-H\\
&>5\mu-2+S_3-S_2+2\epsilon\\
&>5\mu-3+2\epsilon=9\mu-7>2.
\end{aligned}
\]
The penultimate bound uses \(S_2<1,S_3\ge0\). Hence again \(l>C_L\). Both branches establish \(l>C_L,r>C_R\); since the central chords are intervals through zero, the entire horizontal chord of \(C\) is contained in \(F\).

### 7. The grid contradiction after removing redundancy

The six grid segments total \(12\mu\), and corners contribute at most eight. After deleting its redundant horizontal chord, \(C\) contributes at most \(g+\mu+C_U<2\). The length \(\mu\) is the full downward half-segment, present by convexity from the center to its bottom midpoint.

The downward central part of \(F\) is redundant in that half-segment. Right-upper contact prevents its meeting left or bottom; any top chord lies in the top-right half already covered by \(V_3\). Its only new right-edge contribution is the gap \(d\). By Section 2 its remaining contribution is at most \(l+r+u+d<2\). Counting any remaining upper-central overlap twice only weakens the upper bound. Thus
\[
12\mu\le8+(g+\mu+C_U)+(l+r+u+d)<12<12\mu,
\]
impossible. With R5, every near G5 one-midpoint representative is excluded.

### 8. Consequences for actual far-case ownership

The four possible distinct selective hosts for right, top, left midpoints are
\[
(2,3,4),\quad(2,3,1),\quad(2,4,1),\quad(3,4,1).
\]
The first and fourth are reflected near representatives and are excluded. Thus in any survivor, the right midpoint belongs only to \(V_2\), the left only to \(V_1\), while the top may belong to \(V_3,V_4\), or both. Selecting \(V_4\) as top host makes \(W=V_3\). If this \(W\) also contained the right midpoint, selection \((3,4,1)\) would give an excluded near representative. Its duplicate top ownership remains possible. This is an ownership reduction, not yet a far-case exclusion; floating central assistance from \(W\) remains to be controlled.

<a id="R7"></a>
## R7. Boundary exclusion and redundancy in the far G5 representative

**Scope.** Source: `S6_attack_round7.md`, sections 1--4. This derives structural conditions for the last G5 representative. It does not alone exclude that representative. Actual repeated top-midpoint ownership and floating central chords of the free corner are retained.

### 1. Far-case notation and the forced left ray

Use the translated target \([0,2\mu]^2\), \(\mu>1\). The central tiles \(C,F\) both contain \(o\); \(C\) contains the bottom midpoint, \(F\) no midpoint, and no corner contains the bottom midpoint. R6 leaves only actual left host \(V_1\) and right host \(V_2\); top may have hosts \(V_3,V_4\). Select \(V_4\) as top host, \(W=V_3\). Then \(W\) misses the right midpoint but may duplicate the top midpoint and may have floating central chords.

For \(i=1,2,4\), anchored lengths satisfy
\[
L_i+S_i+U_i<2,\quad S_i+U_i\le B(\mu)<1,
\quad\mu\le L_i\le\sqrt2.
\]
The tile \(C\) meets only bottom and \(F\) misses bottom. The entire bottom gap \(g=2\mu-S_1-S_2>0\) lies in \(C\).

Center the chart and denote the central reaches by \(C_L,C_R,C_U\) and \(l,r,u\). The left central endpoint \(q_1=(-(\mu-U_1),0)\) must lie in \(C\cup F\): \(W\) and the other bottom corner are too far; the long top anchor of \(V_4\) excludes the horizontal central line; use closedness beyond the short corner segment. If it lay in \(C\), then
\[
B\ge g+h_C\ge3\mu-(S_1+U_1)-S_2\ge3\mu-2B,
\]
forcing \(B\ge\mu\). Therefore \(l\ge\mu-U_1>C_L\). Thus the left ray of \(C\) is redundant in \(F\). The long-chord three-section lemma, anchored at bottom midpoint and center and using the right central ray, gives
\[
g+\mu+C_U+C_R<2.
\]
This already bounds the effective contribution of \(C\), without first proving right-ray redundancy. The same one-sided observation can shorten the near proof in R6.

### 2. Upper boundary chord bounds, with tangency included

Let \(Q\) contain zero but omit right and top midpoints. Let \(H=l+r\) be its full horizontal central chord and \(u\) its upper reach. R6 gives \(H+u+d_r<2\) for positive-height right contact, including \(d_r=0\); reflection handles left-upper contact. We now show
\[
H+u+d_t<2,
\qquad H+u+d_r+d_t<2
\]
for top-right contact, or simultaneous top-right and right-upper contact, respectively.

#### 2.1. A top boundary chord

Write
\[
-\alpha\le cx+sy\le1-\alpha,\quad-\beta\le-sx+cy\le1-\beta,
\quad c,s>0,\ c^2+s^2=1,\quad0\le\alpha,\beta\le1.
\]
Axial tiles cannot reach an outer line at distance \(\mu>1\) from zero. Top-right contact implies \(1-\alpha>s\mu\); omission of the top midpoint gives \(\beta>1-c\mu\). Its full top chord has endpoints
\[
(c\mu-1+\beta)/s>0,\qquad(1-\alpha-s\mu)/c,
\]
and length
\[
d_t=\frac{s(1-\alpha)+c(1-\beta)-\mu}{sc}\ge0.
\]
This gives \(s(1-\alpha)+c(1-\beta)\ge\mu>1\ge c\), so
\[
r=\beta/s,\quad u=(1-\beta)/c<\mu,\quad l\le\alpha/c.
\]
Consequently
\[
H+u+d_t=u+1/s+1/c-\mu/(sc)+l-\alpha/c
\le u+1/s+1/c-\mu/(sc).
\]
For \(u\le1\), use \(\mu>1\); for \(u\ge1\), use \(\mu>u\) and the negative coefficient \(1-1/(sc)\). Both yield \(H+u+d_t<1+(c+s-1)/(sc)<2\).

#### 2.2. Two adjacent upper boundary chords

For an additional right-upper contact,
\[
d_r=\frac{c(1-\alpha)+s\beta-\mu}{sc}\ge0.
\]
The same \(r,u\) formulae apply, and
\[
H+u+d_r+d_t=l+(2-\alpha)(1/s+1/c)-2\mu/(sc)
\le\frac{2(c+s-\mu)}{sc}-\alpha/s<2.
\]
Here \(\mu>1\) and \(c+s-1<cs\). Both boundary chord lengths may be zero. Contacts on top and an upper side must surround the same upper corner: points \((\mu,d),(-e,\mu)\), \(d,e>0\), would give a center triangle of area \((\mu^2+de)/2>1/2\). Reflection gives all left versions.

### 3. The far tile F has no outer boundary contact

#### 3.1. Top or upper-side contact

Because \(F\) omits all midpoints, each outer chord lies in an open half-edge. If it meets top or an upper side, the central-contact restrictions exclude lower-side and bottom contact. At most a top chord and one same-side upper chord remain; opposite sides are too far apart. Section 2 therefore bounds its full horizontal chord, upper ray, and all available boundary chords by a strict total two.

Its lower central ray is already covered by the bottom-midpoint--center segment of \(C\). The left ray of \(C\) is redundant in \(F\); Section 1 bounds its remainder by two. With corner budget eight, full grid coverage would force \(12\mu<8+2+2=12\), impossible. This includes tangent boundary contacts of length zero.

#### 3.2. Lower-side contact

If \(F\) meets \((-\mu,-d)\), \(d>0\), it misses right by diameter, top by the center triangle/diameter restriction, and bottom by R4. Its only outer contribution, on the left-lower half, is already covered by the long leg of \(V_1\). The exchanged R3.5 lemma yields \(r+u<1\), while omission of the left midpoint gives \(l<\mu\). Thus its effective internal contribution is \(l+r+u<\mu+1\). The right-lower case gives \(l+u<1,r<\mu\), with its outer chord covered by \(V_2\). Either case would require
\[
12\mu<8+2+(\mu+1)=11+\mu<12\mu.
\]
All contacts have been exhausted. Hence \(F\) misses the four target edges entirely. Since it contains zero and is convex, a point outside the target would force an edge intersection. The whole tile \(F\) therefore lies in the target's open interior.

### 4. Three join chains and the remaining redundancy of C

Neither \(C\) nor \(F\) can fill left, right, or top gaps; their corners must join. Let \(A,D\) be the right and top legs of \(W\), and \(H,J\) its actual horizontal-right and vertical-upper central chord lengths. These may float. Then
\[
A<\mu,\quad A+D+H+J\le2,
\quad L_1+S_4,L_2+A,L_4+D\ge2\mu.
\]
Duplicate top ownership \(D\ge\mu\) remains allowed. Put \(\epsilon=2\mu-2>0\). The strict budgets give
\[
S_4>S_1+U_1+\epsilon,
\quad D>S_1+U_1+U_4+2\epsilon,
\quad A>S_2+U_2+\epsilon,
\]
\[
H+J+S_1+S_2+U_1+U_2+U_4<2-3\epsilon.
\]
If \(r\le C_R\), right-central coverage requires \(C_R+U_2+H\ge\mu\). Section 1, even dropping \(C_U\ge0\), gives
\[
2>g+\mu+C_R\ge4\mu-S_1-S_2-U_2-H
>4\mu-2+3\epsilon>2.
\]
Thus \(r>C_R\). Similarly, if \(u\le C_U\), upper coverage requires \(C_U+U_4+J\ge\mu\), and
\[
2>g+\mu+C_U\ge4\mu-S_1-S_2-U_4-J
>4\mu-2+3\epsilon>2.
\]
Thus \(u>C_U\). Together with \(l>C_L\), this places the entire horizontal chord and upper ray of \(C\) in \(F\). Its only effective new grid contributions are bottom gap \(g\) and downward half-segment \(\mu\).

<a id="R8"></a>
## R8. The final far-case inequality and exclusion of G5

**Scope.** Source: `S6_attack_round8.md`, sections 1--4. This closes the last G5 representative, conditional on the stated continuous polynomial certificate and the earlier geometric exclusions. The certificate description is preserved as source evidence; it has not been independently rerun for this English reconstruction.

### 1. Established hypotheses for the last representative

Use the translated target \([0,2\mu]^2\), \(\mu>1\), with the usual corner order. G5 means both \(C,F\) contain the center, and \(\kappa\) counts distinct outer midpoints actually in \(C\cup F\). R2 excludes \(\kappa=2\); R3 excludes \(\kappa=0\), four corner-hosted midpoints, and a midpoint shared by \(C,F\). R4 excludes contact by \(F\) with the edge of the sole midpoint of \(C\); R5--R6 exclude all near representatives.

Thus take \(C\) containing center and bottom midpoint, \(F\) containing center and no midpoint, with no bottom-midpoint corner host. The left host is \(V_1\), the right host \(V_2\); select top host \(V_4\), \(W=V_3\). The free corner misses the right midpoint but may duplicate the top. R7 gives: \(F\) is wholly in the open target interior; \(C\) meets only bottom; left, right, and top corners join; and all left/right/upper central reaches of \(C\) are redundant in \(F\). No earlier numerical conditional bound is used.

The three anchored corners \(i\in\{1,2,4\}\) have local standard forms
\[
L_i\ge\mu>1,\quad L_i+S_i+U_i<2,
\quad c_i,s_i>0,\ c_i^2+s_i^2=1,\quad c_iL_i,s_iL_i\le1,
\]
\[
S_i=(1-s_iL_i)/c_i,\qquad U_i=(1-\mu c_i)/s_i.
\]
Replacements dominate the old target intersection. Any output creating an already excluded ownership pattern must be sent to that exclusion; other changed predicates require complete reclassification under the protocol. Define \(t_i=(1-c_i)/s_i\in(0,1)\). Then
\[
c_i=\frac{1-t_i^2}{1+t_i^2},\quad s_i=\frac{2t_i}{1+t_i^2},
\quad U_i<t_i,\quad S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2},
\]
\[
L_i(1-t_i^2)\le1+t_i^2,\qquad2t_iL_i\le1+t_i^2.
\]
Center the chart and write \(l,r,u\ge0\) for the left, right, upper reaches of \(F\). With actual floating central chord lengths \(H,J\ge0\) of \(W\),
\[
l\ge\mu-U_1,\quad r+U_2+H\ge\mu,\quad u+U_4+J\ge\mu.
\]
Its right and top legs \(A,D\) satisfy \(A<\mu\), while duplicate top ownership \(D\ge\mu\) is retained. Joins give
\[
L_1+S_4\ge2\mu,\quad L_2+A\ge2\mu,\quad L_4+D\ge2\mu.
\]
The bottom gap \(g=2\mu-S_1-S_2\) is entirely in \(C\), which also meets the horizontal central line. The parallel bound gives \(g\le B(\mu)<1\), hence
\[
S_1+S_2>2\mu-1>1.\tag{1}
\]
For \(\mu>\sqrt2\), anchored long chords are already impossible; otherwise R2's parallel bound applies.

### 2. Coupling both central chords of W to its outer legs

If \(H>0\), its horizontal-central chord and top chord are nonempty and parallel, so \(D+H\le B<\mu\). With \(D+L_4\ge2\mu\), \(H<L_4-\mu\). If \(H=0\), \(L_4\ge\mu\) gives the weak bound \(H\le L_4-\mu\). For \(J>0\), the vertical-central and right chords give \(A+J\le B<\mu\); for \(J=0\), \(A<\mu\) gives the same strict inequality. Thus \(J<L_2-\mu\). Coverage now implies
\[
r\ge2\mu-L_4-U_2,\qquad u>2\mu-L_2-U_4.\tag{2}
\]
Only parallel pairs were used. If \(W\) duplicates the top midpoint, it cannot meet the horizontal central line, and is included by \(H=0\).

Put \(\epsilon=2\mu-2>0\). The left join and strict budget of \(V_4\) imply
\[
L_4+U_4<2-S_4\le L_1-\epsilon.\tag{3}
\]

### 3. A two-corner inequality

**Lemma.** Suppose \(t_1,t_2\in(0,1)\), \(L_1,L_2\ge1\),
\[
L_i(1-t_i^2)\le1+t_i^2,\quad2t_iL_i\le1+t_i^2,
\quad S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2},\quad S_1+S_2\ge1.
\]
Then
\[
L_1+L_2+\min(t_1,t_2)+\frac45\max(t_1,t_2)\le\frac{14}5.\tag{4}
\]

#### 3.1. The full two-dimensional parameter domain

Exchange labels to set \(x=t_1\le y=t_2\). Since \(L_i\ge1\), \(S_i\le(1-t_i)/(1+t_i)\), so
\[
x+y+3xy\le1,\quad0<x\le1/3,\quad x\le y\le\frac{1-x}{1+3x}.
\]
Define
\[
T=14/5-x-4y/5,\quad C_1=\frac{1+x^2}{1-x^2},\quad
C_2=\frac{1+y^2}{1-y^2},\quad C_{2s}=\frac{1+y^2}{2y},
\]
\[
S_{1*}=\frac{1+x^2-2xC_1}{1-x^2},\qquad
R=C_1+\frac{1+y^2-(1-S_{1*})(1-y^2)}{2y}.
\]
There are three valid upper bounds \(L_1+L_2\le C_1+C_2,C_1+C_{2s},R\). For the last, put \(a_t=2t/(1-t^2)\), \(b_t=(1+t^2)/(1-t^2)\). The short-leg sum gives \(a_xL_1+a_yL_2\le b_x+b_y-1\), and \(a_x\le a_y\), whence
\[
L_1+L_2\le(1-a_x/a_y)C_1+(b_x+b_y-1)/a_y=R.
\]
It remains to show that at each parameter point at least one upper bound is at most \(T\).

#### 3.2. Exact rational Bernstein certificate

Set
\[
P_0=5(1-x^2)(1-y^2)(T-C_1-C_2),
\]
\[
P_1=10y(1-x^2)(T-C_1-C_{2s}),\qquad
P_2=10y(1-x^2)^2(T-R).
\]
All multipliers are positive in the physical domain; it suffices that one \(P_i\ge0\). Map that full domain to the unit rectangle by
\[
x=u/3,\qquad y=\frac{u(1+u)+(1-u)(3+u)v}{3(1+u)},\qquad0\le u,v\le1.
\]
This equals \(y=x+[(1-x)/(1+3x)-x]v\); the boundary \(u=1\) contracts to \(x=y=1/3\) and is retained. If \(P_i\) has separate degrees \(d_x,d_y\), substitution followed by the positive factor \(3^{d_x+d_y}(1+u)^{d_y}\) yields an integer polynomial \(Q_i\).

The source certificate partitions the rectangle by alternating binary subdivision of \(u,v\) into 45 rational rectangles, maximum path depth ten. For each rectangle a selected \(Q_i\) has all Bernstein coefficients nonnegative. For power coefficients \(a_{pq}\), these coefficients are
\[
b_{ij}=\sum_{p\le i,q\le j}a_{pq}
\frac{\binom{i}{p}}{\binom{n_x}{p}}
\frac{\binom{j}{q}}{\binom{n_y}{q}}.
\]
The basis is nonnegative. The 45 binary paths form a complete prefix tree, covering the rectangle. Their coordinates, selected polynomial, and exact minimum coefficient are recorded in `round8_pair_bernstein_certificate.json` and regenerated `round8_two_corner_checks.json`.

The source describes a checker deriving the three polynomials anew, checking transformation identities and full domain coverage, and recomputing coefficients by direct affine power expansion rather than reusing the generator's de Casteljau recursion. All arithmetic is integral/rational. It also records a nonlinear real counterexample query. These are continuous-domain certificates, not 45 sampled parameter points. The exact certificate artifacts remain the review dependency for this English presentation.

### 4. Contradiction in both weight orders

R4's three-ray lemma and its reflection give
\[
l+u+(2\sqrt2-2)r\le2,\qquad r+u+(2\sqrt2-2)l\le2.
\]
As \(4/5<2\sqrt2-2\), use
\[
l+u+\tfrac45r\le2,\qquad r+u+\tfrac45l\le2.\tag{5}
\]
The source's additional query uses the complete widths \(p,q\ge0,p^2+q^2=1\), \(p(l+r),q(l+r)\le1\), \(pl+qu,qr+pu\le1\); reflection gives the second order.

Put \(\alpha=4/5\). If \(t_1\le t_2\), \(4\) and \(U_i<t_i\) give \(L_1+L_2+U_1+\alpha U_2\le14/5\). From \(2\),
\[
l+u+\alpha r>(3+2\alpha)\mu-L_2-U_4-\alpha L_4-U_1-\alpha U_2.
\]
By \(3\) and \(L_4\ge\mu\),
\[
U_4+\alpha L_4=(L_4+U_4)-(1-\alpha)L_4
<L_1-\epsilon-(1-\alpha)\mu.
\]
Therefore
\[
l+u+\alpha r>(4+\alpha)\mu+\epsilon-(L_1+L_2+U_1+\alpha U_2)
\ge2+\tfrac{34}5(\mu-1)>2,
\]
contradicting \(5\). If \(t_2\le t_1\), \(4\) gives \(L_1+L_2+\alpha U_1+U_2\le14/5\), and directly
\[
r+u+\alpha l>(4+\alpha)\mu-(L_4+U_4+L_2+U_2+\alpha U_1)
\]
\[
>(4+\alpha)\mu+\epsilon-(L_1+L_2+\alpha U_1+U_2)
\ge2+\tfrac{34}5(\mu-1)>2.
\]
Equality of the half-angles belongs to either branch. Thus the last far internal representative is excluded for all \(\mu>1\); combined with the prior modules, this is the candidate exclusion of G5.

<a id="technical-part-B"></a>
# Technical Part B. No owned midpoint and centre-owned midpoint cases

Modules: [R9](#R9), [R10C](#R10C), [R10](#R10), [R11](#R11), [R12](#R12).

<a id="R9"></a>
## R9. Exclusion of the G1 three-join configuration

**Scope.** Source: `S6_attack_round9.md`, sections 1--8. This treats G1 with three joined outer edges, including both possible non-corner owners of the sole gap. The subsequent central exclusivity statement and reduction to exactly two joins depend on the completed G5 exclusion. Exact polynomial certificates are retained as review dependencies, not newly verified claims.

### 1. Cyclic corner matching and the three joins

Use the translated target \([0,2\mu]^2\), \(\mu>1\). The corners \(V_i\) are in counterclockwise order from lower-left; \(C\) contains the center and \(F\) is the other non-corner tile. R8 gives \(o\notin F\). G1 means neither \(C\) nor \(F\) contains an outer midpoint. Hence all four midpoints have distinct corner hosts, with a cyclic matching. Reflect so \(V_i\) contains midpoint \(m_i\) of \(E_i=v_iv_{i+1}\).

For the standard-form anchored corner lengths,
\[
L_i\ge\mu,\quad L_i\le\sqrt2,\quad T_i=L_i+S_i+U_i<2,
\quad S_i+U_i\le B(\mu)<1.
\]
The long anchored outer chord excludes the other central line by the triangle-area bound \(\mu^2/2>1/2\), and remote edges by diameter, so \(T_i\) controls the full grid contribution. Half-angles \(t_i\in(0,1)\) satisfy
\[
U_i<t_i,\quad S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2}
<\frac{1-t_i}{1+t_i},
\quad L_i(1-t_i^2),2t_iL_i\le1+t_i^2.
\]
Only \(1<\mu\le\sqrt2\) needs consideration. Rotate the sole gap to bottom:
\[
L_2+S_3,L_3+S_4,L_4+S_1\ge2\mu,
\qquad L_1+S_2<2\mu.
\]
With \(\epsilon=2\mu-2>0\),
\[
S_1>S_4+U_4+\epsilon>S_3+U_3+U_4+2\epsilon
>S_2+U_2+U_3+U_4+3\epsilon.
\]
In particular \(S_2+U_4<1\). Center the chart. The four central endpoints are
\[
q_1=(0,-\mu+U_1),\quad q_2=(\mu-U_2,0),
\quad q_3=(0,\mu-U_3),\quad q_4=(-\mu+U_4,0).
\]
Each belongs to \(C\cup F\): take limits of points beyond its corner segment; other corners are excluded by their long-chord triangle or diameter. All \(\mu-U_i>0\).

### 2. Exactly one non-corner tile meets the bottom gap

Right joining gives \(S_3\ge2\mu-L_2\). As \(L_2<3/2\) and \(S_3+U_3<1\),
\[
2\mu-U_3>4\mu-5/2>3/2>\sqrt2.
\]
Thus a tile meeting bottom cannot contain \(q_3\), regardless of the horizontal contact coordinate. At least one non-corner tile meets the nonempty bottom gap, while the tile covering \(q_3\) cannot. Exactly one such tile, call it \(D\), meets bottom and covers the whole gap; call the other \(E\).

The far gap endpoint \(Q=(\mu-S_2,-\mu)\) lies in \(D\) by closedness. If \(D\) also contained \(q_4\), its horizontal span would be \(2\mu-S_2-U_4>2\mu-1>1\), with vertical span \(\mu>1\), contradicting diameter. Hence \(E\) contains \(q_3,q_4\). The alternatives \(D=C\) and \(D=F\) are exhaustive.

### 3. A universal boundary-length bound for a larger square

**Lemma.** For an axis-aligned square \(R\) of side \(\mu>1\) and any closed unit square \(Z\), \(\operatorname{length}(Z\cap\partial R)\le2\). No anchor or center hypothesis is required.

First, the sum \(X+Y\) of chord lengths on two orthogonal positive rays is at most two. Choose normals \((c,s),(-s,c)\), with \(c\ge s\ge0,c^2+s^2=1\), exchanging axes if needed. If the upper ray endpoints have coordinates \(x_2,y_2\), then \(sx_2+cy_2\le1\), so \(sX+cY\le1\), and separately \(cX\le1\). Hence
\[
X+Y\le1/c+(1-s/c)X\le(2c-s)/c^2\le2.
\]
The last inequality uses \(s\ge2c(1-c)\); for \(c<1\), \(s/(1-c)=(1+c)/s\ge(1+c)/c>2c\). The axial case has \(X,Y\le1\).

Now classify boundary contacts: one edge contributes at most \(\sqrt2<2\); two adjacent edges use the ray bound; two opposite use \(B(\mu)<1\). For three edges, one opposite pair contributes at most \(B(\mu)\) and the third at most \(\mu\), totaling less than two. Four edges contribute at most \(2B(\mu)<2\). If \(\mu>\sqrt2\), opposite contacts are impossible and only at most two adjacent edges remain. Singleton tangencies add no length. The source records a separate real-algebra query for the two-ray bound.

### 4. If D=C, convexity excludes F from a quarter-square

Take the centered lower-right quarter-square \(R=[0,\mu]\times[-\mu,0]\). Now \(F\) contains \(q_3=(0,u),q_4=(-l,0)\), \(u,l>0\), but not zero. For any nonzero \(z=(x,-y)\in R\), \(x,y\ge0\),
\[
z+(x/l)q_4+(y/u)q_3=0.
\]
Normalize these nonnegative weights: zero lies in their convex hull. Thus a point of \(F\cap R\) would put zero in \(F\), contradicting R8; zero itself is also excluded. Hence \(F\cap R=\varnothing\).

Neither \(V_3\) nor \(V_4\) meets \(\partial R\): their anchors exclude the other central line, \(S_i,U_i<1<\mu\) cannot reach the other half, and diameter excludes remote edges. The contributions of \(V_1,V_2\) are \(L_1-\mu+U_1\) and \(\mu+S_2+U_2\). By Section 3, \(C\) contributes at most two. Therefore
\[
4\mu\le L_1+S_2+U_1+U_2+2.
\]
But the joins and total corner budget yield
\[
L_1+S_2+U_1+U_2+U_3+U_4
=\sum_iT_i-[(L_2+S_3)+(L_3+S_4)+(L_4+S_1)]<8-6\mu.
\]
The required right side is less than \(10-6\mu<4\), while \(4\mu>4\).

### 5. If D=F, charge the extensions of C to corner slack

Now \(C\) contains \(q_3,q_4\). The right/top joins give \(2\mu-U_3,2\mu-U_4>3/2\). Hence \(C\) misses the bottom/right edges of \(R\); only its right and lower central reaches \(r,b\) contribute. Its left/upper reaches satisfy \(l\ge\mu-U_4,u\ge\mu-U_3\). Let its positive normals be \((c,s),(-s,c)\), and \(p=\max(c,s),q=\min(c,s)\), \(p^2+q^2=1\). Both full axial chord lengths are at most \(1/p\), so
\[
r+b\le2/p-l-u\le U_3+U_4-\epsilon+(2/p-2).\tag{1}
\]
The endpoint pair also gives \(cl+su\le1\). The half-angle cascade, with auxiliary ratios denoted \(\rho_i\) instead of the source's local kappa, gives
\[
t_3<\rho_2=\frac{L_2-1}{3-L_2}<4/15,
\quad t_4<\rho_3=\frac{L_3-1}{3-L_3}
\le\frac{t_3^2}{1-2t_3^2}<16/193.
\]
Here \(L_2\le\sqrt2<27/19\), and all denominators are positive. Also
\[
S_3\ge2\mu-L_2>2-\sqrt2>7/12.
\]
Let \(\Delta_i=2-T_i>0\). Section 6 supplies two full-domain algebraic lemmas:

1. For \(0<t\le16/193\), \(L\ge1\), the two corner projection upper bounds, \(S=(1+t^2-2tL)/(1-t^2)\), and \(p(1-t)+(11/15)q\le1\), one has \(2/p-2\le2-L-S-t\).
2. For \(0<t<4/15\), the same projection bounds, \(S\ge7/12\), \(\rho=(L-1)/(3-L)\), and \(p(1-t)+q(1-\rho)\le1\), the same conclusion holds.

If \(c\ge s\), then \(p=c,q=s\); \(cl+su\le1\), \(U_i<t_i\), and \(\mu>1\) imply \(p(1-t_4)+(11/15)q\le1\). Apply the first lemma to \(V_4\): \(2/p-2\le2-L_4-S_4-t_4<\Delta_4\). If \(c<s\), \(p=s,q=c\) and the same width implies \(p(1-t_3)+q(1-\rho_3)\le1\). Apply the second lemma to \(V_3\), obtaining \(2/p-2<\Delta_3\). Thus for some \(j\in\{3,4\}\),
\[
r+b\le U_3+U_4-\epsilon+\Delta_j.\tag{2}
\]
Section 3 bounds the contribution of \(F\) to \(\partial R\) by two; corner contributions remain \(L_1+S_2+U_1+U_2\). Hence coverage would require
\[
4\mu\le2+L_1+S_2+U_1+U_2+r+b
\le12-8\mu-\sum_{i\ne j}\Delta_i<4,
\]
impossible. Both gap owners are excluded.

### 6. Exact rational certificates for the extension lemmas

Put
\[
S=\frac{1+t^2-2tL}{1-t^2},\quad D=2-L-S-t,
\quad L_c=\frac{1+t^2}{1-t^2}.
\]
On the small-angle domains below, \(D\) decreases strictly with \(L\); for \(L\ge1\), \(D\le t(1-t)/(1+t)<t\). The goal is \(2/p-2\le D\).

The calibration fact is as follows. If \(a,b>0,a+b>\sqrt2,0\le D\le t\le4/15\), \(a=1-t\), and
\[
P=b^2D(D+4)-(D+2t)^2\ge0,
\]
then \(p\ge q\ge0,p^2+q^2=1,ap+bq\le1\) implies \(p\ge2/(2+D)\). Indeed \(p_0=2/(2+D)>1/\sqrt2\); the inequality \(P\ge0\) is equivalent to \(ap_0+b\sqrt{1-p_0^2}\ge1\). The function \(ap+b\sqrt{1-p^2}\) is concave on \([1/\sqrt2,p_0]\), and its left endpoint exceeds one. It can be at most one only for \(p\ge p_0\).

#### 6.1. The small-angle V4 lemma

Take \(b=11/15,0<t\le16/193\). The bound \(L\le L_c\) and an exact polynomial certificate give \(D\ge t/2\). Since \(D\le t\),
\[
P\ge4b^2D-(D+2t)^2\ge t(2b^2-9t)>0,
\]
using \(242/225>144/193\). Also \(a+b\ge26/15-16/193>17/12>\sqrt2\). For \(D(L_c)-t/2\), the positive denominator is \(2(1-t^2)^2\), and the numerator is
\[
-t(3t^4-8t^3-10t^2+8t-1).
\]
Its exact Bernstein coefficients on \([0,16/193]\) are all nonnegative; the first is zero and every other one positive. Thus it is strictly positive for \(t>0\), proving the first lemma.

#### 6.2. The adjacent long-leg V3 lemma

Take \(\rho=(L-1)/(3-L),b=1-\rho\). From \(S\ge7/12,L\ge1\),
\[
t\le5/19,\qquad L\le L_c,\quad L\le L_s=\frac{5+19t^2}{24t}.
\]
On the required intervals and selected endpoints, \(1\le L\le241/209\), so \(\rho\le16/193<1/12\), \(b>11/12\), and \(a+b>11/15+11/12>\sqrt2\). As a function of \(b,D\),
\[
P_D=4b^2-4t-2(1-b^2)D>0,\quad P_b=2bD(D+4)\ge0.
\]
Even the weakest constants give
\[
4(121/144)-4(4/15)-2(23/144)(4/15)>0.
\]
Both \(D\) and \(b\) decrease with \(L\), with \(b_L=-2/(3-L)^2<0\); hence \(P\) decreases with \(L\). Use endpoint \(L_c\) for \(0<t\le9/40\), and \(L_s\) for \(9/40\le t\le5/19\).

The four numerator certificates, with positive denominators, are:

1. \(D(L_c)\), denominator \((1-t^2)^2\), numerator \(-t(t^4-4t^3-4t^2+4t-1)\).
2. \(P(L_c)\), denominator \((1-t^2)^4(1-2t^2)^2\), numerator
\[
t(5t^{13}-140t^{12}+150t^{11}+712t^{10}-570t^9-1036t^8+884t^7
+600t^6-579t^5-140t^4+182t^3-24t+4).
\]
3. \(D(L_s)\), denominator \(24t\), numerator \(-43t^2+34t-5\).
4. \(P(L_s)\), denominator \(192t^2(19t^2-72t+5)^2\), numerator
\[
886977t^8-7909244t^7+25765680t^6-36376972t^5+20496142t^4
-5232180t^3+634000t^2-34500t+625.
\]
The first pair has nonnegative Bernstein coefficients on \([0,9/40]\), the second on \([9/40,5/19]\). Except the first coefficients at \(t=0\) in the first pair, all are positive. The source checker derives the numerators from \(S,D,\rho\), verifies expansions, and recomputes exact coefficients. Together with Section 6.1 these are five univariate rational interval certificates; numerical optimization and SMT statuses are not substitutes for them.

### 7. A central region with a unique covering tile

R8 also implies: for a covered target \([0,a]^2\), \(a>2\), each point in \(K=(1,a-1)^2\) is the center of an inscribed axis-aligned square of side greater than two. It belongs to exactly one covering tile, since two would give G5 for that smaller square. The finite relative closed intersections with connected \(K\) are disjoint and cover it; one tile, the original \(C\), therefore contains all of \(K\), and the others avoid \(K\). Taking closure,
\[
[1,a-1]^2\subset C,
\]
or, centered, \([-(\mu-1),\mu-1]^2\subset C\), with \(F\) avoiding its open interior. This statement depends on G5 already being established; it is not an input to R8 or its certificates.

### 8. Exactly two joins remain in G1

**Midpoint-forcing lemma.** A unit square containing \(P=(-d,0),Q=(0,T)\), \(d\ge0,T\ge\mu>1\), also contains \(M=(0,\mu)\).

Choose positive-quadrant normals \((c,s),(-s,c)\), \(c^2+s^2=1\). The first width gives \(cd+sT\le1\). The first projection of \(M\) lies between those of \(P,Q\); if \(sd\le c\mu\), so does the second, proving containment. Otherwise \(sd>c\mu\). Write \(c=\cos\theta,s=\sin\theta\), giving \(\theta>\theta_0=\arctan(\mu/d)\); \(d=0\) makes this alternative impossible. The function \(d\cos\theta+T\sin\theta\) is concave on \([\theta_0,\pi/2]\). Its endpoint values are
\[
\frac{d^2+\mu T}{\sqrt{d^2+\mu^2}}\ge\sqrt{d^2+\mu^2}>1,
\qquad T>1,
\]
contradicting \(cd+sT\le1\). Axial directions are included.

Each G1 gap lies beyond its midpoint in the cyclic matching direction. If one non-corner tile met two adjacent gaps, a rotated midpoint-forcing lemma would put their intervening outer midpoint in that tile, contrary to G1. Opposite gaps cannot share a tile by diameter. Thus \(C,F\) fill at most two gaps, so at least two edges join. Four joins contradict \(\sum(L_i+S_i)\ge8\mu>8\) and \(T_i<2\); three joins were just excluded. Therefore every surviving G1 covering has exactly two joined outer edges, leaving adjacent and opposite representatives. This deduction uses the new projection argument, not the earlier FarPair distance formula.

<a id="R10C"></a>
## R10C. Nonempty-chord correction for opposite G1 gaps

**Scope.** Source: S6_proof_audit_corrigendum.md, sections 2--3. This is the mandatory replacement for the original R10.2 argument. A zero length can mean an empty intersection or a singleton; both are treated before invoking the parallel-chord bound.

### 2. Proof that the horizontal chord of F has positive length

Rotate so that \(C\) fills bottom gap \(g_1>0\), \(F\) fills top gap \(g_3>0\), and the right and left corner intervals join. Use the cyclic \(L_i,S_i,U_i\) of R9 and put \(\epsilon=2\mu-2>0\). Then
\[
L_2+S_3\ge2\mu,\quad L_2+S_2+U_2<2
\quad\Longrightarrow\quad S_3>S_2+U_2+\epsilon,
\]
\[
L_4+S_1\ge2\mu,\quad L_4+S_4+U_4<2
\quad\Longrightarrow\quad S_1>S_4+U_4+\epsilon.
\]
Suppose the target horizontal chord length \(h_F=0\), allowing either an empty chord or tangency. Horizontal-central coverage still requires
\[
h_C\ge2\mu-U_2-U_4.
\]
The tile \(C\) contains the center and the entire bottom gap, so its two parallel intersections really are nonempty and \(g_1+h_C\le B(\mu)<1\) is legitimate. On the other hand,
\[
\begin{aligned}
g_1+h_C
&\ge4\mu-L_1-S_2-U_2-U_4\\
&>4\mu-L_1-S_1-S_3+S_4+2\epsilon\\
&>4\mu-2-S_3+U_1+S_4+2\epsilon\\
&>4\mu-3+U_1+S_4+2\epsilon\\
&=8\mu-7+U_1+S_4>1.
\end{aligned}
\]
The third line uses \(L_1+S_1+U_1<2\), and the fourth \(S_3<1\). Thus \(h_F>0\). If \(C\) originally fills the top gap, rotate by \(180^\circ\) first.

### 3. The restored aggregate contradiction

Now both tiles actually meet their respective outer edge and the horizontal central line. Hence
\[
g_1+h_C\le B,\qquad g_3+h_F\le B,
\qquad h_C+h_F+U_2+U_4\ge2\mu.
\]
The two gaps and two joins imply
\[
\begin{aligned}
\sum_i(L_i+S_i+U_i)
&\ge8\mu-g_1-g_3+\sum_iU_i\\
&\ge10\mu-2B+U_1+U_3>8.
\end{aligned}
\]
This contradicts the four strict anchored-corner budgets. The opposite-gap branch is excluded for every \(\mu>1\), retaining repeated midpoint ownership and allowing tangencies.

The source records separate QF_LRA reconstructions of the empty-chord exclusion and the restored aggregate, both UNSAT, in `work/check_proof_audit_geometry.py` and `work/proof_audit_20261010/fresh_geometry_checks.json`. These identify the source checks; this translation does not independently rerun them.

<a id="R10"></a>
## R10. Completion of the G1 exclusion

**Scope.** Source: S6_attack_round10.md, sections 1 and 3--6. The original section 2 is replaced in full by R10C, which proves the missing nonempty-chord premise before the opposite-gap aggregate is used. This module handles the two adjacent gaps and retains their two possible owners.

### 1. Notation, normalization, and established inputs

Use the centered target \(S=[-\mu,\mu]^2\), \(\mu=a/2>1\). Corners \(V_1,V_2,V_3,V_4\) are lower-left, lower-right, upper-right, upper-left. The unique center tile is \(C\), by R8; \(o\notin F\). In G1 neither non-corner tile contains a midpoint. A reflected cyclic host choice has \(V_1,V_2,V_3,V_4\) containing bottom, right, top, left midpoints.

Each corner can be replaced locally by a target-dominating standard form with \(C,F\) fixed. No corner can acquire a second midpoint or the center. All actual gap and host predicates are then reclassified by the sole protocol; the proof below applies to the resulting G1 configuration. The anchored lengths satisfy
\[
L_i\ge\mu,\quad L_i\le\sqrt2,\quad T_i=L_i+S_i+U_i<2,
\qquad S_i+U_i\le B(\mu)<1,
\]
\[
B(d)=\begin{cases}
d-\sqrt{d^2-1},&1<d\le3/(2\sqrt2),\\
2(\sqrt2-d),&3/(2\sqrt2)\le d\le\sqrt2.
\end{cases}
\]
The long outer anchor excludes the other central line by the triangle area \(\mu^2/2>1/2\), and remote edges by diameter. Thus these lengths bound the full six-line-grid contribution. For \(t_i\in(0,1)\),
\[
c_i=\frac{1-t_i^2}{1+t_i^2},\quad s_i=\frac{2t_i}{1+t_i^2},
\quad S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2},\quad
U_i<t_i,\quad S_i<\frac{1-t_i}{1+t_i},
\]
\[
L_i(1-t_i^2)\le1+t_i^2,\qquad2t_iL_i\le1+t_i^2.
\]
The anchors exclude \(\mu>\sqrt2\). Joining on \(E_i\) means \(L_i+S_{i+1}\ge2\mu\); otherwise \(g_i=2\mu-L_i-S_{i+1}>0\) is an open gap beyond its midpoint in the matching direction.

R9's midpoint-forcing lemma states that a unit tile containing \((-d,0),(0,T)\), \(d\ge0,T\ge\mu>1\), contains \((0,\mu)\). Its rotations forbid one G1 non-corner tile from meeting two adjacent gaps; diameter forbids opposite gaps. Each non-corner tile therefore fills at most one gap. With two gaps, each belongs entirely to a different non-corner tile, endpoints included by closedness. R9 excludes three joins; four contradict \(\sum T_i<8\); fewer than two joins leave too many gaps. Exactly two joins remain. The opposite-gap possibility is excluded by R10C, including its positive-\(h_F\) proof.

The central endpoints
\[
q_1=(0,-\mu+U_1),\quad q_2=(\mu-U_2,0),\quad
q_3=(0,\mu-U_3),\quad q_4=(-\mu+U_4,0)
\]
belong to \(C\cup F\), by limits beyond the corner intervals. Also use R9's universal bound: any unit tile contributes at most two to the boundary of a square of side \(\mu>1\), with floating chords and no center assumption allowed.

### 3. Forced endpoint ownership with adjacent joins

Rotate so right and top join, bottom and left have gaps:
\[
L_2+S_3\ge2\mu,\qquad L_3+S_4\ge2\mu.
\]
Let \(\epsilon=2\mu-2>0\). Then
\[
S_4>S_3+U_3+\epsilon>S_2+U_2+U_3+2\epsilon,
\qquad S_2+U_2+U_3+U_4<1-2\epsilon. \tag{1}
\]
Right joining, \(L_2<3/2\), and \(S_3+U_3<1\) give
\[
2\mu-U_3>4\mu-5/2>3/2>\sqrt2. \tag{2}
\]
The bottom-gap owner cannot contain \(q_3\). It contains the far gap endpoint \(P_b=(\mu-S_2,-\mu)\). If it also contained \(q_4\), the horizontal span \(2\mu-S_2-U_4>1\), together with vertical span \(\mu>1\), would violate diameter. Hence the left-gap owner contains both \(q_3,q_4\).

### 4. C owns the bottom gap: a linear contradiction

Now \(F\) owns the left gap and contains \(q_3=(0,u),q_4=(-l,0)\), \(u,l>0\). For a lower-right point \(z=(x,-y)\), \(x,y\ge0\),
\[
z+(x/l)q_4+(y/u)q_3=0.
\]
Convexity and \(o\notin F\) therefore exclude \(F\) from that closed quarter-square. In particular \(q_1,q_2\in C\). Its bottom gap is \(g_1=2\mu-L_1-S_2\); its horizontal central chord has length at least \(\mu-U_2\). Thus
\[
g_1+\mu-U_2\le B<1,
\]
so \(L_1+S_2+U_2>3\mu-1>2\). Since \(T_1<2\), \(S_1+U_1<S_2+U_2\); using (1),
\[
S_1+U_3<S_2+U_2+U_3<1. \tag{3}
\]
But \(F\) also contains left-gap endpoint \(P_l=(-\mu,-\mu+S_1)\) and \(q_3\). Their horizontal span is \(\mu>1\); diameter requires vertical span \(2\mu-S_1-U_3<1\), hence \(S_1+U_3>2\mu-1>1\), contrary to (3).

### 5. C owns the left gap: coupling its direction to a corner

Now \(C\) contains \(P_l,q_3,q_4\), while \(F\) fills bottom. Rename the source's local \(k,h\) as
\[
t=t_2,\qquad \rho=\frac{L_2-1}{3-L_2},\qquad h_1=t_1.
\]
Here \(\rho\) is an auxiliary ratio, not midpoint count, and \(h_1\) is a corner half-angle, not the central half-angle. Since \(1<L_2\le\sqrt2<27/19\), \(0<\rho<4/15\). Two joins give
\[
t_3<\rho,\qquad t_4<\frac{\rho^2}{1-2\rho^2}=:w(\rho). \tag{4}
\]
Indeed \(L_2+S_3>2\) and \(S_3<(1-t_3)/(1+t_3)\) give the first; the second follows from \(t_4<(L_3-1)/(3-L_3)\) and the cosine upper bound for \(L_3\). All denominators are positive.

For the positive normals \((c,s),(-s,c)\) of \(C\), the pair \(P_l,q_3\) forces
\[
c\mu+s(2\mu-S_1-U_3)\le1. \tag{5}
\]
Since \(S_1<1,U_3<4/15\), the second length exceeds \(11/15\). If \(c\ge s\), the concave function \(\cos\theta+(11/15)\sin\theta\) on \([0,\pi/4]\) has endpoint values \(1,26/(15\sqrt2)>1\), while the strict geometric lengths make (5) exceed one. Thus \(c<s\), including exclusion of the relevant axial direction.

Put \(p=s,q=c\). Then \(p>q\ge0,p^2+q^2=1\), and relaxing (5) gives
\[
q+p\left(1+\frac{2h_1}{1+h_1}-\rho\right)\le1. \tag{6}
\]
Let \(r,b,l,u\) be the target right, lower, left, upper reaches of \(C\). Since \(l\ge\mu-U_4,u\ge\mu-U_3\), and full axial chords are at most \(1/p\),
\[
r+b\le U_3+U_4-\epsilon+E,\qquad E=2/p-2. \tag{7}
\]

#### 5.1. Calibration of the central extension

For \(0<\rho<4/15,h_1\ge0\), \(p\ge q\ge0,p^2+q^2=1\), and (6),
\[
\frac{1+h_1^2}{1-h_1^2}+h_1+E\le1+B_*(\rho),
\qquad B_*(\rho)=\frac{\rho}{2-\rho}+\frac{\rho^2}{2(1-\rho)}. \tag{8}
\]
Condition (6) itself gives \(h_1<1\). To prove this, set \(z=q/(1+p)\); then
\[
p=\frac{1-z^2}{1+z^2},\quad q=\frac{2z}{1+z^2},
\quad E=\frac{4z^2}{1-z^2},
\]
\[
0\le z\le\frac{\rho}{2-\rho},\qquad
0\le h_1\le H_\rho(z)=
\frac{\rho-(2-\rho)z}{2-\rho+(4-\rho)z}.
\]
The function \(f(h)=(1+h^2)/(1-h^2)+h\) is increasing and convex; \(H_\rho\) is nonnegative and convex, with
\[
H_\rho''(z)=\frac{8(4-\rho)}{[2-\rho+(4-\rho)z]^3}>0.
\]
Also \(E(z)\) is convex. Thus \(J(z)=f(H_\rho(z))+E(z)\) has maximum at an endpoint:
\[
J(0)=1+B_*(\rho),\qquad
J\left(\frac{\rho}{2-\rho}\right)=1+\frac{\rho^2}{1-\rho}.
\]
Their difference is \(\rho(2-4\rho+\rho^2)/[2(1-\rho)(2-\rho)]>0\), proving (8). The source records symbolic identity and continuous real-algebra checks, not floating optimization.

#### 5.2. The lower-right quarter-square boundary

For \(R=[0,\mu]\times[-\mu,0]\), (2) excludes \(C\) from bottom, and the top join similarly gives \(2\mu-U_4>3/2\), excluding it from right. Its contribution is \(r+b\); \(V_3,V_4\) contribute zero; \(V_1,V_2\) contribute exactly
\[
V=L_1+S_2+U_1+U_2.
\]
The universal bound gives at most two from \(F\). Therefore
\[
4\mu\le V+r+b+2. \tag{9}
\]
The cosine bound \(L_1\le(1+h_1^2)/(1-h_1^2)\), \(U_i<t_i\), and (4),(7),(8) imply
\[
V+r+b<1+B_*(\rho)+S_2+t+\rho+w(\rho)-\epsilon. \tag{10}
\]
With \(L_2=(1+3\rho)/(1+\rho)\) and exact \(S_2\), the right side is \(2-\Phi(t,\rho)-\epsilon\), where
\[
\Phi(t,\rho)=\frac{t(1-t)}{1+t}
+\frac{4t\rho}{(1-t^2)(1+\rho)}
-\rho-\frac{\rho}{2-\rho}
-\frac{\rho^2}{2(1-\rho)}
-\frac{\rho^2}{1-2\rho^2}. \tag{11}
\]

### 6. Full-domain positivity of Phi

The physical projection bounds give
\[
0<\rho\le K_c(t)=\frac{t^2}{1-2t^2}\quad(0<t\le5/12),
\]
\[
0<\rho\le K_s(t)=\frac{(1-t)^2}{-t^2+6t-1}\quad(5/12\le t<1).
\]
Here \(K_c\le25/94<4/15\); \(K_s\) decreases and is at most \(49/191<4/15\). Moreover
\[
\Phi_{\rho\rho}=
-\frac{8t}{(1-t^2)(1+\rho)^3}
-\frac4{(2-\rho)^3}
-\frac1{(1-\rho)^3}
-\frac{2(1+6\rho^2)}{(1-2\rho^2)^3}<0.
\]
Thus positivity at zero and the selected upper endpoint proves positivity throughout. At zero \(\Phi(t,0)=t(1-t)/(1+t)>0\).

At \(K_c\), the positive denominator is
\[
2(1-t^2)^2(1-2t^2)(1-3t^2)(2-5t^2)(1-4t^2+2t^4),
\]
and the numerator is
\[
t(120t^{14}-254t^{13}-868t^{12}+1178t^{11}+1848t^{10}
-2029t^9-1478t^8+1698t^7+438t^6-741t^5+14t^4
+162t^3-30t^2-14t+4).
\]
The degree-fifteen numerator has first Bernstein coefficient zero and all others strictly positive on \([0,5/12]\); hence it is positive for \(t>0\).

At \(K_s\), put \(D_s=-t^2+6t-1\). The positive denominator is
\[
4D_s(-t^2+4t-1)(-3t^2+14t-3)[D_s^2-2(1-t)^4],
\]
and numerator
\[
(1-t)(12t^{10}-153t^9+165t^8+5460t^7-29628t^6
+55674t^5-34434t^4+6516t^3+872t^2-425t+37).
\]
Its degree-eleven Bernstein coefficients on \([5/12,1]\) are strictly positive except the last, which is zero; hence it is positive for \(t<1\). The first three denominator factors are positive and increasing on this interval, and the last is \(D_s^2(1-2K_s^2)>0\).

The source review package records all rational coefficients and reconstruction identities, derived directly from (11). For \(N(a+(b-a)v)=\sum_jA_jv^j\) of degree \(n\), the exact coefficient formula is
\[
b_i=\sum_{j\le i}A_j\frac{\binom{i}{j}}{\binom{n}{j}}.
\]
These continuous interval certificates, with the specified endpoint zero coefficients, remain an explicit review dependency; they are not angle samples. Thus \(\Phi>0\), making the right side of (9) less than four while \(4\mu>4\). With R10C and the other adjacent owner, this completes the candidate G1 exclusion.

<a id="R11"></a>
## R11. Interior-point obstruction and reduction of a far G2 representative

**Scope.** Source: S6_attack_round11.md, sections 1--10. Here \(C\) contains the center and bottom midpoint, while \(F\) contains neither center nor any outer midpoint. The far representative is reduced to a high-half-angle case, which this module leaves open. R12 later closes the representative using only Sections 3--5, without the normalization-dependent angle arguments of Sections 7--10.

### 1. The representative and its complete parameters

The target is \(S=[-\mu,\mu]^2\), \(\mu>1\). Corners \(V_1,V_2,W=V_3,V_4\) are in the usual order. Write \(m_B=(0,-\mu),m_R=(\mu,0),m_U=(0,\mu),m_L=(-\mu,0)\), corresponding to the source's \(m_1,m_2,m_3,m_4\). Assume \(o,m_B\in C\), \(o\notin F\), and no midpoint in \(F\). Select \(m_L\in V_1,m_R\in V_2,m_U\in V_4\). Initially \(W\) may duplicate right or top midpoint ownership.

For \(i=1,2,4\),
\[
L_i\ge\mu,\quad L_i\le\sqrt2<3/2,\quad
L_i+S_i+U_i<2,\qquad S_i+U_i\le B(\mu)<1.
\]
The long/short legs of \(V_1\) lie on left/bottom, those of \(V_2\) on right/bottom, and those of \(V_4\) on top/left. The center/bottom anchor confines \(C\) to the bottom outer edge. The right/top legs of \(W\) are \(A,D\); its actual target central chord lengths \(H,J\) lie on the open right/upper half-axes and may float:
\[
A+D+H+J\le2.
\]
For corner half-angles \(t_i\in(0,1)\),
\[
S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2},\quad
U_i<t_i,\quad S_i<\frac{1-t_i}{1+t_i},
\quad L_i(1-t_i^2),2t_iL_i\le1+t_i^2.
\]
The parallel bound \(B\) applies only when both line intersections are nonempty, including singleton tangencies; it cannot be invoked for an empty line intersection.

### 2. Axial endpoint propagation

**Lemma.** A unit square containing \(P=(-l,0),Q=(\mu,y)\), \(l>0,\mu>1\), \(y\in\mathbb R\), contains the origin.

Use \((\mu,0)\) as reference, exchange axes, and reflect according to the sign of \(y\). The pair becomes \((0,T),(-d,0)\), \(T=\mu+l>\mu>1,d=|y|\). R9's midpoint-forcing lemma puts \((0,\mu)\), the original origin, in the tile. For \(y=0\), convexity also suffices. The source records an UNSAT real-algebra system with both endpoint projections in common unit intervals but zero strictly excluded from one interval. This status is supporting source evidence. Consequently, if \(F\) contains any point on the negative horizontal half-axis, it cannot touch the right outer edge. Rotations apply.

### 3. F misses the bottom: empty intersections must be separated

Suppose \(F\) meets bottom. Its chord lies in an open half-edge because it omits \(m_B\). It misses top by distance \(2\mu>\sqrt2\). It misses upper halves of side edges: on the same side the midpoint-forcing lemma gives a forbidden side midpoint; on the opposite side both coordinate differences exceed \(\mu\). All remaining non-bottom boundary contributions are redundant in the lower side long legs of \(V_1,V_2\).

#### 3.1. Nonempty horizontal-central intersection

Let \(b_C,b_F\) be bottom chord lengths and \(h_C,h_F\) horizontal-central chord lengths. Both intersections really exist, so
\[
b_C+h_C\le B,\qquad b_F+h_F\le B.
\]
The vertical-central union is at most \(2\mu\), and corners contribute at most eight. Thus
\[
12\mu\le8+2\mu+2B<12\mu,
\]
impossible. A tangent horizontal intersection is included here.

#### 3.2. Empty horizontal intersection and a bottom-right chord

The endpoint \(q_L=(-\mu+U_1,0)\) must belong to \(C\): \(W\) is too far, the top anchor of \(V_4\) excludes the horizontal line, the short interval of \(V_2\) lies on its right half, and \(F\) misses the whole line. The left bottom gap is covered by \(C\), so \(b_C\ge\mu-S_1,h_C\ge\mu-U_1\). Hence
\[
B\ge b_C+h_C\ge2\mu-S_1-U_1\ge2\mu-B,
\]
a contradiction.

#### 3.3. Empty horizontal intersection and a bottom-left chord

Now \(b_C\ge\mu-S_2\). Endpoint propagation also excludes \(F\) from the positive vertical central half-axis. Right and top corners must join:
\[
L_2+A\ge2\mu,\qquad L_4+D\ge2\mu.
\]
If \(C_R,C_U\) are the right and upper reaches of \(C\), coverage requires
\[
C_R+U_2+H\ge\mu,\qquad C_U+U_4+J\ge\mu.
\]
The one-sided long-chord budget \(b_C+\mu+C_U+C_R<2\), the \(W\) budget, and the two anchored budgets yield
\[
2\mu<2-2\mu+S_2+U_2+U_4+H+J
\le4-6\mu+(L_2+S_2+U_2)+(L_4+U_4)<8-6\mu,
\]
contrary to \(\mu>1\). All alternatives are exhausted, so \(F\) misses bottom.

### 4. The left endpoint belongs to F; right joining and a strict top-leg bound

The full bottom gap \(g=2\mu-S_1-S_2>0\) now lies in \(C\). If \(q_L\in C\), its horizontal chord has length at least \(\mu-U_1\), so
\[
3\mu\le B+(S_1+U_1)+S_2\le3B<3.
\]
Thus \(q_L\in F\). Section 2 excludes \(F\) from the whole right boundary. Since \(C\) also misses it,
\[
L_2+A\ge2\mu. \tag{1}
\]
Convexity excludes \(F\) from the positive horizontal half-axis, giving
\[
C_R+U_2+H\ge\mu. \tag{2}
\]
Also \(g+C_R\le B\). If \(H=0\), then \(3\mu\le B+S_1+(S_2+U_2)\le2B+S_1<3\); hence \(H>0\). The actual nonempty top/horizontal chord pair of \(W\) gives \(D+H\le B\), so
\[
D\le B-H\le2B-3\mu+S_1+S_2+U_2
\le3B-3\mu+S_1<S_1. \tag{3}
\]
The length \(H\) is a full floating chord, not an anchored leg.

### 5. No left join; the top must join

If \(L_1+S_4\ge2\mu\), then with \(\epsilon=2\mu-2>0\),
\[
S_4>S_1+U_1+\epsilon.
\]
If top also joined, \(D>S_4+U_4+\epsilon>S_1\), contradicting (3). Otherwise \(F\) fills the top gap and contains its far endpoint \(Q_t=(\mu-D,\mu)\). The pair \(q_L,Q_t\) has horizontal span \(2\mu-D-U_1>2\mu-S_1-U_1>1\) and vertical span \(\mu>1\), contradicting diameter.

Thus left has a nonempty gap, entirely filled by \(F\), in its upper half. If \(F\) also filled a top-right gap, midpoint forcing would give the top midpoint. Therefore
\[
L_4+D\ge2\mu. \tag{4}
\]
The remaining outer pattern has right/top joined, bottom gap in \(C\), and left-upper gap in \(F\).

### 6. F meets the upper vertical axis and avoids the lower-right quarter

Combining the long-chord bound for \(C\), (2),(4), and the \(W\) and anchored-corner budgets gives
\[
C_U+U_4+J<8-8\mu+S_1-S_4<1<\mu.
\]
Therefore \(F\) must contain some \((0,f)\), \(f>0\), to complete the upper vertical central segment. It already contains \(q_L=(-l,0)\), \(l=\mu-U_1>0\). If it contained any \((x,-y)\), \(x,y\ge0\), zero would lie in the convex hull of these three points. Thus \(F\) avoids the entire closed lower-right quarter-square, which is covered by \(C,V_2,W\).

### 7. Two actual endpoints of the right central gap

Sections 7--10 preserve a supplementary historical route for inspection. They are not needed for R12's far-case closure; their local replacement transfer must be checked as specified below.

First \(C_R+U_2<\mu\): otherwise \(g+C_R\le B\), \(S_2+U_2\le B\), \(S_1<1\) would imply \(3\mu<3\). The nonempty interval \((C_R,\mu-U_2)\) on the right central line lies entirely in \(W\), endpoints included by closedness.

In local coordinates \(x\) down the right edge, \(y\) left along top, the source puts \(W\) into the target-dominating form
\[
0\le cx+sy\le1,\qquad-\beta\le-sx+cy\le1-\beta,
\]
\[
c,s>0,\quad c^2+s^2=1,\quad
\max(0,1-c/s)\le\beta\le\min(1,s/c).
\]
The claimed two adjustments move only edges redundant in the first quadrant. The displayed projection intervals describe the output, with
\[
A=\beta/s,\quad D=(1-\beta)/c,\quad sA+cD=1,\quad cA\le1,\ sD\le1.
\]
**Local protocol obligation.** Target containment alone does not preserve the preceding gap, its endpoints, or host representative. The source does not give a complete output-reclassification map for these two adjustments. Any use of the following endpoint/angle consequences must either establish that map or rerun Sections 3--6 on the new family and retain only the resulting surviving branch. R12's final argument does not depend on this normalization.

Write \(\tau=(1-c)/s\in(0,1)\) for the source's \(u\), the half-angle of \(W\):
\[
c=\frac{1-\tau^2}{1+\tau^2},\qquad s=\frac{2\tau}{1+\tau^2}.
\]
Its horizontal chord reaches at most \(X=(1-\mu c)/s<\tau\) leftward from the right edge. Containing the left gap endpoint requires
\[
C_R>\mu-\tau. \tag{5}
\]
Containing the right endpoint gives
\[
s(\mu-A)\le cU_2<ct_2. \tag{6}
\]
These preserve the position of the floating chord, not only its length. If \(b\) is the bottom-right reach of \(C\), and \(r=C_R\), its local half-angle \(\eta\) gives
\[
b<\eta,\quad r<\frac{1-\eta}{1+\eta},\qquad
\eta+\frac{1-\eta}{1+\eta}
+\eta\frac{1-\eta}{1+\eta}=1.
\]
Thus \(b+r+br<1\). Since \(b\ge\mu-S_2\), (5) implies
\[
2S_2+2\tau-S_2\tau-2>0. \tag{7}
\]
Also (4) gives \(D\ge2\mu-L_4>2-\sqrt2>7/12\).

### 8. Excluding the middle half-angle band

Set \(t=t_2,L=L_2,S=S_2\). Equations (7) and the corner formula imply
\[
S>\frac{2(1-\tau)}{2-\tau},\quad
t<T(\tau)=\frac{\tau}{4-3\tau},\quad
L\le F_\tau(t)=\frac{\tau+(4-3\tau)t^2}{2t(2-\tau)}.
\]
From (6), \(sA+cD=1\), and \(D>7/12\),
\[
D<\frac{1-\tau}{1+\tau}+t,\qquad
t>r_*(\tau)=\frac{19\tau-5}{12(1+\tau)}.
\]
Right joining and \(D>7/12\) also give
\[
L>m(\tau)=\frac{-19\tau^2+48\tau-5}{24\tau}.
\]
Divide \([1/3,7/8]\) into three intervals.

1. On \([1/3,2/5]\), \(L\le(1+T^2)/(1-T^2)<m(\tau)\). Their difference has positive denominator \(24\tau(2-\tau)(1-\tau)\) and numerator
\[
-19\tau^4+75\tau^3-115\tau^2+63\tau-10,
\]
whose exact Bernstein coefficients are all positive.
2. On \([2/5,3/4]\),
\[
r_*-T=\frac{-69\tau^2+79\tau-20}{12(1+\tau)(4-3\tau)}>0.
\]
The numerator is concave with endpoint values \(14/25,7/16>0\), contradicting \(r_*<t<T\).
3. On \([3/4,7/8]\), in the feasible range \(r_*<t<T\), the function \(F_\tau(t)\) decreases since \(t^2<T\). Hence \(L\le F_\tau(r_*)\), but \(m>F_\tau(r_*)\). Their difference has positive denominator \(24\tau(2-\tau)(1+\tau)(19\tau-5)\) and numerator
\[
361\tau^5-429\tau^4-1682\tau^3+2345\tau^2-745\tau+50,
\]
with all exact Bernstein coefficients positive on that interval.

The source records coefficients and reconstruction identities derived from the geometric formulas, plus an UNSAT nonlinear query over the entire middle band. These are certificate claims to review, not newly executed checks.

### 9. Excluding small half-angles using an interior point

For \(0<\tau<1/3\), take \(z=(1/3,2\tau/3)\), strictly inside the target.

For the half-angle \(\eta\) of \(C\), (5) and \(C_R<(1-\eta)/(1+\eta)\) imply \(\eta<\tau/(2-\tau)\). At \(x=1/3\), the upper height of \(C\) is at most
\[
\frac{2\eta^2+2\eta/3}{1-\eta^2}
\le\frac{\tau(1+\tau)}{3(1-\tau)}<2\tau/3,
\]
so \(z\notin C\). The first projection of \(W\) already exceeds its bound even after relaxing \(\mu\) to one:
\[
c(1-2\tau/3)+(2/3)s-1
=\frac{2\tau(1-3\tau+\tau^2)}{3(1+\tau^2)}>0.
\]
Thus \(z\notin W\). Its squared distances from the corner anchors of \(V_1,V_4\) are respectively greater than \(25/9\) and at least \(193/81\), both exceeding two. Finally \(t_2<T(\tau)<1/9\); the numerator by which the first projection of \(V_2\) exceeds its unit bound is at least
\[
(2\tau/3)(1-t_2^2)+4t_2/3-2t_2^2>0.
\]
Therefore coverage forces \(z\in F\).

The left bottom gap endpoint and right central endpoint of \(C\) give \(2\mu-S_1-\tau<1\), hence \(S_1+\tau>1\). If \(h_1=t_1\), then \(S_1<(1-h_1)/(1+h_1)\) implies \(h_1<\tau/(2-\tau)<1/5\). Thus \(l=\mu-U_1>4/5\).

**Interior-point forcing lemma.** A unit tile containing \((-l,0)\) and \((1/3,2\tau/3)\), \(l>4/5,0<\tau<1/3\), contains zero. For positive normals \((c_F,s_F),(-s_F,c_F)\), the first endpoint projections straddle zero. If zero is excluded, the second projections must both be strictly positive, forcing \(s_F/c_F<2\tau\). The required first projection span
\[
f(\theta)=(l+1/3)\cos\theta+(2\tau/3)\sin\theta
\]
must be at most one for \(\theta\in[0,\arctan(2\tau)]\). This concave function exceeds one at both ends: at zero it exceeds \(17/15\); at the other endpoint it exceeds \((17/15+4\tau^2/3)/\sqrt{1+4\tau^2}\), whose squared comparison follows from
\[
64/225-(44/45)\tau^2+(16/9)\tau^4
\ge64/225-44/405>0.
\]
Axial cases directly contain zero. The source records a continuous query of this lemma. Since \(q_L,z\in F\), it contradicts \(o\notin F\).

### 10. The high-half-angle remainder

Subject to the Section 7 protocol obligation, any survivor must have
\[
\tau>7/8,\qquad c<15/113,\qquad s>112/113.
\]
The other forced conditions are: \(F\) misses bottom/right and fills the left-upper gap; right/top join; \(C\) fills bottom; \(q_L\in F\); \(F\) meets the upper vertical axis and avoids the lower-right quarter; \(H>0,D<S_1<1<\mu\).

Also \(A<\mu\): otherwise
\[
D\le(1-s\mu)/c<(1-\tau)/(1+\tau)<1/15,
\]
contrary to \(D>7/12\). Thus \(W\) has no midpoint; \(H\), and \(J\) if nonempty, float. Moreover \(S_2<1/2\): otherwise \(t_2\le1/3\), so \(D<(1-\tau)/(1+\tau)+t_2<1/15+1/3=2/5<7/12\). Finally \(S_1>2/3\): the bottom-right reach of \(C\) exceeds \(1-S_2\), so its central-right upper bound is less than \(S_2/(2-S_2)\); using its bottom-left endpoint and (5) gives
\[
S_1+\tau+\frac{S_2}{2-S_2}>2.
\]
Since \(S_2<1/2,\tau<1\), this yields \(S_1>2/3\), hence \(t_1<1/5,l>4/5\). These estimates allow \(\mu\downarrow1\), but do not close the high-angle remainder. The independent R12 boundary argument does.

<a id="R12"></a>
## R12. The noncentral non-corner tile must contain an outer midpoint

**Scope.** Source: S6_attack_round12.md, sections 1--10. This excludes all configurations in which \(C\) contains a midpoint and \(F\) contains none, and then separately excludes their sharing the same midpoint. It does not exclude configurations where \(C,F\) contain different midpoints. Its far-case closure uses R11.3--5 and endpoint propagation, bypassing the supplementary angle route R11.7--10.

### 1. Conventions, inputs, and the two selective representatives

Let \(S=[-\mu,\mu]^2\), \(\mu=a/2>1\), with corners \(V_1,V_2,V_3,V_4\) in the usual order. G5 has already been excluded, so \(C\) is the unique tile containing zero and \(o\notin F\). Initially assume \(C\) contains \(m_B=(0,-\mu)\), \(F\) contains no outer midpoint, and the right/top/left midpoints have corner hosts. A unit tile contains at most one target corner and at most one outer midpoint.

Selecting distinct hosts for right, top, left gives precisely
\[
(2,3,4),\quad(3,4,1),\quad(2,4,1),\quad(2,3,1).
\]
Left-right reflection pairs the first two and last two. The representatives are therefore:

1. Far: \(m_L\in V_1,m_R\in V_2,m_U\in V_4,W=V_3\).
2. Near: \(m_R\in V_2,m_U\in V_3,m_L\in V_4,W=V_1\).

Free means unselected; repeated ownership of a selected midpoint remains allowed. Local corner replacements require the protocol's complete output reclassification.

The corner grid bound is at most two, strictly below two when not axis aligned, as proved in R2 by its endpoint functions \(g_1,g_2\). The source records a recheck of the polynomial identities. For an anchored corner,
\[
L\ge\mu,\qquad L+S+U<2,\qquad S+U\le B<1. \tag{1}
\]
Its anchored chord excludes the other central line by area \(\mu^2/2>1/2\), and remote edges by diameter, so these lengths bound its full contribution.

For two genuinely nonempty parallel line intersections at distance \(\mu>1\), their full lengths have sum at most the common \(B(\mu)<1\). Alternatively, for the finitely many actual pairs in a hypothetical covering, choose a common \(B<1\). A direct strict proof uses \(c,s>0,c^2+s^2=1\): the chord profile is trapezoidal, with end ramps of width \(\min(c,s)\) and plateau width \(|c-s|\). Separation \(\mu>1>\max(c,s)\) puts the lines on opposite ramps, giving
\[
\frac{c+s-\mu}{cs}<\frac{c+s-1}{cs}<1,
\]
since \((1-c)(1-s)>0\). Axial tiles cannot meet both lines. Singleton tangencies are nonempty; empty intersections cannot be used.

The center/bottom anchor confines \(C\) to bottom. Let \(a_C,b_C\) be its bottom reaches left/right from \(m_B\), and \(C_L,C_R,C_U\) its left/right/upper central reaches. The one-sided long-chord bounds are
\[
a_C+b_C+\mu+C_L+C_U<2,\qquad
a_C+b_C+\mu+C_R+C_U<2, \tag{2}
\]
and the parallel bound is
\[
a_C+b_C+C_L+C_R\le B. \tag{3}
\]
Axial endpoint propagation R11.2 says that a unit tile containing \((-l,0),(\mu,y)\), \(l>0,\mu>1,y\in\mathbb R\), contains zero. Its translations, rotations, and reflections apply. The source records fresh continuous checks of propagation and related inputs. When using a quarter-square boundary budget, overlap only enlarges the sum of tile contributions and therefore weakens the necessary inequality \(4\mu\le\) that sum.

### 2. Far-case ownership reductions inherited from R11

Only R11.3--5 are used, not its later angle restrictions. Here \(V_1\) has left long leg and bottom short leg \(S_1\); \(V_2\) right long and bottom short \(S_2\); \(V_4\) top long and left short \(S_4\). The free corner has right/top legs \(A,D\) and floating central chords \(H,J\), with \(A+D+H+J\le2\).

R11.3 proves that \(F\) misses bottom. If it met bottom and the horizontal central line, its non-bottom boundary contributions would be redundant, and the two bottom/horizontal parallel bounds would give \(12\mu\le8+2\mu+2B<12\mu\). If its horizontal intersection were empty, a bottom-right chord forces incompatible bottom-left and left-central coverage by \(C\); a bottom-left chord forces right/top joins and a long-chord-budget contradiction for \(C\). Those three cases were proved separately, avoiding an empty-chord application.

Consequently \(C\) fills \(g=2\mu-S_1-S_2>0\). The endpoint \(q_L=(-\mu+U_1,0)\) cannot lie in \(C\), since \(B\ge g+\mu-U_1\ge3\mu-2B>B\). No other corner can replace it, so \(q_L\in F\). Propagation excludes \(F\) from right outer edge, and convexity excludes the positive horizontal axis. Hence
\[
L_2+A\ge2\mu,\qquad C_R+U_2+H\ge\mu.
\]
The bound \(g+C_R\le B\) forces \(H>0\). The genuine top/horizontal parallel pair of \(W\) then gives
\[
D\le2B-3\mu+S_1+S_2+U_2
\le3B-3\mu+S_1<S_1. \tag{4}
\]
If left joined, \(S_4>S_1+U_1+\epsilon\), \(\epsilon=2\mu-2>0\). A top join would force \(D>S_4\), contrary to (4). A top gap would put its far endpoint \((\mu-D,\mu)\) in \(F\), whose span from \(q_L\) has horizontal length \(2\mu-D-U_1>2\mu-S_1-U_1>1\) and vertical length \(\mu>1\), also impossible.

Thus left has a nonempty upper-half gap in \(F\), including its upper endpoint
\[
P_L=(-\mu,\mu-S_4)\in F.
\]
If \(F\) also contained a top-right point \((x,\mu)\), \(x>0\), translate the origin to the top midpoint: the pair becomes \((-\mu,-S_4),(x,0)\), and a reflected propagation lemma forces the forbidden top midpoint. The midpoint itself is also omitted, so \(F\) misses the entire top-right half. Top therefore joins. On the boundary of the upper-right quarter-square \(R=[0,\mu]^2\), the only possible contribution from \(F\) is on the positive vertical central segment: it misses right, top-right, and positive horizontal segments.

### 3. A new upper-right boundary budget closes the far case

Let \(f\ge0\) be the chord length of \(F\) on that positive vertical side; zero includes an empty intersection or a singleton. All grid contributions of \(W\) lie on \(\partial R\) and total at most two; \(V_1\) misses \(R\). The contributions of \(V_2,V_4,C,F\) give
\[
4\mu\le L_2-\mu+U_2+L_4-\mu+U_4+2+C_R+C_U+f. \tag{5}
\]
The full bottom gap and (2) give
\[
C_R+C_U<2-3\mu+S_1+S_2. \tag{6}
\]
If \(f=0\), the two anchored budgets make the right side of (5) strictly less than
\[
8-5\mu+S_1-S_4<9-5\mu<4\mu.
\]
If \(f>0\), \(F\) actually meets both left and vertical-central lines. Its full left chord contains the gap of length \(2\mu-L_1-S_4\), so
\[
f\le B-2\mu+L_1+S_4.
\]
With (6), the two anchored budgets make the right side of (5) strictly less than
\[
8-7\mu+B+L_1+S_1<10-7\mu+B<4\mu.
\]
Both cases contradict coverage. The entire far representative is excluded for \(\mu>1\), including the previously unresolved high-angle case.

### 4. Near-case parameters and the first host restriction

Now \(W=V_1\); \(V_2,V_3,V_4\) host right, top, left midpoints. Their long legs run up the right edge, left along top, and down the left edge; short legs are bottom \(S_2\), right \(S_3\), top \(S_4\). Let \(A,D\) be the bottom/left legs of \(W\), and \(H,J\) its actual horizontal/vertical central chord lengths, lying entirely on negative half-axes and possibly floating. The corner and center diameter exclude zero and the opposite half-axes. Then
\[
A+D+H+J\le2. \tag{7}
\]
Write the signed bottom-gap length \(g=2\mu-A-S_2\). If \(F\) misses bottom, \(a_C+b_C\ge g\), even when \(g\le0\); in that case no actual gap is asserted.

Necessarily \(D<\mu\). Otherwise \(W\) also hosts the left midpoint; choose it as that host, leaving \(V_4\) free, and reflect to obtain the excluded far representative. This reselects hosts without assuming actual uniqueness. Right/top/left joining means respectively
\[
L_2+S_3\ge2\mu,\quad L_3+S_4\ge2\mu,\quad L_4+D\ge2\mu. \tag{8}
\]
Any gaps lie in right-upper, top-left, left-lower open halves. The tile \(C\) cannot meet them, so each nonempty gap belongs entirely to \(F\).

### 5. No left gap in the near representative

If \(L_4+D<2\mu\), then \(F\) contains the left gap's lower endpoint
\[
P=(-\mu,-\mu+D),\qquad-\mu+D<0.
\]
Translated/rotated propagation excludes its top edge, bottom-right half, and positive horizontal half-axis; diameter excludes right. Therefore right and top join.

#### 5.1. Bottom also has a gap

If \(A+S_2<2\mu\), the far bottom-right endpoint \((\mu-S_2,-\mu)\) must lie in \(C\), since \(F\) misses bottom-right. Thus \(b_C\ge\mu-S_2\). On the lower-right quarter boundary, any bottom-right contribution of \(W\) lies inside this bottom chord of \(C\). Its lower vertical chord and any such chord of \(F\) are redundant in the whole lower vertical half-segment of \(C\); all their other boundary contacts are excluded. Neither \(V_3\) nor \(V_4\) contributes. Hence
\[
4\mu\le(b_C+\mu+C_R)+(\mu+S_2+U_2)
<2+\mu+B<4\mu,
\]
using (2) and (1), impossible.

#### 5.2. Bottom corners join

If \(A+S_2\ge2\mu\), then \(A>\mu\), so \(W\) gains a bottom-midpoint anchor. Consequently \(H=0\) and \(A+D+J<2\). Right/top joins imply
\[
S_3>S_2+U_2+\epsilon,\quad S_4>S_3+U_3+\epsilon,
\quad U_2+U_3<1.
\]
Bottom joining and the \(W\) budget give \(D<S_2-J-\epsilon\); the chain and \(S_4+U_4<1\) give \(S_2+U_3<1\). Hence \(D+U_3<1\).

The right central endpoint \(q_R=(\mu-U_2,0)\) must belong to \(C\), since \(W\) cannot meet the positive half-axis and \(F\) is excluded. The upper endpoint \(q_U=(0,\mu-U_3)\) belongs to \(C\cup F\) by closedness beyond the upper corner interval; it cannot lie in \(F\), because its span from \(P\) has horizontal length \(\mu>1\) and vertical length \(2\mu-D-U_3>1\). Thus \(q_U\in C\). Equation (2) now gives
\[
3\mu-U_2-U_3\le\mu+C_R+C_U<2,
\]
forcing \(U_2+U_3>3\mu-2>1\), a contradiction. Therefore left must join.

### 6. No top gap in the near representative

With left joined, suppose top has a gap. Its top-left contact in \(F\) excludes right and left-lower by propagation; bottom is too distant. Any left-upper chord is redundant in \(V_4\)'s long leg.

If the horizontal-central intersection of \(F\) is nonempty, including tangency, combine the bottom/horizontal bound of \(C\) and top/horizontal bound of \(F\):
\[
12\mu\le8+2\mu+2B<12\mu.
\]
If that intersection is empty, only \(C,V_2\) cover the positive horizontal half-axis, so \(C_R\ge\mu-U_2\). The signed bound \(a_C+b_C\ge g\), valid even for \(g\le0\), and (3) give
\[
B\ge g+C_R\ge3\mu-A-S_2-U_2,
\]
hence \(A\ge3\mu-2B>\mu\). Thus \(W\) is bottom anchored, \(H=0,A+D+J<2\). Left joining and the \(V_4\) budget give \(D>S_4+U_4+\epsilon\). Since \(F\) misses the horizontal line, the full horizontal chord of \(C\) has length at least \(2\mu-U_2-U_4\). Therefore
\[
\begin{aligned}
B&\ge g+2\mu-U_2-U_4\\
&=4\mu-A-S_2-U_2-U_4\\
&>4\mu-2+S_4+\epsilon-(S_2+U_2)\\
&\ge4\mu-2+S_4+\epsilon-B>B,
\end{aligned}
\]
impossible. Top must join.

### 7. No right gap in the near representative

If right has a gap, \(F\) contains a right-upper point. Propagation excludes bottom, top-left, and the negative horizontal half-axis; diameter excludes left. On the boundary of the upper-left quarter \(R=[-\mu,0]\times[0,\mu]\), it can contribute only a positive vertical-central chord, length \(f\ge0\).

The contributions from \(V_4,V_3,W,C\), with none from \(V_2\), imply
\[
4\mu\le S_4+U_4+L_3+U_3+H+C_L+C_U+f. \tag{9}
\]
Since \(F\) misses bottom, (2) and \(a_C+b_C\ge g\) yield
\[
C_L+C_U<2-3\mu+A+S_2. \tag{10}
\]
If \(f=0\), (10), the two corner budgets, (7), and left joining make the right side of (9) strictly less than
\[
8-5\mu+S_2-S_3<9-5\mu<4\mu.
\]
If \(f>0\), \(F\) really meets right and vertical-central lines. Its right chord contains the full gap \(g_R=2\mu-L_2-S_3>0\), so
\[
f\le B-2\mu+L_2+S_3.
\]
Then the right side of (9) is strictly less than
\[
6-5\mu+B+(A+H)+(L_2+S_2)-L_4
<10-5\mu+B-(D+L_4)
\le10-7\mu+B<4\mu,
\]
again impossible.

### 8. No near representative with all three joins

Finally assume right, top, and left all join. Their strict chain is
\[
S_3>S_2+U_2+\epsilon,\quad S_4>S_3+U_3+\epsilon,
\quad D>S_4+U_4+\epsilon,
\]
so
\[
D>S_2+U_2+U_3+U_4+3\epsilon, \tag{11}
\]
\[
A+H<2-S_2-U_2-U_3-U_4-3\epsilon. \tag{12}
\]
In particular \(A+S_2<2<2\mu\); bottom has a genuine gap.

#### 8.1. F meets bottom

All other outer contributions of \(F\) are redundant because those edges join. If its horizontal-central intersection is nonempty, the two bottom/horizontal bounds give \(12\mu\le8+2\mu+2B<12\mu\).

If its horizontal intersection is empty, its bottom chord lies in one open half. For a bottom-left chord, \(C\) covers the bottom-right gap endpoint and right central endpoint, so \(b_C\ge\mu-S_2,C_R\ge\mu-U_2\), giving
\[
B\ge b_C+C_R\ge2\mu-S_2-U_2\ge2\mu-B>B.
\]
For a bottom-right chord, \(a_C\ge\mu-A\), a valid weak bound even if negative. Horizontal coverage requires
\[
C_L+C_R+H+U_2+U_4\ge2\mu.
\]
Using (3),(12),
\[
B\ge a_C+C_L+C_R\ge3\mu-A-H-U_2-U_4
>3\mu-2+S_2+U_3+3\epsilon>1,
\]
also impossible.

#### 8.2. F misses bottom

The whole positive gap \(g\) lies in \(C\). Since \(F\) omits zero, its horizontal chord cannot meet both open half-axes. If it has no positive-half point, \(C_R+U_2\ge\mu\). Equations (2),(12) imply
\[
2>g+\mu+C_R\ge4\mu-A-S_2-U_2
>4\mu-2+U_3+U_4+3\epsilon>2.
\]
If it has a positive-half point, it has no negative-half point; thus \(C_L+H+U_4\ge\mu\), and
\[
2>g+\mu+C_L\ge4\mu-A-H-S_2-U_4
>4\mu-2+U_2+U_3+3\epsilon>2.
\]
All alternatives fail.

### 9. Exhaustion and the first global consequence

The far representative closes in Section 3. In the near representative, Section 4 excludes \(D\ge\mu\) by host reselection into the far case; Section 5 excludes left gaps; Sections 6--8 exhaust top gap, right gap, and all joins. Hence the entire class "\(C\) has a midpoint, \(F\) has none" is impossible for every \(\mu>1\).

R10's G1 exclusion says at least one non-corner tile has a midpoint. Since only \(C\) having one is now excluded, \(F\) must have one. This does not yet exclude both sharing the same midpoint; that case is handled next without presupposing disjoint ownership.

### 10. Separate exclusion of a shared midpoint

Assume \(C,F\) both contain \(m_B\), with \(o\in C,o\notin F\). Each has at most one midpoint. The other three still have corner hosts, giving the same far/near representatives.

The tile \(F\) misses top and both upper side halves: distance from \(m_B\) has vertical difference at least \(\mu\), and side contact adds horizontal difference \(\mu\), exceeding diameter. It also misses the positive vertical central half-axis, since convexity with \(m_B\) would give zero. Its vertical-central interval is therefore redundant in the negative half-segment of \(C\). The combined vertical-central length is at most the full chord of \(C\), bounded by \(\sqrt2\).

#### 10.1. Far representative, or near representative with a left join

In the far case, possible lower side chords of \(F\) are already covered by long legs of \(V_1,V_2\). In the near case with left joined, the left chord is redundant in \(V_4,W\), and right-lower in \(V_2\). Thus all non-bottom outer contributions are redundant.

If the horizontal-central intersection of \(F\) is nonempty, including a singleton,
\[
12\mu\le8+2B+\sqrt2<12,
\]
impossible. If it is empty, use the bottom/horizontal bound only for \(C\), bottom length at most \(\sqrt2\) for \(F\), and effective vertical-central length at most \(\sqrt2\):
\[
12\mu\le8+B+2\sqrt2<12,
\]
using \(B<1,2\sqrt2<3\). No empty-chord parallel estimate is made.

#### 10.2. Near representative with a left gap

Right and top gaps lie on right-upper and top-left halves, which neither \(C\) nor \(F\) can reach; therefore those edges join. The left-gap lower endpoint
\[
P=(-\mu,-\mu+D),\qquad0\le D<\mu,
\]
belongs to \(F\). If \(F\) contained a positive horizontal point \(Q=(x,0)\), \(x>0\), its triangle with \(m_B,P\) would have area
\[
(\mu^2+Dx)/2>1/2.
\]
Thus \(F\) misses the positive horizontal half-axis, and also the positive vertical half-axis as already shown. Closedness beyond the corner intervals forces
\[
q_R=(\mu-U_2,0),\qquad q_U=(0,\mu-U_3)
\]
both into \(C\). Right/top joins give \(S_3>S_2+U_2+\epsilon,S_4>S_3+U_3+\epsilon\), hence \(U_2+U_3<1\). But the long-chord bound yields
\[
3\mu-U_2-U_3\le\mu+C_R+C_U<2,
\]
so \(U_2+U_3>3\mu-2>1\), impossible.

This exhausts the shared-midpoint case. Therefore all G2 configurations in which \(C\) has a midpoint are excluded, whether \(F\) has none or has the same midpoint. Different midpoint ownership belongs to G3/G4 and is outside this assertion. Combining G1 and G5, every hypothetical cover now has a midpoint in \(F\); if \(C\) also has one, it is different. The remaining G2 representative has no midpoint in \(C\) and one in \(F\).

<a id="technical-part-C"></a>
# Technical Part C. Adjacent owned midpoints

Modules: [R20](#R20), [R20A](#R20A), [R21](#R21), [R21A](#R21A), [R22](#R22), [R22A](#R22A), [R23](#R23).

<a id="R20"></a>
## R20. Opposite and adjacent midpoint representatives in G3 and G4

**Scope.** Source: S6_attack_round20.md, sections 1, 2, and 4--7. The T8 remainder in Section 6 is closed by R21. The overly broad right-gap candidate mentioned in Section 5 is corrected by R21.7. Selective hosts never imply unique actual ownership.

### 1. Common setup and finite host classification

Let \(S=[-\mu,\mu]^2\), \(\mu>1\), with corners \(V_1,V_2,V_3,V_4\) lower-left through upper-left. Earlier results give a unique center tile \(C\), with \(O\notin F\) and an outer midpoint in \(F\). Here \(C\) contains a different midpoint. Rotate so \(L=(-\mu,0),O\in C\). A unit tile cannot contain two outer midpoints. The long chord \(LO\) excludes top/bottom contacts by triangle area greater than \(1/2\), and right by distance \(2\mu>\sqrt2\). Thus \(C\) meets only left. Let \(\ell\) be its full left-edge chord, and \(r,u\) its right/upper central reaches. The long-chord budget is
\[
\mu+r+\ell+u<2. \tag{1}
\]
Its left and vertical-central intersections are genuinely nonempty, so their lengths sum to at most \(B=B(\mu)<1\).

In G3, \(R=(\mu,0)\in F\). Top/bottom corner hosts, up to upper-lower reflection, have three representatives: top \(V_4\), bottom \(V_1\) (both on the \(C\) side); top \(V_3\), bottom \(V_2\) (both on the \(F\) side); or top \(V_4\), bottom \(V_2\) (split).

In G4, \(B_0=(0,-\mu)\in F\). The possible injective selections (top host, right host) are
\[
(3,2),\qquad(4,2),\qquad(4,3).
\]
The last is T8. This module focuses on \((4,2)\) and T8. Other corners may duplicate midpoint ownership.

For each locally standardized anchored corner,
\[
L_i\ge\mu,\quad L_i+S_i+U_i<2,\qquad S_i+U_i\le B<1. \tag{2}
\]
Any free corner has full grid contribution at most two. Replacements dominate the old target intersection; if they fill a former gap, the output must enter a join branch. Old gaps cannot be treated as actual after they disappear, and all changed predicates must be reclassified.

### 2. G3: a nonempty vertical chord of F requires an outer gap

The tile \(F\) contains \(R\), so cannot meet left. Its horizontal-central intersection lies entirely on the positive half-axis, because otherwise convexity gives \(O\in F\).

Suppose its vertical-central intersection is nonempty and both top and bottom corners join. Their extra top/bottom chords are then redundant. The corners contribute at most eight to the grid; the horizontal-central union of \(C,F\) is at most \(2\mu\). The left/vertical-central pair of \(C\) contributes at most \(B\), as does the right/vertical-central pair of \(F\). Thus
\[
12\mu\le8+2\mu+2B<12\mu,
\]
impossible. At least one top/bottom edge has a corner gap, which must lie entirely in \(F\). Both cannot, since opposite outer lines are \(2\mu>\sqrt2\) apart. Exactly one does.

If top has the gap, \(F\) cannot contain a negative vertical point \((0,-d)\), \(d>0\): that point and a top outer point force the origin by rotated propagation. The bottom-gap version excludes positive vertical points. Hence
\[
F\cap V_0\ne\varnothing\quad\Longrightarrow\quad
\begin{cases}
\text{top gap in }F,\ \ F\cap V_0\text{ lies on the positive half-axis},\\
\text{or bottom gap in }F,\ \ F\cap V_0\text{ lies on the negative half-axis}.
\end{cases} \tag{3}
\]
Tangency at a nonzero axis point is nonempty. The entirely empty vertical intersection remains a separate branch.

### 4. G4 diagonal hosts (4,2): no positive horizontal chord of F

Here \(V_2\) hosts right, with right long leg \(L_2\) and bottom short leg \(S_2\); \(V_4\) hosts top, with top long leg \(L_4\) and left short leg \(S_4\). The free corners are \(V_1,V_3\). Let \(A,D\) be actual bottom/left legs of \(V_1\), with \(A+D\le2\).

On the upper-right quarter boundary \(R_+=[0,\mu]^2\), \(V_1\) is too far to contribute; \(V_2,V_4\) contribute \(L_2-\mu+U_2,L_4-\mu+U_4\); \(V_3\) contributes at most two by the universal boundary lemma; \(C\) contributes \(r+u\). Because \(F\) contains \(B_0\), it misses top, right-upper, and positive vertical segments; only a positive horizontal chord of length \(f\) can contribute. Therefore
\[
4\mu\le L_2-\mu+U_2+L_4-\mu+U_4+2+r+u+f,
\]
and (1),(2) give
\[
4\mu<8-3\mu-S_2-S_4-\ell+f. \tag{5}
\]
If \(F\) contains a positive horizontal point \((p,0)\), \(p>0\), it cannot meet any left-edge point \((-\mu,y)\), \(-\mu\le y\le\mu\): its triangle with \(B_0,(p,0)\) has twice area
\[
\mu^2+p(y+\mu)>1,
\]
including \(y=-\mu\). Thus all left gaps are filled by \(C\), all bottom gaps by \(F\). With \(b\) its full bottom chord, the signed lower bounds
\[
\ell\ge2\mu-D-S_4,\qquad b\ge2\mu-A-S_2
\]
remain valid when negative. Both bottom and horizontal intersections of \(F\) are nonempty, so \(b+f\le B\). The right side of (5) is consequently at most
\[
\begin{aligned}
8-3\mu-S_2-S_4-\ell+B-2\mu+A+S_2
&\le8-7\mu+B+A+D\\
&\le10-7\mu+B<4\mu,
\end{aligned}
\]
a contradiction. Thus \(F\) has no positive horizontal point in this representative. (6)

### 5. The diagonal-host remainder must join on the left

Now \(F\)'s horizontal intersection is empty or negative, so \(f=0\) in (5). If left had a genuine gap, its upper endpoint \(P=(-\mu,\mu-S_4)\) lies in the left-upper half because \(S_4<1<\mu\). Its distance from \(B_0\in F\) exceeds \(\sqrt2\), so closedness gives \(P\in C\). With \(L\in C\), \(\ell\ge\mu-S_4\). Then
\[
4\mu<8-4\mu-S_2<4\mu,
\]
impossible. Hence
\[
D+S_4\ge2\mu. \tag{7}
\]
Thus \(D>\mu\): \(V_1\) actually duplicates the left midpoint. A target-dominating standardization may denote its left long leg \(L_1\), bottom short leg \(S_1\), and central segment \(U_1\), preserving the join; reclassify other predicates by the protocol.

If \(F\)'s negative horizontal chord is nonempty, propagation excludes its right boundary contact. Neither \(C\) nor \(F\) meets top, so right/top join as well:
\[
L_2+A_3\ge2\mu,\qquad L_4+D_3\ge2\mu.
\]
This is R13's far three-join geometry, with \(C\) additionally containing left midpoint. Section 7 verifies that its \(J=0\) exclusion allows that extra midpoint. Thus the negative-horizontal branch requires \(J_3>0\), but is not excluded. The source also retained an empty-horizontal case with a possible right gap; R21.7 corrects that overbroad allowance: its right gap is geometrically impossible.

### 6. T8 (4,3): no nonempty negative horizontal chord of F

Now \(V_3\) hosts right, with right long leg \(L_3\), top short leg \(S_3\); \(V_4\) hosts top, with top long leg \(L_4\), left short leg \(S_4\). Initially \(V_1,V_2\) are free.

First \(V_1\) must duplicate the left midpoint. On the upper-left quarter \(R_-=[-\mu,0]\times[0,\mu]\), \(V_2\) is too far and the long right chord of \(V_3\) excludes any point by twice triangle area at least \(\mu^2>1\). The tile \(F\) misses top, left-upper, and positive vertical segments; any negative horizontal contribution is redundant in \(LO\subset C\). The tile \(V_1\) misses top and right of this quarter; if it did not contain the left midpoint, it would miss its left-upper edge as well. Only \(C,V_4\) could cover the quarter boundary, contrary to the two-tile boundary exclusion. More quantitatively,
\[
D_1-\mu\ge2\mu-2B,\qquad D_1\ge3\mu-2B>\mu.
\]
Indeed \(C,V_4\) cover the full lower/upper horizontal edges of \(R_-\); each contributes at most \(B\) to its two vertical edges, so the missing length must come from the left-upper part of \(V_1\). This is retained duplicate ownership.

Only \(V_3,V_4\) can cover top, so
\[
L_4+S_3\ge2\mu. \tag{8}
\]
Suppose \(F\) has no positive horizontal point. If left still has a gap, its upper endpoint belongs to \(C\), giving \(\ell\ge\mu-S_4\). Let \(H_2\) be the actual positive horizontal chord length of \(V_2\). Coverage gives
\[
r+U_3+H_2\ge\mu,\qquad u+U_4\ge\mu.
\]
All other potential hosts are excluded by the stated midpoint/diameter restrictions. By (1),
\[
H_2>4\mu-2-S_4-U_3-U_4.
\]
Equation (8) and the \(V_4\) budget give \(S_4+U_4<2-2\mu+S_3\), hence
\[
H_2>6\mu-4-(S_3+U_3)>6\mu-5>1. \tag{9}
\]
But any corner tile's chord on a central line at inward distance \(\mu>1\) is strictly shorter than one: in \(0\le cX+sY\le1\), its chord at \(Y=\mu\) is at most \((1-s\mu)/c<(1-s)/c<1\). An axial tile misses the line. This needs no midpoint anchor for \(V_2\). Therefore
\[
D_1+S_4\ge2\mu. \tag{10}
\]
If \(F\)'s negative horizontal chord is nonempty, propagation also excludes right boundary contact, forcing right joining. Reflecting left/right gives the near three-join geometry of Section 7, with an extra right midpoint in \(C\); that lemma allows the extra midpoint. Thus
\[
\text{T8 with nonempty negative horizontal intersection of }F\text{ is excluded}. \tag{11}
\]
At this stage the source leaves empty-horizontal T8 with left joining, and positive-horizontal T8 with top joining but not both side joins. R21 later closes both. These are historical intermediate remainders, not final claims.

### 7. Exact applicability of the historical geometric lemmas

No G2 label is transferred wholesale to G4. Rechecking R13's premises gives the following two geometric statements.

**Near three-join lemma.** Suppose \(F\) contains bottom midpoint and omits center; \(V_2,V_3,V_4\) host right, top, left; \(W=V_1\); right/top/left join; and \(F\)'s horizontal intersection is nonempty. This is impossible. The tile \(C\) contains center and is allowed an outer midpoint.

The proof first excludes bottom contact by \(C\) using two actual bottom/horizontal parallel pairs and the grid budget. With \(C\) missing bottom, let \(A,D,H,J\) be the actual free-corner lengths, \(b,f\) the bottom/horizontal lengths of \(F\), and \(h_C\) the full horizontal chord length of \(C\). Then
\[
b\ge2\mu-A-S_2,\quad b+f\le B,\quad
h_C+f+U_2+U_4+H\ge2\mu,\quad A+D+H+J\le2.
\]
Left/top joins imply
\[
h_C>6\mu-B-2-L_3-S_2-U_2+\epsilon,\qquad\epsilon=2\mu-2.
\]
The R13 adjacent-corner certificate and \(U_2<t_2\) give
\[
L_3+S_2+U_2+2t_3-t_3^2<2.
\]
Thus \(h_C>6\mu-B-4+2t_3-t_3^2+\epsilon\). Since \(F\) misses the positive vertical axis, \(C\)'s upper reach \(u>1-t_3\), and
\[
h_C+u^2>8\mu-B-5>2,
\]
contrary to the three-ray parabola. No step assumes that \(C\) has no midpoint.

**Far \(J=0\) lemma.** For hosts \(V_1\) left, \(V_2\) right, \(V_4\) top, with \(W=V_3\), three non-bottom joins and nonempty horizontal \(F\), one must have \(J>0\), again allowing a midpoint in \(C\). Bottom contact by \(C\) is first excluded by the grid. If \(J=0\), the bottom/horizontal bound of \(F\), free-corner budget, and right/top joins imply
\[
h_C>8\mu-B-2-L_2-L_4-S_1-S_2-U_1-U_2.
\]
The left adjacent-corner budget and strict \(V_2\) budget give
\[
h_C>8\mu-B-6+2t_4-t_4^2.
\]
Since \(u>1-t_4\), the same contradiction \(h_C+u^2>8\mu-B-5>2\) follows.

These are extensions obtained by checking actual premises, not unrestricted imports of R14--R19 G2 conclusions. The source records a recheck of R13's two complete parameter rectangles, 266 rational coefficients, and one NRA query; those certificate artifacts remain the exact algebraic review input.

<a id="R20A"></a>
## R20A. Excluding a duplicated left midpoint in the same-side G4 representative

**Scope.** Source: S6_attack_round20_addendum.md, sections 1--5. Here \(C\) contains center/left midpoint, \(F\) contains bottom midpoint and omits center, and \(V_2,V_3\) host right/top. This excludes the extra hypothesis that \(V_4\) also contains left midpoint. The joins are derived from these actual anchors, not from a G2 classification label.

### 1. Actual anchors force right and top joins

Use \(S=[-\mu,\mu]^2\), \(\mu>1\), with \(L=(-\mu,0)\), \(B_0=(0,-\mu)\). Suppose \(L,O\in C\), \(B_0\in F\), \(O\notin F\); right/top are in \(V_2,V_3\); and \(L\in V_4\). Locally standardize the three anchored corners by target-dominating replacements, preserving all old target points and anchors, with complete output reclassification. Let their half-angles be \(x=t_2,y=t_3,z=t_4\). Keep the actual bottom/left legs \(A,D\) of \(W=V_1\).

The tile \(C\) meets only left, and \(F\) misses top. Thus \(L_3+S_4\ge2\mu\). Any right corner gap lies in the right-upper half: \(V_2\)'s long leg reaches above right midpoint and \(S_3<1<\mu\). Neither \(C\), anchored at left, nor \(F\), anchored at bottom, can reach it by diameter. Hence \(L_2+S_3\ge2\mu\).

R17's single-corner lemma, writing its auxiliary ratios as \(\rho_i=(L_i-1)/(3-L_i)\), gives
\[
y<\rho_2<\min(x,1-x),\quad y<4/15,\quad
z<\rho_3\le\frac{y^2}{1-2y^2}.
\]
Define
\[
\delta=\frac{2y^4}{(1-y^2)(1-3y^2)}.
\]
The cosine projection bound gives \(L_4<1+\delta\), with \(0<\delta<y^2\).

### 2. F has a positive horizontal intersection

Otherwise both central endpoints \(q_R=(\mu-U_2,0)\), \(q_U=(0,\mu-U_3)\) must lie in \(C\); the other corners and \(F\) are excluded by their anchors or distance. Thus its actual reaches satisfy
\[
r>1-x,\qquad u>1-y,\qquad r+u>2-x-y>1.
\]
But \(C\) also contains the actual left point \(L\), and R17's outer-point lemma with its local displacement \(e=0\) gives \(r+u<1\), a contradiction.

Thus \(F\)'s horizontal chord is nonempty and entirely positive. For any positive point \((p,0)\in F\), a left-edge point \((-\mu,y_L)\) would form with \(B_0\) a triangle of twice area \(\mu^2+p(y_L+\mu)>1\). Therefore \(F\) misses left. It still misses the positive vertical axis, so \(q_U\in C\) and \(u>1-y>11/15\).

### 3. The left midpoint forces a very short right reach of C

Write its normals as \((c,\varepsilon s),(-\varepsilon s,c)\), \(c\ge s\ge0,c^2+s^2=1\). The axial case cannot contain \(LO\) of length \(\mu>1\). For \(\varepsilon=+1\), \(L,(0,u)\) give \(c\mu+su\le1\), hence \(u<(1-c)/s\le\sqrt2-1<11/15\), impossible. Thus \(\varepsilon=-1\).

Put \(\eta=s/(1+c)\in(0,\sqrt2-1]\), the central half-angle (source \(h\)). The second normal gives \(s\mu+cu\le1\); since \(\mu>1,u>1-y\),
\[
s+c(1-y)<1,\qquad \frac{2\eta}{1+\eta}<y,\qquad
\eta<\frac{y}{2-y}.
\]
If \(r_C\) is the actual right reach, the first normal bounds its horizontal span from \(L\):
\[
c(\mu+r_C)\le1,\qquad
r_C<1/c-1=\frac{2\eta^2}{1-\eta^2}
<\frac{y^2}{2(1-y)}<y^2. \tag{1}
\]
This uses the midpoint already in \(C\), without assuming a left gap.

### 4. Left coverage rules out a bottom join

The actual left chord \(\ell\) of \(C\) and its upper reach satisfy \(\ell+u\le B<1\), so \(\ell<y\). Since \(F\) misses left,
\[
D+L_4+\ell\ge2\mu,\qquad D>1-y-\delta. \tag{2}
\]
This is valid whether left corners join or leave a gap.

Suppose bottom joins: \(A+S_2\ge2\mu\). As \(S_2<1<\mu\), \(W\) actually contains bottom midpoint. A target-dominating standardization has half-angle \(w\), left short leg \(S_1\ge D\); reclassify any other output predicates. Its bottom join yields
\[
x<\rho_1<\min(w,1-w),\qquad x<4/15,
\]
so \(D\le S_1<(1-w)/(1+w)<1-x\). Right joining also gives \(y<x^2/(1-2x^2)\). With \(\delta<y^2\),
\[
y+\delta<\frac65x^2+\frac{36}{25}x^4
<\frac{34}{75}x<x/2
\]
using \(x<1/3\). Equation (2) now gives \(D>1-x/2\), a contradiction. Therefore bottom has a genuine nonempty gap.

### 5. The bottom chord and central joining chord of F are too long

The tile \(C\), anchored at center/left, misses bottom. Hence both bottom gap endpoints lie in \(F\). Its far endpoint \(R_B=(\mu-S_2,-\mu)\) and \(B_0\) give full bottom length
\[
b\ge\mu-S_2>\frac{2x}{1+x}. \tag{3}
\]
On the positive horizontal axis, \(V_3\)'s top anchor excludes the horizontal line; \(V_4\) meets only the negative half; \(W\) is too far. Thus \(C,F\) alone join over \([0,\mu-U_2]\). If the actual horizontal chord of \(F\) is \([\alpha,\beta]\),
\[
\alpha\le r_C<y^2,\qquad\beta\ge\mu-U_2>1-x,
\]
so \(f>1-x-y^2\); tangency cannot supply this joining interval.

Let \(m=\min(x,1-x)>0\). The right join gives \(y<m,y<4/15\), whence
\[
y^2<(4/15)m<m/3\le\frac{x(1-x)}{1+x}.
\]
The last inequality is checked separately for \(x\le1/2\) and \(x\ge1/2\). Consequently
\[
b+f>1+\frac{x(1-x)}{1+x}-y^2>1.
\]
Both the bottom and horizontal intersections of this same actual \(F\) are nonempty, contradicting \(b+f\le B<1\). Thus the entire G4 \((3,2)\) branch with a duplicated left midpoint in \(V_4\) is excluded.

<a id="R21"></a>
## R21. Excluding T8 and refining the remaining midpoint representatives

**Scope.** Source: S6_attack_round21.md, sections 1--8. Sections 1--4 close G4 T8 for every target side greater than two. Subsequent sections eliminate a G3 host subclass, constrain duplicate ownership in the two remaining G4 representatives, correct an earlier right-gap allowance, and record a G2 boundary consequence. The statements keep their separate geometric hypotheses.

### 1. T8: actual anchors force left and top joins

Let \(S=[-\mu,\mu]^2\), \(\mu=a/2>1\), with corners in the usual order. Assume \(O,L=(-\mu,0)\in C\), \(B_0=(0,-\mu)\in F\), \(O\notin F\); \(V_3\) hosts right midpoint and \(V_4\) top. Since \(C\) meets only left and \(F\) misses top, top corners join. Locally standardize \(V_3,V_4\) by target-dominating replacements, retaining anchors and old target coverage and reclassifying all output cases.

Only \(C\) and the inward top segment \(U_4\) can cover the positive vertical central axis: \(F\) cannot cross zero from \(B_0\); the right anchor of \(V_3\) excludes that line; both bottom corners are too far. Thus \(u\ge\mu-U_4\), where \(u\) is the actual upper reach of \(C\).

If left has a genuine corner gap, its upper endpoint \(P=(-\mu,\mu-S_4)\) is in \(C\), since its distance from \(B_0\in F\) exceeds \(\sqrt2\). Then the full left chord \(\ell\ge\mu-S_4\). The nonempty parallel pairs of \(C\) and anchored \(V_4\) give
\[
2\mu-S_4-U_4\le B,\qquad S_4+U_4\le B,
\quad\Longrightarrow\quad2\mu\le2B<2.
\]
Thus left joins. Its actual leg \(D_1\) in \(V_1\) satisfies \(D_1+S_4\ge2\mu\), hence \(D_1>\mu\); \(V_1\) actually duplicates \(L\). This holds for every horizontal type of \(F\), stronger than R20's nonpositive-horizontal reduction. A local standardization of \(V_1\) retains the join; keep \(V_2\) as the original free tile.

### 2. Angle cascades and joint projections of C

Let the half-angles of \(V_1,V_4,V_3\) be \(w,x,y\). Anchored corners have
\[
L_i\ge\mu,\quad L_i+S_i+U_i<2,\quad U_i<t_i,
\quad S_i<\frac{1-t_i}{1+t_i}.
\]
The joins \(L_1+S_4,L_4+S_3\ge2\mu\) and R17's auxiliary ratio \(\rho=(L-1)/(3-L)<\min(t,1-t)\), \(\rho<4/15\), yield
\[
0<x<4/15,\quad x<\rho_1<w,\quad
0<y<\rho_4\le\frac{x^2}{1-2x^2}<\frac65x^2<\frac{32}{375}.
\]
Define the actual cosine excess
\[
\epsilon_y=\frac{2y^2}{1-y^2},\qquad \Delta(x)=\frac{x^2}{2(1-x)}.
\]
Here \(L_3\le1+\epsilon_y\), with a weak sign at this same actual angle. Since \(y<4/15\),
\[
\epsilon_y<y,\quad\epsilon_y<3y^2,\qquad
y+\epsilon_y<\frac{1256}{3125}x<\frac5{12}x. \tag{1}
\]
For the last bound, use \((6/5)x^2+(108/25)x^4\) and compare after dividing by \(x<4/15\).

Left joining gives a stronger angle gap. From the cosine cap of \(V_1\) and \(x<\rho_1\),
\[
L_1>\frac{1+3x}{1+x},\qquad
w^2>\frac{x}{1+2x}>\frac94x^2,
\]
because \((9/4)x(1+2x)<23/25<1\). Therefore
\[
w>3x/2. \tag{2}
\]
Now \(u>1-x>11/15\). Choose normals of \(C\) as \((c,\varepsilon_Cs),(-\varepsilon_Cs,c)\), \(c\ge s\ge0,c^2+s^2=1\). Axial directions cannot contain \(LO\) of length \(\mu>1\). The positive sign would give \(c\mu+su\le1\), hence \(u<(1-c)/s\le\sqrt2-1\), impossible. Thus the sign is negative. With central half-angle \(\eta=s/(1+c)\), the actual left/upper endpoints give \(\eta<x/(2-x)\). Projections of the actual right/lower endpoints yield
\[
r<\Delta(x),\qquad d<\eta<\frac{x}{2-x}. \tag{3}
\]
The latter uses \(c\mu+sd\le1\). Put \(E=y+\epsilon_y+\Delta(x)\), \(K=6/5\). Then
\[
\Delta(x)<\frac2{11}x,\quad E<\frac{79}{132}x<x,
\]
\[
d+E<\left(\frac{15}{26}+\frac{79}{132}\right)x
<Kx<8/25<1/2. \tag{4}
\]

### 3. T8 with a bottom join

For free \(V_2\), let \(D,A\) be bottom/right legs and \(H,J\) positive horizontal/negative vertical central chord lengths. If \(D+S_1\ge2\mu\), then \(D>\mu\), so \(V_2\) actually contains \(B_0\). Its long bottom anchor excludes the horizontal central line by twice triangle area \(\mu^2>1\). Hence only \(C,F,V_3\)'s \(U_3\) can join on the positive horizontal axis. Since \(r+y<E<x<1\), \(F\) must have a positive horizontal point. The actual inner endpoint of \(V_3\)'s segment then belongs to \(F\):
\[
q_R=(\beta,0),\qquad\beta=\mu-U_3>1-y>11/15.
\]
Four outer edges cannot all join: the four corner outer contributions total at most eight, below perimeter \(8\mu\). With left/top/bottom joined, right has a genuine lower-half gap, whose upper endpoint
\[
P_R=(\mu,-e)\in F,\qquad
0\le e=L_3-\mu<\epsilon_y<1/4.
\]
No unit square contains \(B_0,P_R,(\beta,0)\) with \(\beta>11/15\). To see this, use normals \((c,\varepsilon_Fs),(-\varepsilon_Fs,c)\), \(c\ge s\ge0\). The positive sign makes the \(B_0\)-to-\(P_R\) width at least \(c\mu+s(\mu-e)>c+s-se>1\), because
\[
c+s-1=s\left(1-\frac{s}{1+c}\right),
\qquad \frac{s}{1+c}\le\sqrt2-1<1/2,\quad e<1/4.
\]
The negative sign makes the width from \(B_0\) to \((\beta,0)\) equal to \(s\beta+c\mu>1\), since \(\beta>(1-c)/s\). Axial cases also fail because \(\mu>1\). Thus every bottom-join case is excluded.

### 4. T8 with a bottom gap

The gap belongs wholly to \(F\), since \(C\) misses bottom. Closedness gives its left endpoint
\[
Q_B=(-q,-\mu)\in F,\qquad
q=\mu-S_1>\frac{2w}{1+w}>w>x,
\quad q>\frac{6x}{2+3x}.
\]
If right also had a gap, \(P_R=(\mu,-e)\in F\) with \(0\le e<\epsilon_y<y<x<q\). Then
\[
|P_R-Q_B|^2=(\mu+q)^2+(\mu-e)^2
>(1+e)^2+(1-e)^2\ge2,
\]
impossible. Thus right joins: \(A+L_3\ge2\mu\), so \(A>1-\epsilon_y\).

Keep all actual free-corner lengths, including floating \(J\), with \(A+D+H+J\le2\). Let \(f_+\) be the positive horizontal chord length of \(F\), zero for negative or empty horizontal types. Positive-axis coverage \(r+U_3+H+f_+\ge\mu\) gives
\[
D+J<E+f_+. \tag{5}
\]
The full bottom chord of \(F\) obeys \(b\ge2\mu-S_1-D=\mu+q-D>1+q-D\).

If \(F\)'s positive horizontal intersection is nonempty, including tangency, its bottom/horizontal bound is \(b+f\le B<1\), hence \(D>q+f\). Equation (5) gives \(q+J<E\), contrary to \(q>x>E\).

If the horizontal intersection is negative or empty, \(D+J<E\). Let \(v\ge0\) be the upward reach of \(F\) from \(B_0\), within the negative vertical target half. The negative vertical axis has only \(C\), this floating \(J\), and \(F\), so
\[
d+J+v\ge\mu>1,\qquad v>1-d-J.
\]
This is a length-sum necessity, not a shared-origin maximum. The bottom anchor and full bottom chord in this same \(F\) give \(b+v^2\le2\). But \(D+J<E,d+E<1/2\), and the exact identity
\[
(1-d-J)^2-D-(1-d-E)^2
=(E-J)(2-2d-E-J)-D>0
\]
yield
\[
b+v^2>1+q+(1-d-E)^2
>1+\frac{6x}{2+3x}+(1-Kx)^2>2.
\]
The last strict inequality follows from
\[
\frac{6x}{2+3x}-2Kx+K^2x^2
=\frac{6x(5-18x+18x^2)}{25(2+3x)}>0.
\]
The polynomial decreases on \([0,4/15]\) and has endpoint value \(37/25>0\). Thus both bottom patterns and all horizontal types are excluded: G4 T8 is impossible for all \(a>2\).

### 5. G3: no representative with all four corner-hosted midpoints

Now \(C\) contains left/center, \(F\) right but not center. If all midpoints have corner hosts, the matching is cyclic; reflect upper/lower to select
\[
m_B\in V_1,\quad m_R\in V_2,\quad m_U\in V_3,\quad m_L\in V_4.
\]
The tile \(F\) cannot meet top-left, while \(V_3\)'s long leg covers top-right and \(C\) misses top. Thus \(L_3+S_4\ge2\mu\). Since \(F\) misses left, \(\ell\ge2\mu-L_4-S_1\), valid even as a negative lower bound. Let \(v_C,v_F\) be the vertical-central chord lengths; only \(U_1,U_3\) contribute there from corners.

If \(F\)'s vertical intersection is empty, \(v_C\ge2\mu-U_1-U_3\), and \(\ell+v_C\le B\), while the corner budgets and top join give
\[
\ell+v_C\ge4\mu-L_4-S_1-U_1-U_3
>7\mu-6+S_3+U_4>1,
\]
a contradiction.

If it is nonempty, R20.2 forces a unique top/bottom gap in \(F\), with matching vertical sign. Top is joined, so bottom has the gap, \(v_F\) is negative, and \(u\ge\mu-U_3\). Its bottom chord \(b\ge2\mu-L_1-S_2\) and horizontal chord \(f\) satisfy \(b+f\le B\), while \(r+f+U_2\ge\mu\) and \(\mu+\ell+r+u<2\).

If right joined, these facts imply
\[
r>5\mu-B-2-L_1-S_3,\qquad
r<6-6\mu+S_1-S_3-U_4,
\]
so \(11\mu-B-8<L_1+S_1-U_4<2\), impossible. Therefore right has a gap, wholly in \(F\). Its upper endpoint \((\mu,\mu-S_3)\) and right midpoint give a right-edge chord \(R_F\ge\mu-S_3\). Both parallel pairs really exist:
\[
R_F+v_F\le B,\qquad\ell+v_C\le B.
\]
Then
\[
\begin{aligned}
v_C+v_F+U_1+U_3
&\le2B-\ell-R_F+U_1+U_3\\
&\le2B-3\mu+L_4+(S_1+U_1)+(S_3+U_3)\\
&<4+2B-3\mu+L_4-L_1-L_3\\
&<6+2B-5\mu-L_1-U_4\\
&\le6+2B-6\mu-U_4<2\mu,
\end{aligned}
\]
contrary to full vertical-central coverage. This G3 subclass is excluded without R13's polynomial certificate.

For G4, the corresponding positive cyclic matching belongs to R20A's excluded \((3,2)\) case with \(V_4\) duplicating left; the reverse cycle belongs to T8. Thus in either G3 or G4, at least one midpoint of \(C,F\) has no corner host.

### 6. The free upper corners of both remaining G4 representatives have no midpoint

Keep \(C\) left/center, \(F\) bottom, and denote (top host, right host).

For \((4,2)\), R20 excludes positive horizontal \(F\); the remaining negative/empty types have left joining. If free \(V_3\) contained right midpoint, reselect it as host to obtain excluded T8. Suppose it instead contained top. The top-host central segments of \(V_3,V_4\) truly share the top-midpoint origin, so their union is measured by \(\max(U_3,U_4)\).

Let half-angles of \(V_1,V_4,V_3,V_2\) be \(w,x,y,t_2\). Right must join because any remaining right gap is upper and neither \(C\) nor \(F\) can fill it. Hence
\[
x<\rho_1<4/15,\quad y<\rho_2<4/15,\quad y<1-t_2.
\]
Set \(m=\max(x,y)\). The upper reach of \(C\) exceeds \(1-m\), and the same actual projections give \(r<\Delta(m),d<m/(2-m)\). The positive horizontal axis has only \(C,V_2\), so \(r+U_2\ge\mu\), \(U_2<t_2\), and \(r>1-t_2>y\). If \(m=y\), this contradicts \(r<\Delta(y)<y\).

If \(m=x\), the bound \(S_2+U_2\le B<1\) gives \(S_2<r<\Delta(x)<2x/11\). Left joining still gives \(w>3x/2\), so \(q=\mu-S_1>3x/2\). The positive bottom gap belongs to \(F\):
\[
b\ge2\mu-S_1-S_2>1+q-S_2.
\]
Only \(C,F\) cover the negative vertical axis, so \(v>1-d\), while \(d<15x/26\). The same-unit-square parabola \(b+v^2\le2\) fails because
\[
b+v^2>2+q-S_2-2d+d^2>2,
\]
using \(S_2+2d<(2/11+15/13)x<3x/2<q\). Thus \(V_3\) has neither possible midpoint. The negative-horizontal branch still carries the historical \(J>0\) necessity; it is not yet closed here.

For \((3,2)\), R20A excludes a duplicated left midpoint in free \(V_4\). If it contained top, select it as top host to obtain \((4,2)\) with \(V_3\) still duplicating top: positive horizontal is excluded by R20, and the other types by the preceding argument. Therefore this free upper-left corner also has no midpoint.

### 7. Correction of an overbroad historical right-gap allowance

R20's empty-horizontal \((4,2)\) remainder allowed a right gap in \(F\). That was too broad: \(V_2\) is already the lower-right/right-midpoint host, so every right gap lies in the upper half. Its distance from \(B_0\in F\) exceeds \(\sqrt2\), and from \(L\in C\) is at least \(2\mu\). Thus right must join.

No old exclusion used that extra candidate, so no earlier theorem is withdrawn; this corrects the continuation classification. In both remaining G4 representatives \((3,2),(4,2)\), right and top join. In \((4,2)\), left also joins for both negative and empty horizontal types. The negative type additionally has \(J>0\) from the historical R13 certificate; a hash check of that artifact is not a rerun of its proof.

### 8. A G2 near right-gap consequence

For this separate statement, \(V_2,V_3,V_4\) host right/top/left, \(F\) contains bottom midpoint, and \(C\) contains center but no midpoint. If \(C\) fills a right-upper gap, its upper endpoint
\[
P_R=(\mu,e),\qquad e=\mu-S_3>\frac{2y}{1+y},\quad y=t_3\in(0,1),
\]
belongs to \(C\); the upper central endpoint also lies there, giving \(u>1-y\). No double-join bound \(y<4/15\) is imported. For \(y\le1/2\), \(u>1/2\); for \(y\ge1/2\), \(e>2/3\). Thus \(C\) has an actual point of height greater than \(1/2\), farther than \(\mu+1/2>3/2>\sqrt2\) from every bottom point. Hence \(C\) misses bottom entirely.

A near top-gap tile \(C\) already misses bottom by distance \(2\mu\). Thus in both remaining near representatives, any actual bottom gap, endpoints included, belongs entirely to \(F\). Moreover a right-gap case with positive horizontal \(F\) has left joining, because neither \(F\) nor the right-contacting \(C\) can touch left. This is a further necessary condition, not a completed G2 exclusion.

<a id="R21A"></a>
## R21A. A strict lower bound for the floating vertical chord in diagonal G4

**Scope.** Source: S6_attack_round21_addendum.md, sections 1--4. This treats the remaining \((4,2)\) G4 representative with negative or empty horizontal intersection of \(F\). It proves \(J>x/3\), not an exclusion of the entire region above that bound. Only the anchored corners are locally replaced; the free corner and \(C,F\) remain the actual original tiles.

### 1. Actual geometry and two coupled budgets

The target is \([-\mu,\mu]^2\), \(\mu>1\). Assume \(C\) contains center/left midpoint, \(F\) bottom midpoint but not center. Left/top/right join; \(V_1,V_2,V_4\) host left/right/top, and \(V_3\) is free with no midpoint, as established by R21. Standardize only these three hosts by target-dominating replacements, retaining their joins and reclassifying output predicates. Let \(x=t_4,w=t_1\), and use \(L_2,S_2,U_2\) for the right host. R21's hand argument from left joining gives
\[
0<x<4/15,\quad w>3x/2,\quad
q=\mu-S_1>\frac{2w}{1+w}>\frac{6x}{2+3x}>\frac{15}{7}x. \tag{1}
\]
For original \(V_3\), let \(A,D\) be top/right legs and \(H,J\) positive horizontal/vertical target chord lengths. These may be empty, tangent, or floating. The full grid budget is \(A+D+H+J\le2\). Top/right joins give \(A+L_4,D+L_2\ge2\mu\). Since \(F\) has no positive horizontal point, coverage requires \(r+H+U_2\ge\mu\), with actual \(C\) reach \(r\). Using \(L_2+S_2+U_2<2\),
\[
S_2+J<r+L_4+4-5\mu.
\]
With the actual cosine cap
\[
\delta(x)=\frac{2x^2}{1-x^2},\qquad L_4\le1+\delta(x),
\]
we obtain the strict inequality
\[
S_2+J<\delta(x)+r. \tag{2}
\]
Its strictness comes from \(\mu>1\) and the strict corner budget, not a false strict cosine cap.

The bottom short legs total less than \(2<2\mu\), so bottom has a genuine gap in \(F\), since the center/left anchor excludes \(C\) from bottom. The full bottom chord \(b\) satisfies
\[
b\ge2\mu-S_1-S_2=\mu+q-S_2>1+q-S_2. \tag{3}
\]
All corners miss the negative vertical axis. Let \(d\) be the lower reach of \(C\), and \(v\) the upward reach from \(B_0\) of \(F\) on that target half. Then \(d+v\ge\mu>1\). The bottom anchor and full chord in this same actual \(F\) give
\[
b+v^2\le2. \tag{4}
\]
No nonempty horizontal-intersection hypothesis on \(F\) is used, so both negative and empty types are covered.

### 2. Actual projections of C under the small-J assumption

Suppose \(0\le J\le x/3\), and put \(z=x+J\). Then
\[
0<z\le4x/3<16/45.
\]
Upper vertical coverage \(u+J+U_4\ge\mu\), with \(U_4<x\), gives \(u>1-z>29/45\).

Choose normals of \(C\) as \((c,\varepsilon s),(-\varepsilon s,c)\), \(c\ge s\ge0,c^2+s^2=1\). Axial directions cannot contain the length-\(\mu\) center/left chord. A positive rotation would force \(c\mu+su\le1\), so \(u<(1-c)/s\le\sqrt2-1<29/45\). Thus the rotation is negative. The actual left/upper endpoint projections, with central half-angle \(\eta=s/(1+c)\), give
\[
\eta<\frac{z}{2-z},\qquad
r<\Delta(z)=\frac{z^2}{2(1-z)},\qquad
0\le d<\eta<\Gamma(z)=\frac{z}{2-z}<8/37<1. \tag{5}
\]
Consequently (2) becomes \(S_2+J<\delta(x)+\Delta(z)\). These projection conclusions are restricted to the small-\(J\) contradiction branch.

### 3. Retain the square term and the floating-chord cancellation

The function \(2d-d^2\) increases on \(0\le d<1\). Thus (2),(5) imply
\[
\begin{aligned}
S_2+2d-d^2
&<\delta(x)+\Delta(z)-J+2\Gamma(z)-\Gamma(z)^2\\
&=\delta(x)+\Delta(z)+x+\frac{z^2(1-z)}{(2-z)^2}. \tag{6}
\end{aligned}
\]
Here the exact identities are
\[
2\Gamma-\Gamma^2-z=\frac{z^2(1-z)}{(2-z)^2},
\qquad z-J=x.
\]
This cancellation keeps the common occurrence of \(J\) in corner and central budgets. It neither turns a sum of floating lengths into an actual union nor uses a fictitious shared-origin maximum.

For \(0<x<4/15,z\le4x/3\), monotone rational bounds give
\[
\delta(x)<\frac{120}{209}x,\qquad
\Delta(z)<\frac{32}{87}x,\qquad
\frac{z^2(1-z)}{(2-z)^2}
<\frac{z^2}{(2-z)^2}<\frac{240}{1369}x.
\]
For the last, bound successively by \((16/9)x^2/(2-4x/3)^2\); after division by \(x\) it increases strictly and has endpoint value \(240/1369\). Exactly,
\[
\frac{120}{209}+\frac{32}{87}+1+\frac{240}{1369}
=\frac{52704679}{24892527}<\frac{15}{7},
\]
with margin \(4455152/174247689>0\). Sections (1),(6) therefore give \(S_2+2d-d^2<q\). Since \(v>1-d>0\), (3) yields
\[
b+v^2>1+q-S_2+(1-d)^2
=2+q-S_2-2d+d^2>2,
\]
contrary to (4). Thus \(J>x/3\).

### 4. Premise audit and extent of the checks

The three joins and actual left-midpoint ownership of \(V_1\) are established before the three-host replacements. The free \(V_3\), its chord positions, and \(C,F\) are not moved. The quantity \(J\) is the positive vertical target chord; its corner is too far from any negative-axis point to contribute there. The sign restriction on \(F\) is exactly the surviving negative/empty horizontal types, after R20's positive-type exclusion.

The inequality \(u+J+U_4\ge\mu\) allows floating intervals and overlap. The bottom chord/square bound is rooted at the actual \(B_0\) in the same \(F\); gap endpoints lie in \(F\) by closedness. Negative rotation, \(d<1\), and the positive lower bound \(v>1-d\) were proved only inside the small-\(J\) assumption, ensuring that squaring has the stated direction.

The source records eleven scalar counterexample queries (nine NRA, two LRA), all UNSAT, plus two symbolic identities and four exact constant comparisons. They check the hand-derived scalar chain; there is no layout optimization or fixed-angle/interval sampling. The new core does not need R13's adjacent-corner certificate. Historical package preservation or hashing is distinguished from rerunning an old entry point. This module closes only \(J\le x/3\) in its assigned host subclass; \(J>x/3\) remains for R22.

<a id="R22"></a>
## R22. Actual bridge endpoints exclude the diagonal G4 representative

**Scope.** Source: S6_attack_round22.md, sections 1--5. This closes G4 with top host \(V_4\), right host \(V_2\), including negative and empty horizontal types of \(F\). The positive type was excluded in R20. The bridge argument uses the original free corner and its actual endpoint membership.

### 1. Actual three-join framework and established inputs

Let \(S=[-\mu,\mu]^2\), \(\mu=a/2>1\). Assume \(O,L=(-\mu,0)\in C\), \(B_0=(0,-\mu)\in F\), \(O\notin F\), with \(V_2\) right and \(V_4\) top hosts. R20--R21 prove that when \(F\) has no positive horizontal point, left/top/right all join. Left joining gives actual left-midpoint ownership by \(V_1\). Standardize only \(V_1,V_2,V_4\) by target-dominating local replacements, preserve their joins, and reclassify outputs. Keep original \(W=V_3\) fixed.

Use \(L_i,S_i,U_i\) for host lengths, with half-angles \(w,x,y\) for \(V_1,V_4,V_2\). Actual central reaches of \(C\) are \(r,u,d\); its full left chord is \(\ell\). Actual target values of \(W\) are top/right legs \(A,D\), positive horizontal/vertical chords \(H,J\). The inputs from R3, R17, R21, R21A are
\[
0<x<4/15,\quad w>3x/2,\quad U_4<x,\quad U_2<y,\quad0<y<1,
\]
\[
q=\mu-S_1>\frac{6x}{2+3x}>\frac{15}{7}x,\qquad J>x/3>0, \tag{1}
\]
\[
S_2+J<\delta(x)+r,\qquad\delta(x)=\frac{2x^2}{1-x^2}, \tag{2}
\]
\[
\mu+\ell+r+u<2. \tag{3}
\]
Equation (2) uses the actual budget \(A+D+H+J\le2\), top/right joins and positive-axis coverage; it does not standardize \(W\) or assume chord origins.

Since \(C\) misses bottom and bottom short legs sum to less than \(2<2\mu\), the genuine bottom gap belongs entirely to \(F\). Its full bottom chord \(b\) and upward reach \(v\) from \(B_0\) within the negative vertical half satisfy
\[
b>1+q-S_2,\qquad v>1-d,\qquad b+v^2\le2. \tag{4}
\]
All corners miss that negative half-axis. These facts apply to negative and empty horizontal \(F\), without applying a nonempty parallel bound to an empty chord.

Define the forced positive-axis endpoints
\[
Q_R=(\mu-U_2,0),\qquad Q_U=(0,\mu-U_4).
\]
Only \(C,V_2,W\) cover the positive horizontal axis, and only \(C,V_4,W\) the positive vertical axis. Taking limits beyond the corner-tail intervals gives \(Q_R,Q_U\in C\cup W\), even though each endpoint also belongs to its anchored corner.

### 2. The bridge lemma: C owns at least one positive-axis endpoint

Suppose neither endpoint belongs to \(C\). Then \(r<\mu-U_2,u<\mu-U_4\). Open gaps beyond the actual endpoints of \(C\) on both axes can only be bridged by this same original \(W\). Closedness yields
\[
(r,0),(0,u)\in W.
\]
In upper-right inward coordinates \(X=\mu-x_{\rm global},Y=\mu-y_{\rm global}\), choose a positive-quadrant normal \((c,s)\), \(c,s\ge0,c^2+s^2=1\), of \(W\). It contains its corner \((0,0)\); the parallel support lines are one apart, so throughout \(W\),
\[
cX+sY\le1.
\]
The intercept one is an upper bound, not an assumption that the corner lies on that supporting line. If \(c\) or \(s\) were zero, \(W\) could not reach one of the two central axes at distance \(\mu>1\); hence both are positive.

The bridge points imply
\[
r\ge\mu-X_{\max},\quad u\ge\mu-Y_{\max},\qquad
X_{\max}=\frac{1-s\mu}{c},\quad Y_{\max}=\frac{1-c\mu}{s}.
\]
Their sum is
\[
X_{\max}+Y_{\max}=K=\frac{c+s-\mu}{cs}<1,
\]
using \(\mu>1\) and \(c+s-1<cs\), equivalent to \((1-c)(1-s)>0\). Thus \(r+u\ge2\mu-K>2\mu-1>1\), contrary to (3), which gives \(r+u<2-\mu-\ell<1\). Therefore
\[
Q_U\in C\quad\hbox{or}\quad Q_R\in C. \tag{5}
\]
No midpoint-free assumption on \(W\) is needed for this bridge inequality, and replacing \(H,J\) by their sum would not supply its endpoint geometry.

### 3. C owns the upper endpoint: bottom-chord contradiction

If \(Q_U\in C\), then \(u\ge\mu-U_4>1-x\). Let its normals be \((p,\varepsilon s_C),(-\varepsilon s_C,p)\), \(p\ge s_C\ge0\). Axial directions cannot contain the long left chord. Positive rotation forces \(p\mu+s_Cu\le1\), giving \(u<(1-p)/s_C\le\sqrt2-1\), contrary to \(u>11/15\). Thus only negative rotation is possible, and the actual endpoint projections give
\[
r<\Delta(x)=\frac{x^2}{2(1-x)},\qquad
0\le d<\frac{x}{2-x}<1.
\]
Equation (2) with \(J\ge0\) gives \(S_2<\delta(x)+\Delta(x)\). For \(x<4/15\),
\[
\delta(x)<\frac{120}{209}x,\quad
\Delta(x)<\frac2{11}x,\quad2d<\frac{15}{13}x.
\]
The exact margin
\[
\frac{15}{7}-\left(\frac{120}{209}+\frac2{11}+\frac{15}{13}\right)
=\frac{4432}{19019}>0
\]
and (1) imply \(S_2+2d<q\). Since \(v>1-d>0\), (4) yields
\[
b+v^2>1+q-S_2+(1-d)^2
=2+q-S_2-2d+d^2>2,
\]
impossible. Thus (5) forces \(Q_R\in C\).

### 4. C owns the right endpoint: complementary-angle feedback

Put \(\nu=1-y\in(0,1)\), the source's local \(k\), not midpoint count. Then
\[
r\ge\mu-U_2>1-y=\nu.
\]
The actual left and right points in \(C\) have horizontal separation \(\mu+r\le\sqrt2\), so
\[
0<\nu<r\le\sqrt2-\mu<\sqrt2-1<3/7. \tag{6}
\]
Since \(J>0\), the original \(W\) really meets right and vertical-central lines, giving \(D+J\le B\). Right joining \(D+L_2\ge2\mu\) then gives \(J\le B-2\mu+L_2<L_2-1\). The sine cap of \(V_2\) yields
\[
J<\Delta(\nu)=\frac{\nu^2}{2(1-\nu)}. \tag{7}
\]
This is a bound in the complementary parameter \(1-y\); no older small-angle restriction is imposed on \(y\).

Set \(z=x+J\). By monotonicity of \(\Delta\),
\[
0<z<4/15+\Delta(3/7)=4/15+9/56
=359/840<3/7. \tag{8}
\]
Upper-axis coverage gives \(u>1-z>4/7>\sqrt2-1\), again excluding positive rotation of \(C\). The actual left/upper projections, with \(\eta=s_C/(1+p)\), now give
\[
\eta<\frac{z}{2-z},\qquad r<\Delta(z). \tag{9}
\]
These are newly justified under (8), not borrowed from R21A's small-\(J\) assumption.

For \(0<t<3/7\), direct multiplication shows \(\Delta(t)<3t/8\). Applying it to \(\nu,z\),
\[
J<\Delta(\nu)<3\nu/8<3r/8
<3\Delta(z)/8<9z/64. \tag{10}
\]
But \(J>x/3\) and \(z=x+J\) imply \(J>z/4\), contradicting \(9/64<1/4\). Both alternatives in (5) fail. Thus negative and empty horizontal types are excluded; with R20's positive type, the whole diagonal G4 representative is impossible for every \(a>2\).

### 5. Two conditional G3 directions retained for continuation

For this separate continuation, \(C\) contains center/left, \(F\) right but not center.

1. If \(V_1\) duplicates left and top host is \(V_3\), bottom host must be \(V_2\). Any top/bottom gaps would be on left halves; neither \(C\) nor right-anchored \(F\) can fill them. Both edges join. The unique top/bottom-gap theorem then forces the vertical-central intersection of \(F\) to be empty.
2. If \(V_2\) duplicates right and top host is \(V_4\), bottom host must be \(V_1\). Suppose \(F\)'s vertical-central intersection were empty. Then
\[
\ell\ge2\mu-S_1-S_4,\qquad
v_C\ge2\mu-U_1-U_4-J,
\]
while the nonempty parallel pairs give \(\ell+v_C\le B\) and \(S_i+U_i\le B\). Hence \(J\ge4\mu-3B>1\), contradicting the strict single-central-chord bound for any free corner.

These are conditional directions for the specified host choices, not an exclusion of all G3 or all repeated-midpoint patterns. The alternative top-host choice must still be handled. The source first froze these notes and their original checks in this round's package.

<a id="R22A"></a>
## R22A. Two genuine gaps are forced in the same-side G4 representative

**Scope.** Source: S6_attack_round22_addendum.md, sections 1--5. This excludes every negative or empty horizontal type of \(F\), and excludes a left or bottom join when \(F\) has a positive horizontal point. It concerns the G4 selection top \(V_3\), right \(V_2\), and keeps the original free upper-left corner fixed throughout its bridge arguments.

### 1. Unified notation and the actual upper-left bridge

Let \(S=[-\mu,\mu]^2\), \(\mu>1\). Assume \(L=(-\mu,0),O\in C\), \(B_0=(0,-\mu)\in F\), \(O\notin F\); \(V_2,V_3\) host right/top. Right and top join, and \(W=V_4\) has no midpoint, by R21. Locally standardize only \(V_2,V_3\), with half-angles \(a,y\in(0,1)\), using target-dominating replacement and output reclassification. Right joining gives
\[
y<\rho_2=\frac{L_2-1}{3-L_2}<\min(a,1-a),\qquad y<4/15. \tag{1}
\]
The source's local kappa is denoted \(\rho_2\) to reserve \(\kappa\) for global midpoint count.

Let \(A_1,D_1\) be the actual bottom/left legs of free \(V_1\), and \(A,D\) the actual top/left legs of original \(W\). Since \(W\) misses left midpoint, \(D<\mu\). The full left chord \(\ell\) and central right/upper/lower reaches \(r,u,d\) of \(C\) satisfy
\[
\mu+\ell+r+u<2.
\]
Only \(C,V_2\), and a positive horizontal chord of \(F\) can cover the positive horizontal axis. Only \(C,V_3,W\) cover the positive vertical axis. Define
\[
Q_R=(\mu-U_2,0),\qquad Q_U=(0,\mu-U_3),\qquad U_2<a,\quad U_3<y.
\]
If \(Q_U\notin C\), the same original \(W\) contains \(Q_U\) and \((0,u)\), the actual upper endpoint of \(C\), by closedness across the intervening gap.

In upper-left inward coordinates \(X=x_{\rm global}+\mu,Y=\mu-y_{\rm global}\), choose a positive-quadrant normal \((c,s)\) of \(W\), \(c,s>0,c^2+s^2=1\). An axial tile cannot span the horizontal distance \(\mu>1\) from its corner to \(Q_U\). The corner lies in \(W\), so unit width gives
\[
cX+sY\le1,\qquad T=\frac{s}{1+c}\in(0,1),
\qquad g(T)=\frac{1-T}{1+T}=\frac{1-s}{c}.
\]
The bridge point \((0,u)\) gives
\[
u>1-T. \tag{2}
\]
The points \(Q_U=(\mu,U_3)\) and the actual left-leg endpoint \((0,D)\) are in the same \(W\). The other projection width gives
\[
s\mu+c(D-U_3)\le1,\qquad D<g(T)+y. \tag{3}
\]
Therefore
\[
D+T<1+y-\frac{T(1-T)}{1+T}<1+y. \tag{4}
\]
No free-corner standardization or fictitious origin for a floating chord is used.

### 2. Nonpositive horizontal F: C owns the right endpoint but not the upper one

If \(F\) has no positive horizontal point, closedness forces \(Q_R\in C\). Put \(\nu=1-a\), giving
\[
0<\nu<r\le\sqrt2-\mu<3/7.
\]
The sine cap is \(L_2\le(1+a^2)/(2a)=1+\Delta(\nu)\), where \(\Delta(t)=t^2/[2(1-t)]\). Since \(L_2<2\), (1) gives
\[
y<\rho_2<L_2-1\le\Delta(\nu)<9/56. \tag{5}
\]
If \(Q_U\in C\), then \(u>1-y>4/7\). The actual long left chord and upper endpoint exclude positive rotation of \(C\); negative rotation gives \(r<\Delta(y)\). Since \(\Delta(t)<3t/8\) for \(0<t<3/7\),
\[
r<\Delta(y)<3y/8<3\Delta(\nu)/8<9\nu/64<\nu,
\]
contradicting \(r>\nu\). Thus \(Q_U\notin C\), and the actual bridge bounds (2),(3) apply.

Suppose left has a gap. Its upper endpoint \(P=(-\mu,\mu-D)\) lies in the upper half and cannot belong to bottom-anchored \(F\), so it belongs to \(C\). Consequently \(\ell\ge\mu-D\). With the long-chord budget and (2),
\[
r<D+T+2-3\mu<D+T-1<y,
\]
contrary to \(y<\nu<r\). Therefore negative/empty horizontal \(F\) requires left joining.

### 3. Nonpositive horizontal F with a left join: feedback and the bottom parabola

Left joining \(D_1+D\ge2\mu\), \(D<\mu\), gives actual left-midpoint ownership by \(V_1\). Only now standardize it as a left host, with left long leg \(L_1\), bottom short leg \(S_1\), and half-angle \(w\), retaining the join and reclassifying other predicates. Keep \(W\) fixed.

The cap \(L_1\le\sqrt2<10/7\) yields \(D>2\mu-L_1>4/7\). Equations (3),(5) imply
\[
g(T)>4/7-9/56=23/56,\qquad T<33/79<3/7.
\]
Thus \(u>4/7\), so \(C\) rotates negatively, with actual projections
\[
r<\Delta(T),\qquad0\le d<T/(2-T).
\]
Hence \(\nu<\Delta(T)\), \(y<\Delta(\nu)\), initially giving
\[
y<\Delta(\Delta(3/7))=\Delta(9/56)=81/5264.
\]
Combining \(D>4/7,D<g(T)+y\),
\[
\frac{2T}{1+T}=1-g(T)<3/7+y
<3/7+81/5264<4/9,
\]
so \(T<2/7\). Feeding this back gives
\[
\nu<\Delta(T)<T/5,\quad\nu<2/35,\qquad
y<\Delta(\nu)<\nu/33<T/165. \tag{6}
\]
Left joining and (3) now imply
\[
L_1>1+\frac{2T}{1+T}-y
>1+\left(\frac{14}{9}-\frac1{165}\right)T
=1+\frac{767}{495}T.
\]
The cosine cap \(w^2\ge(L_1-1)/(L_1+1)\) and \(L_1+1<17/7\) give
\[
w^2>\frac{5369}{8415}T>\frac{14}{25}T>
\frac{49}{25}T^2,\qquad w>7T/5.
\]
Set \(q=\mu-S_1\). The short-leg bound \(S_1<g(w)\) yields
\[
q>\frac{2w}{1+w}>\frac{14T}{5+7T}>2T. \tag{7}
\]
Because \(Q_R\in C\), \(r+U_2\ge\mu\). The actual parallel pair of \(V_2\) gives \(S_2+U_2\le B<1\), so \(S_2<r<\Delta(T)<T/5\). Also \(d<T/(2-T)<7T/12\), whence
\[
S_2+2d<41T/30<2T<q.
\]
The left/right anchored \(V_1,V_2\) miss the vertical central line, while \(V_3,W\) meet it only positively. The negative half has only \(C,F\). The actual bottom chord \(b\) and upward reach \(v\) of \(F\) therefore satisfy
\[
b>1+q-S_2,\qquad v>1-d>0,\qquad b+v^2\le2.
\]
The first two imply \(b+v^2>2+q-S_2-2d+d^2>2\), a contradiction. Every negative or empty horizontal type is excluded, with either left gap or left join, without R13's three-join polynomial certificate.

### 4. Positive horizontal F cannot have a left join

Suppose \(F\) has a positive horizontal point and left joins. As above \(V_1\) is an actual left host; after local standardization \(S_1<1,q=\mu-S_1>0\). Bottom has a positive gap in \(F\), giving \(b>1+q-S_2\). Let \(f\) be its full positive horizontal chord length, possibly zero at tangency. Both line intersections are nonempty, so \(b+f\le B<1\). Positive-axis coverage gives \(f>1-a-r\). Write
\[
S_2<g(a)=1-a-\chi(a),\qquad
\chi(a)=\frac{a(1-a)}{1+a}.
\]
The local function \(\chi\) is the source's \(\eta(a)\); it is not the central half-angle. Thus
\[
b+f>1+q+\chi(a)-r. \tag{8}
\]
From (1), \(\chi(a)>y/3\): use \(\chi(a)\ge a/3\) for \(a\le1/2\), or \(\chi(a)\ge(1-a)/3\) for \(a\ge1/2\).

If \(Q_U\in C\), \(u>1-y\), so the negative-rotation projection gives \(r<\Delta(y)<2y/11<y/3<\chi(a)\), contradicting (8) and \(b+f<1\).

If \(Q_U\notin C\), use the actual bridge (2),(3). Left joining still gives \(D>4/7\), while \(y<4/15\); hence \(g(T)>32/105\), so
\[
T<73/137,\qquad u>1-T>64/137>\sqrt2-1.
\]
Thus \(C\) rotates negatively and \(r<\Delta(T)\). If \(T\le y\), then \(r<\Delta(y)<y/3<\chi(a)\), again impossible.

If \(T>y\), left joining and (3) imply
\[
L_1>1+\frac{2T}{1+T}-y
>1+\frac{T(1-T)}{1+T}.
\]
Its cosine cap gives
\[
w^2>\frac{T(1-T)}{2+3T-T^2}>T^2/4,\qquad w>T/2.
\]
The second inequality is equivalent to \(4-6T-3T^2+T^3>0\); this polynomial decreases on \([0,73/137]\) and is strictly positive at its right endpoint. Consequently
\[
q>\frac{2w}{1+w}>\frac{2T}{2+T}>\Delta(T)>r.
\]
The penultimate comparison is \(4-6T-T^2>0\), likewise positive through the right endpoint. Equation (8) again gives \(b+f>1\). Every positive-horizontal left-join case is excluded by this independent hand argument.

### 5. Positive horizontal F cannot have a bottom join

A bottom join makes \(V_1\) an actual bottom-midpoint host, since \(S_2<\mu\). Locally standardize it as a bottom host, using half-angle \(w_B\), long bottom leg \(L_B\), short left leg \(S_L<g(w_B)<1\). These are different roles from the left-host parameters of the preceding section.

Since original \(W\) has \(D<\mu\), left has a positive gap. The tile \(F\), containing \(B_0\) and a positive horizontal point \((p,0)\), cannot meet any left point \((-\mu,z)\), \(z\ge-\mu\): twice triangle area is \(\mu^2+p(z+\mu)>1\). Thus the entire left gap belongs to \(C\), giving
\[
\ell\ge2\mu-S_L-D. \tag{9}
\]
Right and bottom joins yield respectively
\[
y<\rho_2<a,\qquad a<\rho_B<w_B. \tag{10}
\]
If \(Q_U\in C\), use \(u>\mu-y,D<\mu\), the long-chord budget, and (9) to obtain \(S_L>1+r-y\). If not, the actual bridge gives \(Y_{\max}=(1-c\mu)/s<T\) and \(D+Y_{\max}<D+T<1+y\); with \(u\ge\mu-Y_{\max}\), the same budget again gives \(S_L>1+r-y\).

Thus always \(S_L>1-y\), whereas \(S_L<g(w_B)\). Hence
\[
\frac{2w_B}{1+w_B}<y,\qquad
w_B<\frac{y}{2-y}<y,
\]
contrary to \(y<a<w_B\) in (10). Every positive-horizontal bottom-join case is excluded. The surviving same-side representative must therefore have positive horizontal \(F\) and genuine gaps on both left and bottom; R23 treats that remainder.

<a id="R23"></a>
## R23. Completion of the G4 exclusion

**Scope.** Source: S6_attack_round23.md, sections 1--7. This closes the final same-side-host G4 representative with positive horizontal \(F\) and genuine left/bottom gaps. It retains every possible bottom-midpoint ownership by \(V_1\), including tangency and duplication. All endpoint and projection statements concern the same actual \(C,F,W\).

### 1. The three G4 host representatives and the remaining case

Let \(S=[-\mu,\mu]^2\), \(\mu=a/2>1\), with corners in the usual order. Assume \(O,L=(-\mu,0)\in C\), \(B_0=(0,-\mu)\in F\), \(O\notin F\); reflection puts any adjacent central midpoint pair in this arrangement. A unit tile cannot contain two outer midpoints. The other top/right midpoints require corner hosts, with three selective representatives:

1. Top \(V_4\), right \(V_3\): T8, excluded by R21.
2. Top \(V_4\), right \(V_2\): diagonal, excluded by R22.
3. Top \(V_3\), right \(V_2\): same side, with negative/empty horizontal \(F\) and positive-horizontal left or bottom joins excluded by R22A.

These exclusions allow repeated midpoint hosts. The only remainder has positive horizontal \(F\), genuine left and bottom corner gaps, and right/top joins. The free \(W=V_4\) has no midpoint: a top midpoint could be reselected into the excluded diagonal case; a left midpoint is excluded by R20A. The source froze R22A in this round and recorded a correction to an earlier working suggestion; no incorrectly matched historical near three-join suggestion is used in the final theorem.

### 2. Actual endpoints and two budgets in the last remainder

Standardize the right/top hosts \(V_2,V_3\) by stepwise target-dominating replacement. If a left or bottom gap is filled, reclassify into the cases already excluded by R22A; retain here only outputs with both gaps genuine. Keep original \(V_1,W,C,F\) fixed. Their half-angles \(a,y\in(0,1)\) satisfy
\[
y<\rho_2=\frac{L_2-1}{3-L_2}<\min(a,1-a),\quad
y<4/15,\qquad L_2\le\sqrt2<2. \tag{1}
\]
Define
\[
\chi(a)=\frac{a(1-a)}{1+a},\qquad
\Delta(t)=\frac{t^2}{2(1-t)},\qquad
g(t)=\frac{1-t}{1+t}.
\]
Here \(\rho_2\) is the source's local kappa, and \(\chi\) is its local \(\eta(a)\), not the central half-angle. The bottom short leg of \(V_2\) satisfies \(S_2<g(a)=1-a-\chi(a)\).

Let \(r,u\ge0\) be actual central reaches of \(C\), \(\ell\) its full left-edge chord, and \(\ell_+\) its upward reach from the left midpoint, so \(\ell\ge\ell_+\). The source calls this last length \(\lambda\); here it is renamed to avoid conflict with the global slope function \(\lambda(t)\). The long-chord budget is
\[
\mu+\ell+r+u<2.
\]
Let \(A_1,D_1\) be actual bottom/left legs of \(V_1\), and \(D<\mu\) the actual left leg of \(W\). Since \(F\) contains \(B_0\) and a positive horizontal point \((p,0)\), any left point \((-\mu,z)\), \(z\ge-\mu\), would form a triangle of twice area \(\mu^2+p(z+\mu)>1\). Thus \(F\) misses left. The entire left gap, endpoints included, belongs to \(C\), and the bottom gap to \(F\), since \(C\)'s center/left chord excludes bottom:
\[
\ell\ge2\mu-D_1-D,\qquad b\ge2\mu-A_1-S_2.
\]
The actual upper left-gap endpoint \(P=(-\mu,\mu-D)\in C\) gives
\[
\ell_+\ge\mu-D>0. \tag{2}
\]
The full bottom/horizontal chords \(b,f\) of this same \(F\) are nonempty, even if the latter is a singleton, so \(b+f\le B(\mu)<1\). Positive-axis coverage gives \(f\ge\mu-r-U_2>1-a-r\).

The upper central endpoint \(Q_U=(0,\mu-U_3)\), \(U_3<y\), belongs to \(C\cup W\). If \(Q_U\in C\), then \(u>1-y>11/15\); actual left/upper endpoint projections exclude positive rotation of \(C\), and give
\[
r<\Delta(y). \tag{3}
\]
If \(Q_U\notin C\), original \(W\) bridges the actual endpoint \((0,u)\) of \(C\) and \(Q_U\). Its actual upper-left support normal has half-angle \(T\in(0,1)\); no bound \(T\le\sqrt2-1\) is presumed. The two point projections give \(u>1-T,D<g(T)+y\). Combined with the long-chord budget and (2),
\[
r<D+T+2-3\mu
<y-\frac{T(1-T)}{1+T}.
\]
Set \(z=y-r\). Then
\[
0<\chi(T)<z<y<4/15. \tag{4}
\]
The free corner has not been moved; both bridge points and the left-gap endpoint remain actual.

### 3. Exhaust the bottom-midpoint ownership of V1

**Class A: \(V_1\) does not contain \(B_0\).** Its actual bottom leg has \(A_1<\mu\), even if it duplicates left midpoint. Hence \(b>\mu-S_2>1-S_2\). Combining with \(f>1-a-r\) and \(S_2<1-a-\chi(a)\),
\[
b+f>1+\chi(a)-r.
\]
Since \(b+f<1\),
\[
r>\chi(a). \tag{5}
\]

**Class B: \(V_1\) contains \(B_0\), possibly also in \(F\).** Use a target-dominating bottom-host parameter bound for \(V_1\), with \(L_B,S_L,w_B\), while keeping original \(C,F,W\) fixed. The old legs obey \(A_1\le L_B,D_1\le S_L\), so
\[
\ell\ge2\mu-S_L-D,\qquad
b\ge2\mu-L_B-S_2.
\]
These are legitimate weak bounds from dominating parameters; no expanded gap is identified with the old gap. The short-leg bound is \(S_L<g(w_B)<1\).

If \(Q_U\in C\), the inequalities \(u>\mu-y,D<\mu\), together with the long-chord budget, give \(S_L>1+r-y\). If \(Q_U\notin C\), the actual bridge bound \(Y_{\max}<T\), \(D+Y_{\max}<D+T<1+y\), gives the same result. Thus \(z=y-r>0\), \(S_L>1-z\), and
\[
w_B<\frac{z}{2-z}.
\]
The cosine cap therefore gives
\[
L_B-1<\Delta(z). \tag{6}
\]
The two full nonempty chords of \(F\) satisfy
\[
b+f>1+\chi(a)-r-(L_B-1),
\]
hence
\[
r+\Delta(z)>\chi(a). \tag{7}
\]
Here \(r\ge0\) and \(0<z\le y<4/15\). Since \(\Delta(z)<z\), (7) also forces \(\chi(a)<r+z=y\).

These two classes exhaust \(V_1\), including exact tangency at \(B_0\), which is in Class B. Duplicate midpoint ownership is never forbidden by convention.

### 4. A lower bound for the right-host angle function

If \(\chi(a)<y\), then (1) implies \(\chi(a)<\rho_2\). The two projection caps
\[
L_2(1-a^2)\le1+a^2,\qquad2aL_2\le1+a^2
\]
force
\[
1/3<a<1/2,\qquad\chi(a)>1/6. \tag{8}
\]
Indeed, if \(a\le1/3\), then \(\rho_2\le a^2/(1-2a^2)\). This upper bound is at most \(\chi(a)\) exactly when \(1-2a-3a^2+2a^3\ge0\); this polynomial decreases on that interval and has endpoint value \(2/27>0\), a contradiction.

If \(a\ge1/2\), then \(\rho_2\le(1-a)^2/(6a-1-a^2)\), which is at most \(\chi(a)\) exactly when \(7a^2-a-a^3-1\ge0\). This polynomial increases on the interval and has left endpoint value \(1/8>0\), also a contradiction. In between,
\[
\chi(a)-1/6=\frac{(3a-1)(1-2a)}{6(1+a)}>0.
\]
No sampled-angle estimate is used.

### 5. C owns the upper endpoint: both bottom-host classes fail

In Class A, (5) gives \(r>\chi(a)\). The comparison in (1) implies \(\chi(a)>y/3\), checking \(a\le1/2\) and \(a\ge1/2\) separately. But (3) gives \(r<\Delta(y)<2y/11<y/3\), impossible.

In Class B, (7) implies \(\chi(a)<y\), so (8) applies. As \(r\ge0,z=y-r\le y\), (3) gives
\[
r+\Delta(z)<2\Delta(y)<2\Delta(4/15)
=16/165<1/6<\chi(a),
\]
contrary to (7). Thus every \(Q_U\in C\) branch is excluded.

### 6. The original free corner bridges: common strict bounds

Now (4) applies. In Class A, \(\chi(a)<r<y\), so (8) gives \(r>1/6>3/20\), and \(z=y-r<4/15-1/6=1/10<3/28\).

In Class B, (7) and \(\Delta(z)<z\) again give \(\chi(a)<y\), hence \(\chi(a)>1/6\). Therefore
\[
z-\Delta(z)=y-r-\Delta(z)<y-\chi(a)<1/10.
\]
The function \(z-\Delta(z)\) increases strictly on \(0<z<4/15\), with derivative
\[
\frac{2-6z+3z^2}{2(1-z)^2}>0,
\qquad3/28-\Delta(3/28)=141/1400>1/10.
\]
Thus \(z<3/28\). By (7),
\[
r>\chi(a)-\Delta(z)>1/6-\Delta(3/28)
=673/4200>3/20.
\]
Both classes yield
\[
r>3/20,\qquad0<\chi(T)<z<3/28. \tag{9}
\]
The identity
\[
\chi(T)-3/28=\frac{(7T-1)(3-4T)}{28(1+T)}
\]
therefore gives the exhaustive continuous split
\[
T<1/7\quad\hbox{or}\quad T>3/4. \tag{10}
\]
This is an algebraic full-domain split, not an interval sampling tree.

### 7. Both free-corner angle ranges contradict actual projections of C

If \(T<1/7\), the bridge gives \(u>1-T>6/7\). The actual long left chord and upper endpoint force negative rotation of \(C\), and
\[
r<\Delta(T)<\Delta(1/7)=1/84,
\]
contrary to \(r>3/20\).

If \(T>3/4\), the actual left leg of \(W\) satisfies \(D<g(T)+y<1/7+4/15=43/105\). The real gap endpoint in (2) gives
\[
\ell_+\ge\mu-D>62/105. \tag{11}
\]
Choose near-horizontal normals of \(C\) as \((p,\varepsilon\sigma),(-\varepsilon\sigma,p)\), \(p\ge\sigma>0,p^2+\sigma^2=1\). It contains actual left and right points \(L=(-\mu,0)\), \((r,0)\), with chord span \(H=\mu+r>23/20\). Axial directions cannot contain \(H>1\). The width condition \(pH\le1\) gives \(p<20/23\). Thus the central half-angle \(\eta=\sigma/(1+p)\) obeys
\[
\eta^2=\frac{1-p}{1+p}>3/43>(5/19)^2.
\]
For positive rotation, the other projection span from \((-\mu,\ell_+)\) to \((r,0)\) gives \(\sigma H+p\ell_+\le1\), hence
\[
\ell_+\le(1-\sigma H)/p<(1-\sigma)/p
=g(\eta)<g(5/19)=7/12.
\]
For negative rotation, the appropriate span is \(pH+\sigma\ell_+\le1\), so
\[
\ell_+<(1-p)/\sigma=\eta\le\sqrt2-1<7/12.
\]
Both contradict (11), because \(62/105-7/12=1/140>0\).

The two angle ranges in (10) are exhausted, as are the upper-endpoint owner and bottom-midpoint classes. The final positive-horizontal two-gap same-side representative is excluded. Together with R20A, R21, R22, and R22A, all three G4 host representatives, every horizontal type of \(F\), and every actual outer join/gap pattern are excluded for every \(a>2\).

<a id="technical-part-D"></a>
# Technical Part D. Opposite owned midpoints

Modules: [R24](#R24), [R24A](#R24A), [R25](#R25).

<a id="R24"></a>
## R24. Exclusion of the G3 representative with both hosts on the F side

**Scope.** The target is \(T_\mu=[-\mu,\mu]^2\), \(\mu>1\). The same actual tiles satisfy \(L=(-\mu,0),O\in C\) and \(R=(\mu,0)\in F\), \(O\notin F\). The selected bottom and top midpoint hosts are respectively \(V_2,V_3\). All replacements below are individual target-relative covering dominations with \(C,F\) fixed. The conclusion concerns this representative.

Here \(L=m_L=(-\mu,0)\) and \(R=m_R=(\mu,0)\) are local aliases for outer midpoints, not the axial endpoints \(L_C,R_C\); the displayed chord \(LO\) means \(m_LO\). The central half-angle is \(\eta\), corresponding to the source's local letter h.

### 1. Actual joins and the right-edge deficit

The tile \(C\) misses the top, bottom and right edges; \(F\) misses the left edge and meets the horizontal central segment only in its positive open half. Normalize \(V_2,V_3\), leaving \(V_1,V_4,C,F\) fixed. Their long legs, short right legs, central vertical penetrations and half-angles satisfy
\[
L_i\ge\mu,\quad U_i<t_i,\quad S_i<g(t_i),\qquad g(t)=\frac{1-t}{1+t}.\tag{1}
\]
Their long horizontal chords exclude the entire central horizontal line. The left corner tiles cannot meet its positive open half, by the unit-square diameter. Thus \(C,F\) must actually join there. Any top-edge corner gap would lie in the left half, which neither \(C\) nor \(F\) can cover; hence the top is joined, as is the bottom. R20's unique-gap theorem for a nonempty central vertical section of \(F\) therefore gives
\[
F\cap\{x=0\}=\varnothing.\tag{2}
\]
This excludes tangency too, rather than merely asserting zero section length.

Write \(r,u,d\) for the actual right, upper and lower axial reaches of \(C\), and \(\ell_+,\ell_-\) for its upward and downward reaches on the left outer line. Write \(D_1,D_4\) for the actual left legs of the unchanged corner tiles and \(J_1,J_4\) for their target-relative central vertical lengths. These sections can be empty, tangent or floating; they are not assumed rooted at an outer midpoint. They lie respectively on the negative and positive half-axes.

Let \(b\) be the full right-edge chord of \(F\), and \(f\) its horizontal ray from \(R\) toward the left. Since \(S_2,S_3<1<\mu\), the true right-edge gap straddles \(R\), including its endpoints, and belongs to \(F\). Hence
\[
b\ge2\mu-S_2-S_3,\qquad f\ge\mu-r.
\]
The actual rooted sections of this same tile obey \(b+f^2\le2\) and \(b\le\sqrt2\). Consequently
\[
S_2+S_3>(1-r)^2,\qquad S_2+S_3>\frac47.\tag{3}
\]
The second comparison uses \(2-\sqrt2>4/7\), equivalently \(10/7>\sqrt2\).

### 2. Joint projections of C and scalar budgets

After a vertical reflection, the normals of \(C\) are \((p,s),(-s,p)\), where \(p\ge s>0\), \(p^2+s^2=1\). An axis-aligned tile cannot contain the chord \(LO\) of length \(\mu>1\). Put
\[
\eta=\frac{s}{1+p}\in(0,\sqrt2-1]\subset(0,5/12),\quad G=g(\eta),\quad
\delta(\eta)=\frac{2\eta^2}{1-\eta^2},\quad q(t)=\frac{t}{2-t}.
\]
Projection widths of the actual points in \(C\) give
\[
u<\eta,\quad d<G,\quad r<\delta(\eta),\quad \ell_++d<G,\quad \ell_-+u<\eta.\tag{4}
\]
For example \(s\mu+p(\ell_++d)\le1\), \(p\mu+s(\ell_-+u)\le1\), and \(p(\mu+r)\le1\). The reaches are constrained jointly within the same tile.

Define
\[
M(\eta)=q(\eta)+q(G)=\frac \eta{2-\eta}+\frac{1-\eta}{1+3\eta},\quad
A(\eta)=1-G-q(\eta)=\frac{3\eta(1-\eta)}{(1+\eta)(2-\eta)},\quad T_0(\eta)=g(A(\eta)).
\]
The required scalar inequalities are
\[
0<\eta\le\tfrac13:\quad M(\eta)+\eta/12<(1-\delta(\eta))^2,\quad
T_0(\eta)<(1-\delta(\eta))^2;\tag{5}
\]
\[
\tfrac13\le \eta\le\sqrt2-1:\quad M(\eta)\le\tfrac8{15},\quad
T_0(\eta)\le\tfrac7{13}<\tfrac47.\tag{6}
\]
Here are exact certificates. The first difference in (5) is
\[
\frac{hP(\eta)}{12(2-\eta)(1-\eta^2)^2(1+3\eta)},\quad
P=82-185\eta-401\eta^2+514\eta^3+556\eta^4-377\eta^5+3\eta^6.
\]
On \([0,1/3]\), \(P'\le-185-122\eta/3<0\), while \(P(1/3)=32/243>0\). The second difference is
\[
\frac{hQ(\eta)}{(1-\eta^2)^2(1+2\eta-2\eta^2)},\quad
Q=3-7\eta-14\eta^2+22\eta^3+19\eta^4-19\eta^5.
\]
There \(Q'\le-113/27-6\eta<0\), \(Q(1/3)=20/243>0\); these derivative estimates use only \(\eta\le1/3\), for instance \(66\eta^2\le22\eta\) and \(76\eta^3\le76/27\). All displayed denominators are positive. Furthermore
\[
M'=\frac{14(\eta^2+2\eta-1)}{(2-\eta)^2(1+3\eta)^2}\le0,\qquad
A-\frac3{10}=\frac{3(2-3\eta)(3\eta-1)}{10(2-\eta)(1+\eta)}\ge0
\]
on the large-angle interval, proving (6).

If \(C\) directly joins both vertical host sections, then \(t_2>1-d\), \(t_3>1-u\), so \(S_2+S_3<M(\eta)\), contradicting (3), (5), (6). More quantitatively,
\[
J_1+J_4>\eta/24.\tag{7}
\]
Indeed, length coverage alone gives \(t_2+J_1>1-G\), \(t_3+J_4>1-\eta\). Since \(g\) decreases on \([0,\infty)\) and \(|g'|\le2\),
\(S_2+S_3<M+2(J_1+J_4)\). If \(J_1+J_4\le \eta/24\), (5) contradicts (3) for small \(\eta\); for large \(\eta\), the upper bound is \(8/15+5/144=409/720<4/7\). This calculation does not root a floating section at the boundary.

### 3. A bridge bound for the original corner tile

Suppose \(u+U_3<\mu\). By (2) and the half-axis assignments, only the original \(W=V_4\) covers the open gap from \((0,u)\) to \((0,\mu-U_3)\); closedness puts both endpoints in \(W\). In its inward coordinates \(X=x+\mu,Y=\mu-y\), let \(D\) be its true left leg and choose positive normal \((c,s)\), \(c^2+s^2=1\). The axis-aligned case cannot reach the line at distance \(\mu>1\). For \(T=s/(1+c)\in(0,1)\), projections of the corner and inner endpoint give
\[
c\mu+s(\mu-u)\le1\quad\Longrightarrow\quad T>1-u.
\]
Projecting the actual leg endpoint \((0,D)\) against the other bridge endpoint \((\mu,U_3)\) gives \(cD+s\mu-cU_3\le1\). Therefore
\[
D<U_3+g(T)<t_3+q(u).\tag{8}
\]
We used \(u<1\) and \(g(1-u)=q(u)\). No replacement of \(W\), boundary attachment of its chord, or shared chord origin is assumed. Reflection gives \(D_1<t_2+q(d)\) whenever \(d+U_2<\mu\).

### 4. Excluding a left-edge corner gap

Suppose \(D_1+D_4<2\mu\). The entire actual gap belongs to \(C\), so
\[
D_4+\ell_+\ge\mu,\quad D_1+\ell_-\ge\mu.\tag{9}
\]
These remain valid weak inequalities if one corner already reaches the left midpoint; duplicated midpoint membership is allowed. On the upper half-axis either there is a direct join, giving \(t_3>1-u\), or (4), (8), (9) give \(t_3>1-G+d-q(u)\). Similarly
\[
t_2>1-d\quad\hbox{or}\quad t_2>1-\eta+u-q(d).\tag{10}
\]
Enlarge the parameter domain to \(0\le u\le \eta,0\le d\le G\). For each of the four choices, the sum of the two resulting \(g\)-bounds is separately convex in \(u,d\): \(g\) is decreasing and convex, \(q\) increasing and convex. The arguments of \(g\) stay positive; their smallest possibilities are \(A(\eta)\) and
\[
A_b=1-\eta-q(G),\qquad A_b-A=
\frac{3\eta(1-\eta)(1-2\eta-\eta^2)}{(2-\eta)(1+\eta)(1+3\eta)}\ge0.
\]
The maximum is thus at a rectangle vertex. The vertex expressions reduce to \(M,T_0,g(A_b),q(\eta),q(G),q(q(\eta)),q(q(G))\) and the corresponding sums. Using \(g(A_b)\le T_0\), \(q(q(t))\le q(t)\), one obtains
\[
S_2+S_3<\max\{M(\eta),T_0(\eta)\}.\tag{11}
\]
This is convex optimization on the full rectangle. Equations (3), (5), (6) contradict (11). Hence
\[
D_1+D_4\ge2\mu.\tag{12}
\]

### 5. The unique left midpoint host and angle loss

At least one of \(V_1,V_4\) now contains \(L\). If both did, their long left chords would give \(J_1=J_4=0\), violating (7). Reflect to make \(V_1\) the unique such host, normalize it, and keep the original \(V_4\). Put \(a=t_2,w=t_1,\epsilon=\delta(w)\). The joined bottom \(L_2+S_1\ge2\mu\) and the R17 angle lemma give
\[
w<\chi_2:=\frac{L_2-1}{3-L_2}<\min(a,1-a),\qquad w<4/15.\tag{13}
\]
Here \(\chi_2\) is the source's local angle bound, distinct from the global midpoint count \(\kappa\). Since \(J_1=0\), (7) gives \(J=J_4>\eta/24\). Left joining and \(L_1\le1+\epsilon\) imply \(D_4>1-\epsilon\). As \(J>0\), both parallel sections of the original \(V_4\) are nonempty, so \(D_4+J\le B(\mu)<1\). Thus
\[
\eta/24<J<\epsilon.\tag{14}
\]
The projection caps, used only with positive denominators, give
\[
w<Y_c(a)=\frac{a^2}{1-2a^2},\qquad
w<Y_s(a)=\frac{(1-a)^2}{6a-1-a^2}.\tag{15}
\]
The latter decreases on \([9/20,1)\). A useful coarse consequence is
\[
\epsilon<2a/5.\tag{16}
\]
For \(a\le2/5\), \(w<Y_c(a)\le10a/17<2a/3\); for \(a\ge2/5\), \(w<4/15\le2a/3\). Together with \(w<4/15\), this gives \(\epsilon<80a/209<2a/5\).

### 6. Both rotation signs of C

Keep \(V_1\) fixed as left host; a further reflection must not silently change this role.

If \(d<\eta\), the missing \(V_1\) vertical section forces \(d+U_2\ge\mu\), hence \(a>1-\eta>1/2\). Monotonicity of \(Y_s\) gives
\[
w<Y_s(1-\eta)=\frac{\eta^2}{4-4\eta-\eta^2}<\eta^2/2.
\]
Since \(\eta<5/12\), \(w<1/8\) and
\[
\epsilon<\frac{32}{63}\eta^4<\frac{125}{3402}\eta<\eta/24,
\]
contradicting (14).

Otherwise \(u<\eta,d<G\). The lower join gives \(a>1-G\), hence
\[
\eta<\frac a{2-a},\quad r<\Delta(a):=\frac{a^2}{2(1-a)},\quad
q(\eta)<\frac a{4-3a}.\tag{17}
\]
The direct upper join was already excluded in Section 2, so the original \(V_4\) bridges. Equation (8) and \(D_4>1-\epsilon\) imply \(t_3>1-\epsilon-q(\eta)\). Put \(X=\epsilon+q(\eta)\); in every interval below \(X<1\), and
\[
S_2+S_3<g(a)+\frac X{2-X}.\tag{18}
\]
For \(0<a\le9/20\), (16), (17) give \(X<4a/5\le9/25\), so
\[
S_2+S_3<1-\frac{40}{29}a+\frac{20}{41}a
=1-\frac{1060}{1189}a.
\]
But \(1060/1189>9/11\), whereas \((1-r)^2>(1-\Delta(a))^2>1-2\Delta(a)\ge1-9a/11\), violating (3).

For \(9/20\le a\le1/2\), \(w<121/599<3/14\), \(\epsilon<18/187<1/10\), and \(q(\eta)<1/5\). Thus \(X<3/10\) and
\(S_2+S_3<11/29+3/17=274/493<4/7\).

For \(1/2\le a<1\), \(w<1/7\), \(\epsilon<1/24\), \(q(\eta)<5/19\), hence \(X<139/456<1/3\) and \(S_2+S_3<1/3+1/5=8/15<4/7\). Each violates (3). These intervals cover all \(a\in(0,1)\), with overlapping endpoints. Both rotation signs and both left-edge states are excluded, completing this G3 representative.

<a id="R24A"></a>
## R24A. Reduction of the G3 representative with both hosts on the C side

**Scope.** The actual tiles satisfy \(L,O\in C\), \(R\in F\), \(O\notin F\). Normalize \(V_1\) as bottom host and \(V_4\) as top host, retaining \(C,F,V_2,V_3\). This module excludes the case where the central vertical section of \(F\) is empty and reduces the nonempty case; R25 supplies the final exclusion.

The local outer-midpoint aliases are \(L=m_L=(-\mu,0)\), \(R=m_R=(\mu,0)\), distinct from \(C\)'s axial endpoints. The central half-angle is \(\eta\), the source's local h.

### 1. The true left-edge gap prohibits both direct joins

The normalized left short legs, vertical penetrations and angles obey
\[
S_i<g(t_i)<1,\quad U_i<t_i,\quad S_i+U_i\le B(\mu)<1.
\]
Only \(C\) can cover the left-edge gap. Its full left chord \(\ell\) therefore satisfies
\[
\ell\ge2\mu-S_1-S_4>0.\tag{A1}
\]
The gap crosses the left midpoint, and both endpoints belong to \(C\). Both relevant parallel sections of \(C\) are nonempty, so \(\ell+u+d\le B\). If \(u+U_4\ge\mu\), then
\[
\ell+u\ge3\mu-S_1-S_4-U_4>3\mu-1-B>B,
\]
a contradiction. The lower argument is identical, giving
\[
u+U_4<\mu,\qquad d+U_1<\mu.\tag{A2}
\]
This conclusion does not require an empty section of \(F\).

### 2. An empty vertical section of F forces horizontal joining

Assume \(F\cap\{x=0\}=\varnothing\). The original right corner tiles are the sole bridges in (A2). Closedness yields
\[
(0,u),(0,\mu-U_4)\in V_3,\quad
(0,-d),(0,-\mu+U_1)\in V_2.\tag{A3}
\]
Their central vertical sections have positive length and cannot float arbitrarily. Neither tile can also contain the actual right endpoint \(Q=(r,0)\) of \(C\). Indeed, for \(V_3\), positive normals \((c,s)\), \(c^2+s^2=1\), would give
\[
c(\mu-r)+s\mu\le1,\quad c\mu+s(\mu-u)\le1.
\]
Eliminating gives \(r+u\ge2\mu-K>1\), with
\(K=(c+s-\mu)/(cs)<1\), since \(c+s-1\le cs\). But the actual long-chord lemma for \(C\) gives \(\mu+\ell+r+u<2\), hence \(r+u<1\). Axis alignment is already impossible because of the span \(\mu>1\). The lower reflection uses \(r+d<1\). Thus
\[
Q\notin V_2\cup V_3.\tag{A4}
\]
The long horizontal outer chords of \(V_1,V_4\) exclude the central horizontal line. Take points immediately to the right of \(Q\) and pass to a constant tile subsequence in the finite closed cover. Equation (A4) forces \(Q\in F\). Its rooted horizontal reach satisfies
\[
f\ge\mu-r.\tag{A5}
\]
This is an actual join derived from closedness, not from adding section lengths.

### 3. Joint outer-leg and bridge budget

Reflect so that \(u<\eta,d<G=g(\eta)\), \(0<\eta\le\sqrt2-1\). Use the same-tile inequalities
\[
r<\delta(\eta),\quad\ell_++d<G,\quad\ell_-+u<\eta.
\]
The left gap gives \(\ell_+\ge\mu-S_4,\ell_-\ge\mu-S_1\), whence
\[
t_4<g(1-G+d),\qquad t_1<g(1-\eta+u).\tag{A6}
\]
Here \(g\) decreases and \(g(g(t))=t\). If \(E_2,E_3\) are the original right outer legs, the reflected actual-bridge lemma R24 gives
\[
E_3<U_4+q(u)<t_4+q(u),\quad E_2<U_1+q(d)<t_1+q(d).
\]
Consequently
\[
E_2+E_3<[g(1-\eta+u)+q(u)]+[g(1-G+d)+q(d)].\tag{A7}
\]
For \(0\le x\le a<1\), the positive-denominator identity
\[
q(a)-g(1-a+x)-q(x)
=\frac{x(a-x)(4-a)}{(2-a)(2-x)(2-a+x)}\ge0\tag{A8}
\]
with \((a,x)=(\eta,u),(G,d)\) proves
\[
E_2+E_3<M(\eta):=q(\eta)+q(G).\tag{A9}
\]
This uses the original bridge tiles and the same actual \(C\).

### 4. Closing the empty-section case

The true right gap crosses \(R\): (A3) prevents either right corner tile from also containing \(R\). Thus \(b\ge2\mu-E_2-E_3\). Equations (A5), \(b+f^2\le2\), \(b\le\sqrt2\) give
\[
E_2+E_3>(1-r)^2,\qquad E_2+E_3>4/7.
\]
For \(\eta\le1/3\), R24 gives \(M<(1-\delta(\eta))^2<(1-r)^2\). For \(\eta\ge1/3\), it gives \(M\le8/15<4/7\). Both contradict (A9), excluding the entire empty-section case.

### 5. Actual reduction when F has a nonempty vertical section

By R20's unique-gap theorem, reflect to make the top the unique true outer gap belonging to \(F\); its central vertical section lies only in the positive half-axis, and the bottom is joined. Equation (A2) makes the original \(V_2\) bridge the lower gap with positive section length.

If \(V_3\) also meets the central vertical line, even tangentially, all six tiles have nonempty sections on two vertical lines at distance \(\mu\): \(C,V_1,V_4\) on the left and central lines; \(F,V_2,V_3\) on the right and central lines. Their total contribution to the three target vertical segments is at most \(6B<6\mu\), impossible. Therefore
\[
V_3\cap\{x=0\}=\varnothing.\tag{A10}
\]
Only \(F\) can fill the upper gap in (A2), so
\[
(0,u),(0,\mu-U_4)\in F.\tag{A11}
\]
One cannot reuse (A4) for \(V_3\), which no longer bridges the upper endpoint.

### 6. The right edge must be joined

Do not reflect the fixed host pattern further. Write \(\{A,D\}=\{\eta,g(\eta)\}\) with \(u<A,d<D,A+D<1\). Cross-projections and the left gap imply
\[
t_1<g(1-A+u),\quad t_4<g(1-D+d).
\]
Since \(g(1-A+u)=(A-u)/(2-A+u)\le A-u\), and by (A8),
\[
t_1+u<A,\qquad t_4+q(d)<q(D).\tag{A12}
\]
The full central vertical chord of \(F\) is at least \(\mu-U_4-u\). Both it and its right chord \(b\) are nonempty, so
\[
b+v_F\le B<1\quad\Longrightarrow\quad b<t_4+u.\tag{A13}
\]
If the right edge had a corner gap, the lower bridge \(V_2\) could not also contain \(R\), so \(E_2<\mu\). The lower gap endpoint and \(R\) lie in \(F\), giving \(b\ge\mu-E_2>1-E_2\). The bridge estimate \(E_2<t_1+q(d)\) would then imply
\[
1<b+E_2<t_1+t_4+u+q(d)<A+q(D)<A+D<1.
\]
Thus the right edge is joined and \(E_3\ge2\mu-E_2>\mu\): \(V_3\) actually duplicates \(F\)'s membership at \(R\).

Normalize \(V_3\) as right host, keeping the original \(V_2,C,F\). The top gap cannot disappear, since that would leave both top and bottom joined while the unchanged \(F\) has a nonempty vertical section, violating R20. Its empty central vertical section, and the right and bottom joins, persist.

### 7. A conditional continuous upper bound

The remaining representative has \(V_1\) bottom, \(V_4\) top, \(V_3\) right, and the original \(V_2\) bridging below. Five tiles have two nonempty vertical sections; \(V_3\) contributes only its right long leg \(L_3\) to the three vertical target lines. Hence
\[
6\mu\le5B(\mu)+L_3,\qquad L_3\le\sqrt2.\tag{A14}
\]
For \(1<\mu\le\sqrt2\), the two-branch formula gives \(B(\mu)\le\mu-\sqrt{\mu^2-1}\). In its second branch this follows from
\[
(3\mu-2\sqrt2)^2-(\mu^2-1)=(2\sqrt2\mu-3)^2\ge0,
\]
where \(3\mu-2\sqrt2\ge0\). Thus \(\mu+5\sqrt{\mu^2-1}\le\sqrt2\). Squaring on these nonnegative sides yields
\[
24\mu^2+2\sqrt2\mu-27\le0,\qquad
2\mu\le\frac{5\sqrt{26}-\sqrt2}{12}.\tag{A15}
\]
This is a bound conditional on this residual representative. It is not a global improvement and does not exclude \(\mu\) arbitrarily close to one. R25 continues the exclusion.

<a id="R25"></a>
## R25. Excluding all three G3 host representatives

**Scope.** Label the corner tiles \(V_1,V_2,V_3,V_4\) as lower-left, lower-right, upper-right, upper-left. The actual tiles satisfy \(L=(-\mu,0),O\in C\), \(R=(\mu,0)\in F\), \(O\notin F\). The tile \(C\) misses the top, bottom and right edges, and \(F\) misses the left edge. This module uses R24 and R24A and treats the remaining diagonal representative. The source presents this as a completed candidate exclusion; no independent validation is asserted here.

Here \(L=m_L\) and \(R=m_R\) are local outer-midpoint aliases, not \(L_C,R_C\). The central half-angle is \(\eta\), corresponding to the source's local h; the auxiliary loss function is separately denoted \(\zeta\).

### 1. Representatives and common inequalities

Each corner tile contains at most one outer midpoint. Up to vertical reflection, the top/bottom midpoint hosts are: \(V_3,V_2\) on the \(F\) side (R24); \(V_4,V_1\) on the \(C\) side (R24A excludes the empty-section case); or \(V_4,V_2\), the diagonal case. Duplicated membership with \(C\) or \(F\) is allowed.

The chord \(LO\) makes \(\mu>\sqrt2\) impossible, so assume \(1<\mu\le\sqrt2\). Corner tiles avoid \(O\), and \(F\) avoids \(O\). A finite closed cover therefore makes \(O\) an interior point of its unique host \(C\); in particular \(r,u,d>0\).

Use
\[
g(t)=\frac{1-t}{1+t},\quad q(t)=\frac t{2-t},\quad
\delta(t)=\frac{2t^2}{1-t^2},\quad\Delta(t)=\frac{t^2}{2(1-t)}.
\]
A target-dominating normalization of one anchored corner gives
\[
S<g(t),\quad U<t,\quad L\le\sqrt2,\quad L\ge\mu,\quad
L(1-t^2)\le1+t^2,\quad2tL\le1+t^2,\quad0<t<1.\tag{1}
\]
Two nonempty parallel full sections at distance \(\mu\) have sum at most \(\mathcal B=B(\mu)<1\). Tangency is nonempty; a completely empty section does not permit this bound.

Write the source's local angle bound as \(\chi(L)=(L-1)/(3-L)\), distinct from the global midpoint count \(\kappa\). R17 gives
\[
\chi(L)<\min(t,1-t),\quad\chi(L)<4/15.\tag{2}
\]
An actual join \(L_i+S_j\ge2\mu\) gives \(t_j<\chi(L_i)\). When their denominators are positive, the projection caps give
\[
\chi(L)\le Y_c(t)=\frac{t^2}{1-2t^2},\quad
\chi(L)\le Y_s(t)=\frac{(1-t)^2}{6t-1-t^2}.\tag{3}
\]
Here \(Y_c\) increases, and \(Y_s\) decreases on the used interval \([2/5,1)\).

For \(C\), write \(\ell_+,\ell_-\) for left-edge reaches and \(\eta\in(0,\sqrt2-1]\) for its nearest-horizontal half-angle. Both rotation signs are encoded by
\[
\{A,D\}=\{\eta,G\},\ G=g(\eta),\quad u<A,\ d<D,\quad
\ell_++d<D,\quad\ell_-+u<A,\quad r<\delta(\eta).\tag{4}
\]
Since \(A+D<1\), both signs also give
\[
u<g(d).\tag{5}
\]
R24 proves, for \(M=q(\eta)+q(G)\) and \(T_0=g(1-G-q(\eta))\),
\[
\eta\le1/3:\quad M+\eta/12<(1-\delta(\eta))^2,\quad T_0<(1-\delta(\eta))^2;\tag{6}
\]
\[
\eta\ge1/3:\quad M\le8/15,\quad T_0\le7/13<4/7.\tag{7}
\]

### 2. A local exit lemma closes the C-side residual case

Let \(V_4\) be a top host with long leg \(L\), half-angle \(t\), penetration \(U\), and endpoints
\[
P=(L-\mu,\mu),\qquad V=(0,\mu-U).
\]
**Exit lemma.** Any unit tile \(Q\) containing \(R,P\) cannot contain \(V\); every positive central vertical point in \(Q\) has height below \(\chi(L)\).

Choose its nearest-horizontal normals \((p,\pm s),(\mp s,p)\), \(p\ge s\ge0\), \(p^2+s^2=1\). Axis alignment is excluded by the vertical span \(\mu>1\). Put \(\eta=s/(1+p)\le\sqrt2-1\). For the positive sign the \(RP\) projection width is \(p\mu+s(2\mu-L)>1\): indeed \(2\mu-L>2-\sqrt2>\sqrt2-1\ge \eta\), and \(p+sH=1\). Thus only the negative sign remains. With \(z=L-\mu\ge0\), its other projection gives
\[
p(2\mu-L)+s\mu\le1\quad\Longrightarrow\quad
z>\frac{p+s-1}{p}=\frac{2\eta}{1+\eta}.
\]
Consequently \(\eta<z/(2-z)<\chi(L)\). If \((0,v)\in Q,v>0\), projection with \(R\) gives \(p\mu+sv\le1\), hence \(v<\eta<\chi(L)\). But \(V\) has height \(\mu-U>1-t>\chi(L)\), proving the lemma. No center-membership or prior nonempty-section assumption on \(Q\) is needed.

The C-side residual in R24A has, after reflection, a unique top gap belonging to \(F\), with \(R,P,V\in F\). The exit lemma excludes it. Together with R24A's empty-section argument this closes that representative.

### 3. A new angle budget and a two-step chain

Define the local function \(\zeta(t)=t(1-t)/(1+t)\). Then
\[
q(\chi(L))<\zeta(t).\tag{8}
\]
For \(t\le1/3\), (3) gives \(q(\chi)\le t^2/(2-5t^2)\le3t/13<t/2\le\zeta(t)\). For \(1/3\le t\le1/2\), use \(q(\chi)<q(4/15)=2/13<1/6\le\zeta(t)\), with
\[
\zeta(t)-1/6=\frac{(3t-1)(1-2t)}{6(1+t)}.
\]
For \(t\ge1/2\), (3) gives \(q(\chi)\le(1-t)^2/(14t-3-3t^2)\le2(1-t)/13<(1-t)/3\le\zeta(t)\). All denominators on the stated intervals are positive.

If bottom and left are joined, and \(V_2,V_1,V_4\) have respective half-angles \(\alpha,w,x\), then
\[
w<\chi_2,\quad x<\chi_1,\quad x<w/3,\quad w<2\alpha/3,
\quad x<\alpha/4,\quad x<(1-\alpha)/3.\tag{9}
\]
For \(x<w/3\), use \(w<4/15\) and \(Y_c(w)/w<60/193<1/3\). For \(w<2\alpha/3\), use \(Y_c(\alpha)\le10\alpha/17\) below \(2/5\), and \(w<4/15\) above it. These are continuous projection estimates.

### 4. The diagonal representative has a lower join but no direct upper join

Fix top host \(V_4\) and bottom host \(V_2\); normalize them individually, keeping \(V_1,V_3,C,F\). A bottom gap could only be in the left half, which neither \(C\) nor \(F\) can cover. Hence bottom is joined. If \(F\)'s vertical section is nonempty, R20 places it in the positive half-axis at the unique top gap. In either case \(F\) misses the negative vertical axis.

Put \(x=t_4\). If the left edge has a true gap, its upper endpoint lies in \(C\), so \(\ell_+\ge\mu-S_4\). If \(u\ge\mu-U_4\), then
\[
\ell+u\ge2\mu-S_4-U_4\ge2\mu-\mathcal B>\mathcal B,
\]
violating the nonempty parallel-section bound for \(C\). If left is joined, \(V_1\) actually contains \(L\) and can be normalized as left host. The bottom-left chain gives (9), including \(x<w<\chi_2<1-\alpha\), \(x<4/15\). Its long left chord excludes the central vertical line, so \(d\ge\mu-U_2>1-\alpha>x\). If \(u\ge\mu-U_4>1-x>11/15\), the upper reach must be the large one: \(u<g(\eta),d<\eta\). Then \(\eta<x/(2-x)<x\), impossible. Thus in both left states
\[
u<\mu-U_4.\tag{10}
\]

### 5. A complete original upper bridge is impossible

Assume the original \(V_3\) contains both \((0,u)\) and \(V=(0,\mu-U_4)\). Its section has positive length. It cannot also contain \(Q=(r,0)\), since the projection argument of R24A gives \(r+u>1\), while \(C\)'s actual long chord gives \(r+u<1\). The long horizontal chords of \(V_2,V_4\), and the distance obstruction for \(V_1\), exclude them from the positive horizontal axis. Closedness therefore gives \(Q\in F\), hence \(f\ge\mu-r\).

The bridge \(V_3\) cannot also contain \(R\), so \(E_3<\mu\); also \(S_2<\mu\). The right gap straddles \(R\) and belongs entirely to \(F\). With \(b\ge2\mu-S_2-E_3\), the rooted square and diameter bounds imply
\[
S_2+E_3>(1-r)^2,\qquad S_2+E_3>4/7.\tag{11}
\]
The actual-bridge inequality gives
\[
E_3<U_4+q(u)<x+q(u).\tag{12}
\]

If left has a gap, its upper endpoint and (4) give \(x<g(1-D+d)\). A direct lower join gives \(\alpha>1-d\), \(S_2<q(d)\); identity (A8) of R24A then yields \(S_2+E_3<M\), contrary to (6), (7), (11). Otherwise only the original \(V_1\) bridges below; \(D_1<\alpha+q(d)\), \(D_1+\ell_-\ge\mu\), and \(\ell_-+u<A\) imply \(\alpha>1-A+u-q(d)\). Thus
\[
S_2+E_3<g(1-A+u-q(d))+g(1-D+d)+q(u).\tag{13}
\]
On \(0\le u\le A,0\le d\le D\), all \(g\)-arguments are positive because \(A+D<1\), and the expression is separately convex. Its vertex values are \(M,g(1-A-q(D)),M,q(q(D))+q(A)\). The second is \(T_0\) or \(g(A_b)\le T_0\) from R24, and the last is at most \(M\). Hence (13) is below \(\max(M,T_0)\), again impossible.

If left is joined, normalize \(V_1\) and use (9). Its empty vertical section forces
\[
d>1-\alpha.\tag{14}
\]
If \(d<\eta,u<g(\eta)\), then \(\alpha>1-\eta\), \(w<Y_s(1-\eta)<\eta^2/2\), and
\[
x<Y_c(w)<8\eta^4/31<\eta/12
\]
using \(\eta<5/12\). Equations (12), (14) give \(S_2+E_3<M+x<M+\eta/12\), contradicting (6) for small \(\eta\), and \(8/15+5/144<4/7\) for large \(\eta\).

If \(u<\eta,d<g(\eta)\), then
\[
\eta<\frac\alpha{2-\alpha},\quad r<\Delta(\alpha),\quad
q(u)<\min\left(\frac\alpha{4-3\alpha},\frac5{19}\right).\tag{15}
\]
The function \(F_0(\alpha)=g(\alpha)+\alpha/(4-3\alpha)\) decreases on \((0,1/2]\). Since \(S_2+E_3<g(\alpha)+x+q(u)\), the following exact interval bounds cover all \(\alpha\):

1. If \(\alpha\le2/5\), \(x<\alpha/4\), \(q(u)<5\alpha/14\), so the sum is below \(1-23\alpha/28\), whereas \((1-r)^2>1-2\Delta(\alpha)\ge1-2\alpha/3\).
2. If \(2/5\le\alpha\le9/20\), \(x<16/193\), \(F_0\le4/7\), \(r<81/440\), and \(4/7+16/193<(359/440)^2\).
3. If \(9/20\le\alpha\le12/25\), \(w<121/599\), \(x<14641/329519\), \(F_0\le844/1537\), \(r<72/325\), and \(844/1537+14641/329519<(253/325)^2\).
4. If \(12/25\le\alpha\le1/2\), \(w<169/1031\), \(x<28561/1005839\), \(F_0\le319/592\), and \(319/592+28561/1005839<4/7\).
5. If \(\alpha\ge1/2\), \(w<1/7,x<1/47\). Also \(g(\alpha)+q(u)\le8/15\): on \([1/2,3/5]\), use convexity of \(F_0\) and endpoint values \(8/15,23/44\); above \(3/5\), use \(1/4+5/19<8/15\). Thus the sum is below \(8/15+1/47=391/705<4/7\).

Each contradicts (11). Both left states and both rotation signs are exhausted. Therefore
\[
V_3\text{ cannot contain both }(0,u)\text{ and }(0,\mu-U_4).\tag{16}
\]
The proof allowed either an empty or a positive vertical section of \(F\).

### 6. The empty F-section diagonal branch

By (10) the upper axial gap is genuine. If \(F\)'s central vertical section is empty, only \(V_3\) can fill it. Closedness forces the complete bridge prohibited by (16). Thus the diagonal case must have a nonempty, positive section of \(F\), belonging to a unique top gap.

### 7. Shared bridging also gives a contradiction

The actual top exit gives \(R,P\in F\); the exit lemma excludes \(V=(0,\mu-U_4)\) from \(F\), and (10) excludes it from \(C\). Taking a limit from immediately below \(V\) forces \(V\in V_3\), whose central vertical section is nonempty.

If \(V_1\) also met that line, all six tiles would have two nonempty vertical sections at distance \(\mu\): \(C,V_1,V_4\) on left/central, and \(F,V_2,V_3\) on right/central. Their budget \(6\mathcal B<6\mu\) is impossible. Thus \(V_1\)'s entire section is empty and
\[
d\ge\mu-U_2.\tag{17}
\]
Equation (16) prevents \(V_3\) from containing \((0,u)\). A limit from above that point then forces \((0,u)\in F\). Let \(v_F\) be the highest point of \(F\)'s central vertical section. The exit lemma gives
\[
u\le v_F<\chi_4<1-x<\mu-U_4.
\]
The original \(V_3\) must bridge from \(v_F\) to \(V\), so (8) and the bridge bound give
\[
E_3<U_4+q(v_F)<x+q(\chi_4)<x+\zeta(x)
=\frac{2x}{1+x}=1-g(x).\tag{18}
\]
Neither right corner contains \(R\); the true right gap belongs to \(F\). Both parallel sections of \(F\) are nonempty, so \(b<\mathcal B<1\). Right-edge coverage requires
\[
S_2+E_3>1.\tag{19}
\]
If left has a gap, \(\ell_+\ge\mu-S_4\), and (17), together with \(\ell_++d<1\), imply \(S_4+U_2>1\). Thus \(\alpha>1-g(x)>x\), giving \(S_2<g(\alpha)<g(x)\), contrary to (18), (19). If left is joined, (9) gives \(\alpha>4x\), while \(S_2<g(\alpha)<1-\alpha\) and (18) gives \(E_3<2x\). Then \(S_2+E_3<1-2x<1\), again impossible. This closes the diagonal case and hence all three G3 representatives in the candidate route.

<a id="technical-part-E"></a>
# Technical Part E. Near-end residual configurations

Modules: [R13](#R13), [R14](#R14), [R15](#R15), [R15S](#R15S), [R16P](#R16P), [R16](#R16), [R16A](#R16A), [R17](#R17), [R18](#R18), [R19](#R19), [R26](#R26), [R27](#R27), [R28](#R28).

<a id="R13"></a>
## R13. Adjacent-corner budgets and necessary restrictions in G2

**Scope.** Work in \(T_\mu=[-\mu,\mu]^2\), \(\mu>1\), with corners indexed lower-left through upper-left. R8 makes \(C\) the unique center host. R12 makes \(F\) an outer-midpoint host with no midpoint shared by \(C,F\). In this G2 branch \(C\) owns no outer midpoint; rotate so \(F\) contains \((0,-\mu)\). All duplicated corner memberships remain allowed. Replacements are stepwise covering dominations, with their resulting branches interpreted on the actual family.

### 1. Geometric and analytic inputs

Convexity and diameter imply that \(F\) misses the positive vertical half-axis, top edge, and upper halves of the side edges. Its rooted vertical reach \(v_F<\mu\). Any nonempty horizontal central section lies in one open half-axis; tangency counts as nonempty. The other three midpoints have distinct selected corner hosts; reflection leaves near and far representatives.

For a normalized anchored corner, with long leg \(L\), short leg \(S\), penetration \(U\), and half-angle \(t\in(0,1)\),
\[
L\ge\mu>1,\quad L+S+U<2,\quad U<t,
\]
\[
S=\frac{1+t^2-2tL}{1-t^2},\quad
L(1-t^2)\le1+t^2,\quad2tL\le1+t^2.\tag{1}
\]
Every corner tile contributes at most two to the six-line target grid. Two **nonempty** full parallel sections at distance \(\mu\) have sum at most \(B(\mu)<1\). A unit tile containing \((-l,0),(r,0),(0,u)\), with nonnegative reaches, satisfies
\[
h+u^2\le2,\qquad h=l+r.\tag{2}
\]
R4 supplies its hand proof; the source also records a fresh continuous-angle check.

### 2. The adjacent-corner inequality

Suppose \(x,y\in(0,1)\), \(L_x,L_y\ge1\), and both corners satisfy the two projection constraints and short-leg formula in (1). Then
\[
L_x+S_y\ge2\quad\Longrightarrow\quad
L_y+S_x+x+2y-y^2\le2.\tag{3}
\]
Actual joins give \(L_x+S_y\ge2\mu>2\). Replacing angles by smaller actual penetrations yields a weaker valid inequality, never its converse.

Put \(a_x=2x/(1-x^2),b_x=(1+x^2)/(1-x^2)\), and similarly for \(y\). Then \(S_x=b_x-a_xL_x\), and joining yields \(L_x\ge2-b_y+a_yL_y\). The left side of (3) is at most
\[
(1-a_xa_y)L_y+b_x-2a_x+a_xb_y+x+2y-y^2.\tag{4}
\]
The certificate below proves \(1-a_xa_y\ge0\), allowing \(L_y\le b_y\). Call the resulting expression \(F(x,y)\).

Since \(S_y\le g(y)\), joining gives \(y\le(L_x-1)/(3-L_x)\). The two projection caps cover the actual angle domain by
\[
0<x\le2/5:\quad0\le y\le Y_c(x)=\frac{x^2}{1-2x^2},
\]
\[
2/5\le x<1:\quad0\le y\le Y_s(x)=\frac{(1-x)^2}{6x-1-x^2}.\tag{5}
\]
The denominators are respectively at least \(17/25,31/25\), and both upper bounds are below one. Define
\[
P=(2-F)(1-x^2)(1-y^2)^2,\quad
Q=(1-x^2)(1-y^2)-4xy.
\]
Substitute \(x=2u/5,y=Y_c(x)v\), or \(x=2/5+3u/5,y=Y_s(x)v\), for \(0\le u,v\le1\), and clear the appropriate powers of the positive \(Y\)-denominators. The resulting degrees are \((15,6)\) for \(P\), \((6,2)\) for \(Q\). In each region all 112 coefficients for \(P\) and all 21 for \(Q\) in the bivariate Bernstein basis are nonnegative: 266 exact rational coefficients in total. In the cosine region the minima are \(0,3013/15625\); both minima in the sine region are zero. Nonnegativity of the basis proves \(P,Q\ge0\), hence (3).

The source's `round13_pair_certificate.json` stores all coefficients. Its independent checker reconstructs the original expressions and the full Bernstein polynomials, checks polynomial identity and every coefficient sign. A separate full nonlinear real counterexample query is recorded as UNSAT. These are full parameter rectangles, not sampled angles.

### 3. Near representative: three nonbottom joins force an empty F horizontal section

Choose \(V_2,V_3,V_4\) as right, top, left hosts, and \(W=V_1\) free. Let its actual bottom and left legs be \(A,D\), its horizontal and negative vertical central lengths \(H,J\). They can float, be empty, or be tangent, and \(A+D+H+J\le2\). Assume
\[
L_2+S_3\ge2\mu,\quad L_3+S_4\ge2\mu,\quad L_4+D\ge2\mu,\tag{6}
\]
and that \(F\) meets the horizontal central line. If \(C\) also met bottom, the two bottom/horizontal parallel budgets, corner grid budget and central vertical union bound would give \(12\mu\le8+2B+2\mu<12\mu\). Other outer sections are redundant under the three joins. Thus \(C\) misses bottom and \(F\) fills its entire residual gap.

Write \(b,f\) for \(F\)'s bottom and horizontal lengths and \(h\) for \(C\)'s full horizontal length. Coverage yields
\[
b\ge2\mu-A-S_2,\quad b+f\le B,\quad
h+f+U_2+U_4+H\ge2\mu,
\]
so \(h\ge4\mu-B-A-H-S_2-U_2-U_4\). With \(\epsilon=2\mu-2>0\), the free-corner grid bound and left/top joins give \(A+H\le2-2\mu+L_4\), \(L_4+U_4<L_3-\epsilon\). Therefore
\[
h>6\mu-B-2-L_3-S_2-U_2+\epsilon.
\]
Apply (3) at the right join: \(L_3+S_2+t_2+2t_3-t_3^2\le2\). Since \(U_2<t_2\),
\(h>6\mu-B-4+2t_3-t_3^2+\epsilon\). Only \(V_3\) can help \(C\) on the upper axis, so \(u\ge\mu-U_3>1-t_3>0\). Hence \(h+u^2>6\mu-B-3+\epsilon=8\mu-B-5>2\), contrary to (2). The horizontal section of \(F\) is therefore completely empty.

### 4. Near right/top joins with empty F section force a bottom gap longer than one

Left joining is not assumed here. Coverage gives \(l\ge\mu-U_4-H,r\ge\mu-U_2,u\ge\mu-U_3\). Put \(t=t_2\) and use the local angle bounds
\[
\chi=\frac{L_2-1}{3-L_2}\in(0,4/15),\quad t_3<\chi,\quad
t_4<w:=\frac{\chi^2}{1-2\chi^2}.
\]
R5 supplies the full-domain single-corner budget
\[
\Phi=1-S_2-t-2\chi+\chi^2-w>0.\tag{7}
\]
If \(H\le S_2\), then \(l>1-S_2-w,r>1-t,u>1-\chi\), and \(l+r+u^2>2+\Phi\), impossible. Thus \(H>S_2\). Both sections of \(W\) are now nonempty, so \(A+H\le B\), giving
\[
A+S_2<B<1,\qquad g_B=2\mu-A-S_2>2\mu-B>1.\tag{8}
\]
Also \(q_U=(0,\mu-U_3)\in C\); since \(t_3<4/15\), its vertical distance from any bottom point exceeds \(26/15>\sqrt2\). Thus \(C\) misses bottom and the entire bottom residual interval, including both endpoints by closedness, belongs to \(F\). The free corner does not contain the bottom midpoint. This is a necessary restriction, not yet a contradiction.

### 5. Far representative: three joins and nonempty F section force J positive

Choose \(V_1,V_2,V_4\) as left, right, top hosts, \(W=V_3\) free. Let its right/top legs and horizontal/vertical lengths be \(A,D,H,J\), with sum at most two. Suppose all three nonbottom edges are joined, \(F\) meets the horizontal central line, and \(J=0\). The same grid argument excludes \(C\) from bottom. Thus
\[
b\ge2\mu-S_1-S_2,\quad b+f\le B,\quad
h+f+U_1+U_2+H\ge2\mu.
\]
Right/top joining gives \(A+D\ge4\mu-L_2-L_4\), so
\[
h\ge8\mu-B-2-L_2-L_4-S_1-S_2-U_1-U_2.
\]
At the left join, (3) gives \(L_4+S_1+t_1+2t_4-t_4^2\le2\). Combining \(U_1<t_1\) and \(L_2+S_2+U_2<2\) yields \(h>8\mu-B-6+2t_4-t_4^2\). Since \(J=0\), \(u\ge\mu-U_4>1-t_4\), and \(h+u^2>8\mu-B-5>2\), impossible. Thus \(J>0\). No claim that three joins force either \(H=0\) or \(J=0\) is made. In particular the withdrawn bound \((c+s-1)/(cs)\le5/6\) is unavailable: this ratio tends to one near axis alignment.

### 6. Far top gap with nonempty F section is excluded

Only \(C\) can fill nonbottom upper gaps: \(F\)'s bottom midpoint and diameter prevent it. A tile containing the center cannot fill both a top-right gap and a left-upper gap, by the triangle area bound \(1/2\). Thus a top gap forces the left edge joined.

If right is also joined, the \(C\) top/horizontal and \(F\) bottom/horizontal budgets, corner grid bound and central vertical union again give \(12\mu\le8+2B+2\mu<12\mu\). The same argument excludes the near case with a top gap, left joined and nonempty \(F\) horizontal section, since its right-upper gap must then be absent.

Otherwise \(C\) fills both right and top gaps. Put
\[
g_B=2\mu-S_1-S_2,\quad g_T=2\mu-L_4-D>0,\quad
g_R=2\mu-L_2-A>0.
\]
The tile \(C\) misses bottom, so \(b\ge g_B\). Actual nonempty parallel sections give
\[
l+r+g_T\le B,\quad u+d+g_R\le B,\quad b+f\le B.
\]
Axis coverage gives \(l+r+f+U_1+U_2+H\ge2\mu\), \(u+U_4+J\ge\mu\). On the lower axis, \(v_F<\mu\) forces \(d>0\). The sum of the three left sides is therefore strictly larger than
\[
3\mu+g_B+g_T+g_R-(U_1+U_2+U_4+H+J).
\]
The three anchored budgets and free-corner budget sum to less than eight, and left joining gives \(L_1+S_4\ge2\mu\). Hence this exceeds \(9\mu-8+L_1+S_4\ge11\mu-8>3\), contradicting the upper bound \(3B<3\).

<a id="R14"></a>
## R14. Forced seams, disappearance of a vertical section, and the near left gap

**Scope.** In \(T_\mu\), \(\mu>1\), \(C\) is the unique center tile and owns no outer midpoint. The same \(F\) contains the bottom midpoint. In the near representative, \(V_2,V_3,V_4\) are right, top, left hosts and \(W=V_1\) is the free lower-left corner. Assume right and top joined and the horizontal central section of \(F\) completely empty. Duplicated midpoint memberships, including \(W\)'s possible membership at the left midpoint, remain allowed.

### 1. Normalized inputs and actual sections

Each anchored corner satisfies
\[
L_i\ge\mu>1,\quad U_i<t_i<1,\quad L_i+S_i+U_i<2,
\]
\[
S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2},\quad
L_i(1-t_i^2)\le1+t_i^2,\quad2t_iL_i\le1+t_i^2.
\]
The assumed joins are \(L_2+S_3\ge2\mu,L_3+S_4\ge2\mu\). Set
\[
t=t_2,\quad\chi=\frac{L_2-1}{3-L_2}\in(0,4/15),\quad
w=\frac{\chi^2}{1-2\chi^2},\quad t_3<\chi,\quad t_4<w.
\]
The letter \(\chi\) denotes the source's angle cap, not the global count \(\kappa\). R13 gives, for the actual bottom leg \(A\) and horizontal length \(H\) of \(W\), \(H>S_2\), \(A+S_2<B(\mu)<1\). The tile \(C\) misses bottom; \(F\) fills the entire bottom gap \(g_B=2\mu-A-S_2\), including endpoints by closedness.

In fact the entire \(F\) lies below \(y=0\). A segment from its bottom midpoint to any point at height at least zero would meet \(y=0\); any such point within distance \(\sqrt2\) of the midpoint belongs to the target horizontal segment. That contradicts its empty section. Coverage gives
\[
l\ge\mu-U_4-H,\quad r\ge\mu-U_2,\quad u\ge\mu-U_3,
\]
and \(l+r+u^2\le2\). We also use that any triangle contained in a unit square has area at most \(1/2\): separately maximize the absolute affine area in each vertex to reduce to square vertices.

### 2. The stronger margin Phi

For \(\Phi=1-S_2-t-2\chi+\chi^2-w\), the strengthened bound is
\[
\Phi>\chi^2/3>\frac{2w^2}{1-3w^2}.\tag{1}
\]
Define
\[
\widetilde\Psi(t,\chi)=\frac{t(1-t)}{1+t}
+\frac{4t\chi}{(1-t^2)(1+\chi)}-2\chi-\chi^2/2.
\]
Then
\[
\Phi-\chi^2/3-\widetilde\Psi
=\frac{\chi^2(1-14\chi^2)}{6(1-2\chi^2)}>0,
\quad \partial_\chi^2\widetilde\Psi
=-\frac{8t}{(1-t^2)(1+\chi)^3}-1<0.
\]
Here \((4/15)^2<1/14\). Concavity reduces positivity to the endpoints of the allowed \(\chi\)-interval; at zero the value is \(t(1-t)/(1+t)>0\).

For \(0<t\le5/12\), use \(K_c=t^2/(1-2t^2)\). Then
\[
\widetilde\Psi(t,K_c)=\frac{-tP(t)}{2(1-t^2)^2(1-2t^2)^2},
\quad P=8t^8-23t^7-40t^6+50t^5+26t^4-35t^3+8t-2.
\]
The Bernstein coefficients of \(-P(5v/12)\) on \([0,1]\) are
\[
2,\frac{19}{12},\frac76,\frac{10993}{13824},\frac{73009}{145152},
\frac{300181}{995328},\frac{16469}{93312},\frac{27810283}{286654464},
\frac{4202143}{107495424}.
\]
All are positive; the source checker also verifies the full polynomial identity.

For \(5/12\le t<1\), use \(K_s=(1-t)^2/(6t-1-t^2)\), giving
\[
\widetilde\Psi(t,K_s)=\frac{(1-t)Q(t)}{2(t^2-6t+1)^2},\quad
Q=2t^4-27t^3+101t^2-49t+5.
\]
Here \(Q'''=48t-162<0\), \(Q''\ge Q''(1)=64\), \(Q'(5/12)=9367/432>0\), \(Q(5/12)=2335/10368>0\). Thus \(Q>0\). The sine interval must begin at \(5/12\): \(Q(2/5)=-73/625\), so R5's weaker-budget split at \(2/5\) cannot be reused.

Finally
\[
\frac{\chi^2}{3}-\frac{2w^2}{1-3w^2}
=\frac{\chi^2(1-10\chi^2+\chi^4)}{3(1-4\chi^2+\chi^4)}>0.
\]
The denominator is positive, and the numerator's quartic decreases on \([0,4/15]\), ending at \(14881/50625>0\). This proves (1).

### 3. A left-edge residual gap is impossible

The three-ray inequality implies
\[
2\ge l+r+u^2>(1-w-H)+(1-t)+(1-\chi)^2,
\]
so \(H-S_2>\Phi\). The two sections of \(W\) are nonempty, hence \(A+H\le B<1\), and
\[
g_B=2\mu-A-S_2>2\mu-1+\Phi>1+\Phi.\tag{2}
\]
R13's adjacent inequality implies \(t_2+t_3<1\), from \(L_3+S_2+t_2+2t_3-t_3^2\le2\), \(L_3\ge1,S_2\ge0\). The forced right and upper endpoints of \(C\) therefore satisfy \(r+u\ge2\mu-U_2-U_3>1\). If \(C\) contained any lower-half left-edge point, R3's reflected outer-point/two-ray bound would give \(r+u<1\). Thus it misses that half-edge.

A true left gap would consequently belong entirely to \(F\), which would contain its upper endpoint \(P=(-\mu,\mu-L_4)\). Together with the two bottom-gap endpoints, this forms a triangle in \(F\) with base \(g_B\) and height \(2\mu-L_4\). Put \(\delta=2w^2/(1-w^2)<1\). The cap \(t_4<w\) gives \(L_4-1<\delta\), so its height exceeds \(1-\delta\). Equation (1) says \(\Phi>\delta/(1-\delta)\); by (2),
\[
g_B(2\mu-L_4)>(1+\Phi)(1-\delta)>1,
\]
contradicting the triangle area bound. Thus left is joined too, uniformly as \(\mu\downarrow1\).

### 4. A forced seam with the original left-host endpoint

Let \(q_L=(-\mu+U_4,0)\). If \(q_L\in C\), then \(l>1-w,r>1-t,u>1-\chi\), giving \(l+r+u^2>2+\Phi+S_2>2\). Since \(F\)'s horizontal section is empty and no other corner can take the left open half-axis, a limit from the host's short segment forces \(q_L\in W\).

In inward coordinates \(X=x+\mu,Y=y+\mu\), normalize \(W\) by
\[
0\le cX+sY\le1,\quad-\beta\le sX-cY\le1-\beta,
\quad c,s>0,\ c^2+s^2=1,\ 0\le\beta\le1.
\]
Its actual bottom leg is \(A=(1-\beta)/s<1\). Define an auxiliary \(D^*=\beta/c\); the actual left leg is
\[
sA+cD^*=1,\qquad D=\min(D^*,1/s).
\]
Do not replace \(D\) by \(D^*\) in a grid budget, especially when \(W\) duplicates the left midpoint. With \(z=(1-c)/s\in(0,1)\), membership of \(q_L\) gives \(c(\mu-D^*)\le sU_4\), hence
\[
A<z+U_4.\tag{3}
\]
Its furthest horizontal-section abscissa is \(X_{\max}=(1-\mu s)/c\). Only \(C\) can cover beyond it, so
\[
l\ge\mu-X_{\max}>\frac{2z}{1+z}.\tag{4}
\]
These conclusions derive the seam from actual coverage; no initial boundary attachment of a floating chord is assumed.

### 5. The negative vertical section of W has zero length

At \(X=\mu\), the actual target-relative negative vertical length is
\[
J=\max(0,K_\mu-D^*),\qquad K_\mu=\frac{c+s-\mu}{cs}.
\]
The premise \(A<\mu\) puts the lower endpoint above zero in local coordinates; the maximum handles an empty section. The seam gives
\[
K_\mu-D^*<K_1-1+(s/c)U_4
=\frac sc\left(U_4-\frac{(1-z)^2}{2}\right),\tag{5}
\]
where \(K_1=(1+z^2)/(1+z)\). The withdrawn cap \(K\le5/6\) is not used.

Put \(x=t_2,y=t_3,N=L_3\). The triangle bound \((l+r)u\le1\), (4), and the axial lower bounds yield
\[
\left(\frac{2z}{1+z}+1-x\right)(1-y)<1.
\]
Define \(d_*=2-x-3y+xy,n=x+y-xy\). The certificate below gives \(1-x-2y+xy\ge0\), strictly in the actual domain because its \(y\) is below the enlarged boundary. Thus \(d_*>n>0\), \(Z=n/d_*<1\), and \(z<Z\). It suffices to prove
\[
G(N)=(1-Z)^2(3-N)-2(N-1)\ge0.
\]
As \(G\) strictly decreases in \(N<3\), this gives \(2\chi_3\le(1-Z)^2<(1-z)^2\), where \(\chi_3=(L_3-1)/(3-L_3)\). Top joining gives \(U_4<t_4<\chi_3\), so (5) is strictly negative, proving \(J=0\).

The actual domain is covered by \(y=Y(x)v,0\le v\le1\), with
\[
Y=\frac{x^2}{1-2x^2}\ (0\le x\le2/5),\quad
Y=4/15\ (2/5\le x\le17/40),\quad
Y=\frac{(1-x)^2}{6x-1-x^2}\ (17/40\le x\le1).
\]
Actual \(y<Y\). Put \(M=(1+3Y)/(1+Y)\). Projection and joining give two simultaneous bounds
\[
N\le N_b=\frac{1+y^2}{1-y^2},\quad
N\le N_m=1+\frac{(Y-y)(1-y)}{y(1+Y)}.
\]
After clearing positive denominators, use \(R=1-x-2y+xy\) and the candidates
\[
P_b=(d_*-n)^2(2-4y^2)-4y^2d_*^2,
\]
\[
P_m=(d_*-n)^2\{2v(1+Y)-(1-v)(1-Yv)\}
-2(1-v)(1-Yv)d_*^2.
\]
Nonnegativity of either candidate implies \(G\ge0\) through its corresponding valid \(N\)-bound. The cosine and sine regions each need one full rectangle; the middle region is divided into ten rational rectangles. On all 12, every Bernstein coefficient of \(R\) and of at least one candidate is nonnegative: 316 rational coefficients in all. The source checker reconstructs the polynomials, verifies complete partition-tree coverage, recomputes coefficients, and checks both \(G\)-identities; a separate nonlinear real counterexample query is UNSAT. This proves the length statement \(J=0\) without requiring prior left joining. Where physical emptiness rather than zero length is needed later, tangency must still be addressed by the strict bound in (5).

### 6. A forced interior intersection in C

R13 gives \(x+y<1\); the physical caps and right join give \(y<x\) (also checked by a full real query in the source). Put \(R_2=s_2/c_2,R_3=s_3/c_3\), so \(R_2>R_3>0\). The actual intersection \(Q_\mu=(X_\mu,Y_\mu)\) of the inward upper side of \(V_2\) and inward lower side of \(V_3\) solves
\[
s_2X_\mu-c_2Y_\mu=\mu(s_2+c_2)-1,
\quad s_3X_\mu-c_3Y_\mu=\mu(s_3-c_3)+c_3S_3.
\]
Joining and \(U_2+U_3<x+y<1\le L_3\) imply
\[
\mu-U_2<X_\mu\le\mu,\qquad0<Y_\mu<\mu-U_3.
\]
For the latter upper bound one may use \(S_3\ge2\mu-L_2>2-\sqrt2>4/15>U_3\). Points
\(Q_\mu-(\varepsilon,(R_2+R_3)\varepsilon/2)\) for small positive \(\varepsilon\) remain in the upper-right quadrant but are outside the relevant halfplanes of both corners. The free lower-left tile cannot reach that quadrant by diameter; \(V_4\)'s corner and left midpoint exclude it by a triangle of base \(\mu\) and width at least \(\mu\); \(F\) lies below the axis. Hence these points lie in \(C\), and closedness gives \(Q_\mu\in C\).

Solving the same lines formally at \(\mu=1\) defines an auxiliary point
\[
Y=\frac{2xy(N-x-y)}{(x-y)(1+xy)},\quad
X=1-x+\frac{y(1-x^2)(N-x-y)}{(x-y)(1+xy)}.\tag{6}
\]
It is necessary to prove membership in the actual \(C\), rather than change the target size. The exact relations are
\[
X_\mu-X=(\mu-1)\left(1+\frac2{R_2-R_3}\right)>0,
\quad Y_\mu-Y=(\mu-1)\left(\frac{2R_2}{R_2-R_3}-1\right)>0.
\]
The tile \(C\) contains \(0,q_R=(\mu-U_2,0),q_U=(0,\mu-U_3),Q_\mu\). The point \(Q=(X,Y)\) is in their convex quadrilateral: above the \(q_RQ_\mu\) edge because its \(V_2\)-edge intercept \(1-x<\mu-U_2\), and below the \(q_UQ_\mu\) edge because \(X\le X_\mu,Y\le Y_\mu<\mu-U_3\). Thus \(Q\in C\), and triangle areas give
\[
uX+l(u-Y)\le1,\qquad X(u+d_C)\le1.\tag{7}
\]
Here \(d_C\) is the actual lower reach. This point is forced by the actual continuous geometry, not chosen as an arbitrary finite coverage test.

<a id="R15"></a>
## R15. Continuous angle restrictions and a long-leg-free intersection in the near residual case

**Scope.** Retain the near G2 three-join family of R14. The tile \(C\) uniquely contains the center and owns no outer midpoint; \(F\) contains the bottom midpoint and has empty horizontal central section. The right, top, left hosts are \(V_2,V_3,V_4\); \(W=V_1\) is free. All duplicated midpoint memberships remain allowed. This module establishes necessary conditions, not infeasibility of the whole residual model.

### 1. Actual geometry and input bounds

Put
\[
x=t_2,\ y=t_3,\ N=L_3,\ S=S_2,\quad
\chi=\frac{N-1}{3-N},\quad z=t_W.
\]
The local \(\chi\) is not the global midpoint count \(\kappa\). R13 and R14 give
\[
0<y<x<1,\quad x+y<1,\quad y<4/15,\quad1<N<\sqrt2,
\]
\[
N+S+x+2y-y^2\le2,\quad0<\chi\le N-1.
\]
The actual bottom leg satisfies \(A<z+U_4<z+\chi\). The negative vertical section of \(W\) is empty by R14's strict projection bound. The entire \(F\) lies below the horizontal axis and fills the bottom gap. The actual reaches of \(C\) satisfy
\[
l>l_0:=\frac{2z}{1+z},\quad r>1-x,\quad u>1-y,
\]
and \(C\) contains R14's \(Q(N)\). No auxiliary leg \(D^*\) is substituted for a true leg. If \(d\) is the lower reach of \(C\) and \(v\) is \(F\)'s rooted upward reach, then \(d+v\ge\mu>1\). The bottom-gap chord has length \(g=2\mu-A-S>2-z-\chi-S\), and its actual rooted geometry gives
\[
g+v^2\le2,\quad g^2\le2,\quad gv\le1.\tag{1}
\]

### 2. Joint lower bounds for the rotations

Choose principal normal coefficients \(p\ge q\ge0\), \(p^2+q^2=1\), retaining both signs. Define
\[
\rho=1/p-1\in[0,\sqrt2-1]\subset[0,5/12),\quad
j=q/p=\sqrt{\rho(2+\rho)}.
\]
Projection gives \(l+r\le1+\rho,u+d\le1+\rho\). Hence
\[
\frac{2z}{1+z}<x+\rho,\qquad v>1-y-\rho>0.\tag{2}
\]
Using the adjacent budget in (1),
\[
g+v^2>2-z-\chi-S+(1-y-\rho)^2
\ge2+(N-1-\chi)+(x-z-2\rho)+2y\rho+\rho^2.
\]
Thus
\[
z+2\rho>x.\tag{3}
\]
If \(5\rho\le x(1-x)\), (2) gives \(z<(x+\rho)/(2-x-\rho)\), with positive denominator. But
\[
x-2\rho-\frac{x+\rho}{2-x-\rho}
=\frac{x(1-x)-\rho(5-x-2\rho)}{2-x-\rho}>0.
\]
For \(\rho=0\) this follows from \(0<x<1\); otherwise its numerator is at least \(\rho(x+2\rho)>0\). This contradicts (3), so
\[
\rho>x(1-x)/5.\tag{4}
\]
In particular \(C\) is not axis aligned.

### 3. The small-x exclusion

Both normal signs imply \(p(1-x)+q(1-y)\le1\): the alternate bound \(q(1-x)+p(1-y)\le1\) implies it since \(y<x,p\ge q\). Therefore
\[
(1-y)^2\rho(2+\rho)\le(x+\rho)^2.\tag{5}
\]
For \(0<x\le3/14\), use \(y\le Y_c=x^2/(1-2x^2)\) and define
\(F(x,\rho)=(1-Y_c)^2\rho(2+\rho)-(x+\rho)^2\). This is concave in \(\rho\), so positivity at \(\rho_0=x(1-x)/5\) and \(5/12\) suffices on the interval permitted by (4). After positive denominator clearing,
\[
\frac{(1-2x^2)^2}{x}F(x,\rho_0)
=\frac{5x^7+30x^6-227x^5+54x^4+198x^3-50x^2-45x+10}{25},
\]
\[
(1-2x^2)^2F(x,5/12)
=-\frac{576x^6+480x^5-1781x^4-480x^3+914x^2+120x-120}{144}.
\]
On \([0,3/14]\), substituting \(x=3v/14\) gives respectively eight and seven strictly positive Bernstein coefficients, with full polynomial identities checked in the source. Thus \(F>0\), contradicting (5), and
\[
x>3/14.\tag{6}
\]

### 4. The large-x exclusion

Use \(y\le Y_s=(1-x)^2/(6x-1-x^2)\). For \(x\ge1/2\), the triangle condition \((l_0+1-x)(1-y)<1\) forces \(l_0<1-y\), since otherwise the left side is at least \((2-x-y)(1-y)>1\). The last inequality follows from
\[
(1-x)(1-Y_s)-2Y_s+Y_s^2
=\frac{(1-x)(2x^4-23x^3+69x^2-37x+5)}{(6x-1-x^2)^2}>0.
\]
The quartic's Bernstein coefficients on \([1/2,1]\) are \(1,95/32,13/2,11,16\). The two rotation signs now both imply
\[
l_0+j(1-y)\le1+\rho.\tag{7}
\]
One gives this directly; the other uses \(ql_0+p(1-y)\le1\) and \(l_0<1-y\).

If \(x\ge3/4\), then \(y\le1/47,\chi\le1/2207,S\le1/7\). The diameter \(g\le\sqrt2<10/7\) and \(A<z+\chi\) yield
\[
z>\frac{6614}{15449},\quad l_0>L_*:=\frac{13228}{22063},\quad U_*:=46/47.
\]
For \(\rho\ge1/6\), (7) requires \(L_*+U_*\sqrt{\rho(2+\rho)}<1+\rho\). Yet the concave quadratic
\(U_*^2\rho(2+\rho)-(1+\rho-L_*)^2\) has positive values
\[
\frac{104489781499}{4301152462084},\qquad
\frac{5107729380395}{17204609848336}
\]
at \(\rho=1/6,5/12\), respectively. This is impossible.

For \(\rho\le1/6\), (3) gives \(l_0>2(x-2\rho)/(1+x-2\rho)\). Combining with (7), clearing positive denominators and squaring gives the necessary \(P(x,\rho)<0\), where
\[
P=47^2\left\{(46/47)^2\rho(2+\rho)(1+x-2\rho)^2
-[1-x+\rho(3+x)-2\rho^2]^2\right\}.
\]
But over \(3/4\le x\le1,x(1-x)/5\le\rho\le1/6\), substitute
\[
x=3/4+u/4,\quad \rho=x(1-x)/5+(1/6-x(1-x)/5)v,
\quad0\le u,v\le1.
\]
The degree-\((8,4)\) polynomial has 45 nonnegative Bernstein coefficients. The source verifies the original expression, substitution, coefficients and full identity. Thus \(P\ge0\), a contradiction, and
\[
x<3/4.\tag{8}
\]

### 5. A uniform central rotation bound

Equations (4), (6), (8), and concavity of \(x(1-x)\) give
\[
\rho>33/980.\tag{9}
\]
For the central half-angle \(\eta=(1-p)/q\),
\[
\eta^2=\rho/(2+\rho)>33/1993>1/64,\qquad
\eta\le\sqrt2-1<5/12.
\]
Thus the rational enlarged interval \(1/8<\eta<5/12\) is legitimate; its upper endpoint is not asserted to be physically attained.

### 6. The small-y exclusion

Suppose \(0<y\le1/32\). Set \(U=31/32,K=1/1022\); then \(\chi\le y^2/(1-2y^2)\le K\). The tile \(C\) contains \(r_0=1-x\) on the right axis and the auxiliary upper point of height \(U\), and has \(l>l_0\). Define
\[
M(\eta)=\frac{1+63\eta^2}{64\eta},\quad
R(\eta)=\frac{1+\eta^2-2\eta U}{1-\eta^2}.
\]
For normals \((p,q),(-q,p)\), projections give \(r_0\le M,l_0\le R\); for \((p,-q),(q,p)\), they give \(r_0\le R,l_0\le M\). The two bounds are exchanged, not applied twice to one side. Since \(S\le r_0/(2-r_0)\), \(z=l_0/(2-l_0)\), and \(A<z+K\), either sign yields
\[
g>G(\eta):=2-\frac{R}{2-R}-\frac{M}{2-M}-K.\tag{10}
\]
Vertical width and \(d+v>1\) give
\[
v>V(\eta):=U-\frac{2\eta^2}{1-\eta^2}>0.\tag{11}
\]
On \([1/8,5/12]\), \(0<R<1,0<M<9/20\), so the denominators are positive and \(G>0\). On \([1/8,17/50]\), the numerator of \(GV-1\), after clearing a positive denominator, is
\[
P_A=-879483024\eta^6+1884775817\eta^5-656537008\eta^4
-557283218\eta^3+222455952\eta^2-5070327\eta-490064.
\]
Its seven Bernstein coefficients are positive, so \(GV>1\), contrary to \(gv\le1\). On \([17/50,5/12]\), the corresponding numerator of \(G-99/70\) is
\[
P_D=14819616\eta^4-27309388\eta^3+14795712\eta^2-2377652\eta-23904.
\]
Its five coefficients are positive, so \(g>99/70>\sqrt2\), contradicting diameter. The denominator factors \(48\eta^2-31\eta-16\), \(63\eta^2-128\eta+1\) are convex and negative at both interval endpoints, so remain negative throughout; their product is positive. The source checker verifies rational identities, all twelve coefficients, denominator signs and separate UNSAT queries for both signs. Therefore
\[
y>1/32.\tag{12}
\]
Since \(Y_s\) decreases and \(Y_s(5/7)=1/34<1/32\), this also sharpens the final range to \(3/14<x<5/7\).

### 7. Eliminating the long-leg parameter from the forced point

R14 gives \(Q(N)=(X(N),Y(N))\in C\), with \(D=(x-y)(1+xy)>0\),
\[
X(N)=1-x+\frac{y(1-x^2)(N-x-y)}D,\quad
Y(N)=\frac{2xy(N-x-y)}D.
\]
Also \(R_0=(1-x,0)\in C\). With \(\alpha_0=(1-x-y)/(N-x-y)\in(0,1)\), the identity \(Q(1)=(1-\alpha_0)R_0+\alpha_0Q(N)\) proves
\[
Q_0=\left(1-x+\frac{y(1-x^2)(1-x-y)}{(x-y)(1+xy)},
\frac{2xy(1-x-y)}{(x-y)(1+xy)}\right)\in C.\tag{13}
\]
This is a proved convex combination in the actual \(C\); it does not set the actual \(N\) to one or change the target size. The source checks both coordinate identities and \(1-\alpha_0\).

One may further relax
\[
S\le\overline S(x,y)=\frac{1+x^2-2x(1+3y)/(1+y)}{1-x^2},\qquad
\chi\le K(y)=\frac{y^2}{1-2y^2},
\]
using right joining, \(N\ge1\), and the cosine projection cap. The three joins also imply
\[
A\le\min\left(1,z+K(y),z+
\frac{(1-z^2)y^4}{z(1-y^2)(1-3y^2)}\right).
\]
The last bound uses the actual left join, \(D^*\ge D_W\ge2\mu-L_4\), and \(sA+cD^*=1\); it does not identify auxiliary and actual legs. This five-parameter necessary-condition model in \(x,y,z,\eta,d\) still needs a full infeasibility proof. R16P supplies the extra projection premises needed when using \(Q_0\) in R16.

<a id="R15S"></a>
## R15S. Angle separation and interior displacement of the near intersection

**Scope.** Use R15's near configuration with empty horizontal section of \(F\), \(x=t_2,y=t_3\), and the actual membership \(Q_0\in C\). These are strict necessary margins, not a covering contradiction.

### 1. Separation of the two angles

From \(3/14<x<5/7\), \(y>1/32\), the right-join cascade, and both projection caps,
\[
x-y>3/20,\qquad x+y<3/4.
\]
For \(x\le5/12\), use \(y\le K_c=x^2/(1-2x^2)\). The function \(x-K_c\) is strictly concave, with endpoint values \(102/623,85/564>3/20\) at \(3/14,5/12\). The increasing \(x+K_c\) ends at \(385/564<3/4\). For \(x\ge5/12\), use \(y\le K_s=(1-x)^2/(6x-1-x^2)\). Since \(K_s\) decreases, \(x-K_s\) increases, starting at \(367/2292>3/20\). Also
\[
K_s''=\frac{8(x^3-3x+6)}{(6x-1-x^2)^3}>0.
\]
Thus \(x+K_s\) is strictly convex; its endpoint values \(1543/2292,177/238\) at \(5/12,5/7\) are below \(3/4\). In particular,
\[
(x-y)(1+xy)>3/20,\qquad1-x-y>1/4.
\]

### 2. Strict interior displacement

The coordinates of the actual contained auxiliary point obey
\[
Q_{0,x}-(1-x)>9/2000,\qquad Q_{0,y}>21/1600.
\]
Indeed \(y>1/32,x<5/7,y<4/15,1-x-y>1/4,x-y<x\), and \(1+xy<25/21\), so
\[
Q_{0,y}=\frac{2xy(1-x-y)}{(x-y)(1+xy)}
>\frac{y}{2(1+xy)}>21/1600,
\]
\[
Q_{0,x}-(1-x)
=\frac{y(1-x^2)(1-x-y)}{(x-y)(1+xy)}
>\frac{(1/32)(24/49)(1/4)}{(5/7)(25/21)}=9/2000.
\]
The source's separation-addendum checker recomputes derivatives, endpoint values and four real counterexample queries. Its result file is separate from the frozen package's count of 77 coefficients and nine queries.

<a id="R16P"></a>
## R16P. Projection premises for the near intersection

**Scope.** This premise audit applies only to R15-R16's near configuration with the horizontal central section of \(F\) empty. It neither enlarges the exclusion nor modifies the frozen certificate packages. It must be used before taking the four-point projection extrema in R16.

### 1. The auxiliary upper-point comparison

The main calculation needs \(r<X\le1\), \(0<Y<u\), where \(r=1-x,u=1-y\) are auxiliary axial coordinates and \((X,Y)=Q_0\). These \(r,u\) are exactly the \(r_0,u_0\) of R16, rather than the full actual axial reaches of \(C\). The fact that the actual \(Q_\mu\) lies below the actual upper endpoint alone does not prove \(Y<1-y\).

Set \(\sigma=x+y\in(0,1)\). Since \(4xy\le\sigma^2\) and
\[
4/27-\sigma^2(1-\sigma)
=(\sigma-2/3)^2(\sigma+1/3)\ge0,
\]
we have \(2xy(1-x-y)\le2/27\). R15S gives \((x-y)(1+xy)>3/20\), so
\[
0<Y<40/81<11/15\le1-y=u.
\]
The source also records a full continuous-angle counterexample query as UNSAT, with historical result identifier work/round16_Q0_height_premise_check.json; this extra query is outside the main package's 18 and addendum's eight queries. That attribution does not replace the explicit bound just proved.

### 2. The remaining projection and elimination premises

The inequality \(r<X\) follows from \(Q_0\)'s positive horizontal increment. For \(X\le1\), use \(X_\mu\le\mu\) and \(X_\mu-X(N)>\mu-1\); then \(X(N)<1\), and the convex combination of \(R_0,Q(N)\) defining \(Q_0\) also has \(X\le1\). This is not an assumed bound on \(C\)'s actual full horizontal projection.

Further audited premises are: \(l_0<1\) follows from \(z<1\); the actual lower reach \(d\le1\) follows from the diameter applied to the auxiliary upper point and actual lower point; the higher-order bound for \(A\) uses the actual left join and \(D^*\ge D_W\). Upper-endpoint substitution in the function \(H(z)\) is used only on its proved monotonicity interval \(z\ge1/10\); smaller \(z\) uses \(A\le z+K\) separately. The positive and negative projections for the two rotation signs are not merged or exchanged.

The extension of \(Q_0\) to a negative horizontal section of \(F\) in R16A does not automatically inherit these angle bounds. Its projection extrema require a separate audit, performed in the later route rather than presumed here.

<a id="R16"></a>
## R16. Exclusion of the near G2 three-join branch

**Scope.** In \(T_\mu\), \(\mu>1\), \(C\) is the unique center host, owns no outer midpoint, and \(F\) contains the bottom midpoint but not the center. The near hosts \(V_2,V_3,V_4\) are right, top, left; \(W=V_1\) is free. Assume right/top joined and the horizontal central section of \(F\) empty. R14 then forces left joining, the left axial seam of \(W\), and its empty negative vertical section; R13 excludes \(C\) from bottom. Duplicated corner midpoint memberships remain allowed. This module must be read with R15S and the premise audit R16P; both rotation signs are essential.

### 1. Forced points and the actual bottom gap

Put \(x=t_2,y=t_3,N=L_3,z=t_W\). The already proved ranges are
\[
3/14<x<5/7,\quad1/32<y<4/15,\quad x-y>3/20,\quad x+y<3/4,
\quad1/8<\eta\le\sqrt2-1<5/12.
\]
Here \(\eta\) is the absolute central half-angle, with
\(c=(1-\eta^2)/(1+\eta^2),s=2\eta/(1+\eta^2)\), physically \(c\ge s>0\). The same actual \(C\) contains
\[
0,(-l_0,0),(r_0,0),(0,u_0),(0,-d),Q_0=(X,Y),
\quad l_0=\frac{2z}{1+z},\ r_0=1-x,\ u_0=1-y.
\]
The first three nonzero axial points are interior lower-bound points, not actual endpoint equalities; \(d\) is the actual lower reach. With \(\Delta=(x-y)(1+xy)>0\),
\[
X=1-x+\frac{y(1-x^2)(1-x-y)}\Delta,\quad
Y=\frac{2xy(1-x-y)}\Delta.
\]
R16P proves the needed \(r_0<X\le1,0<Y<u_0\); these do not follow merely by formally setting \(N=1\) or \(\mu=1\).

Let \(v\) be \(F\)'s actual upward reach from the bottom midpoint. The negative axis gives \(d+v\ge\mu>1\). The actual bottom gap \(g=2\mu-A-S_2\), whose two endpoints belong to \(F\), obeys
\[
g^2\le2,\qquad gv\le1.\tag{1}
\]
The second inequality is twice the area of the triangle formed by those endpoints and the upper rooted endpoint.

### 2. Eliminating long legs and the bottom leg of W

Define
\[
\overline S=\frac{1+x^2-2x(1+3y)/(1+y)}{1-x^2},\quad
K=\frac{y^2}{1-2y^2},\quad b=\frac{y^4}{(1-y^2)(1-3y^2)}.
\]
Right joining and \(N\ge1\) give
\[
0\le S_2\le\overline S,\qquad
\frac{1+3y}{1+y}\le\frac{1+x^2}{1-x^2}.\tag{2}
\]
The seam gives \(A<z+\chi\), where \(\chi=(N-1)/(3-N)\le K\); therefore
\[
A\le z+K.\tag{3}
\]
For the second bound keep the actual left leg \(D_W\) distinct from the auxiliary \(D^*\). Left joining gives
\(D^*\ge D_W\ge2\mu-L_4>1-2\chi^2/(1-\chi^2)\). Substitute this into \(s_WA+c_WD^*=1\), with \(c_W/s_W=(1-z^2)/(2z)\). Since \(K^2/(1-K^2)=b\),
\[
A\le z+\frac{(1-z^2)\chi^2}{z(1-\chi^2)}
\le z+b(1/z-z).\tag{4}
\]
This remains valid when \(W\) duplicates the left midpoint.

### 3. Separate projection eliminations for both signs

For normals \((c,s),(-s,c)\), set
\[
M_+=\max(su_0,cX+sY),\quad T_+=\max(sr_0,sX-cY).
\]
The four points \(0,(r_0,0),(0,u_0),Q_0\) have projection ranges \([0,M_+]\) and \([-T_+,cu_0]\). Thus
\[
M_+\le1,\quad cu_0+T_+\le1,\tag{5+}
\]
\[
l_0\le L_+:=\min\left(1,\frac{1-M_+}c,\frac{1-T_+}s\right),\tag{6+}
\]
\[
d\le D_+:=\min\left(1,\frac{1-M_+}s,\frac1c-u_0\right).\tag{7+}
\]
These retain only necessary pairwise widths; dropping additional left/lower mutual constraints enlarges the domain.

For normals \((c,-s),(s,c)\), set
\[
T_-=\max(cr_0,cX-sY),\quad M_-=\max(cu_0,sX+cY).
\]
The ranges are \([-su_0,T_-]\) and \([0,M_-]\), giving
\[
T_-+su_0\le1,\quad M_-\le1,\tag{5-}
\]
\[
l_0\le L_-:=\min\left(1,\frac{1-T_-}c,\frac{1-M_-}s\right),\tag{6-}
\]
\[
d\le D_-:=\min\left(1,\frac1s-u_0,\frac{1-M_-}c\right).\tag{7-}
\]
The cap one in (6) uses \(l_0<1\), not the actual left reach. In (7), \(d\le1\) follows independently from \(u_0\ge11/15\) and \(u_0+d\le\sqrt2\), since \(26/15>\sqrt2\). The source's five exact real queries check these implications, \(b<1/101\), and the monotonicity below, all as UNSAT counterexample queries.

### 4. A three-parameter diameter or area contradiction

For either sign let \(L=L_\pm>0,Z=L/(2-L)\in(0,1]\). Then \(z\le Z\). The function \(H(z)=z+b(1/z-z)\) is not increasing on all \((0,1]\). Use \(\varepsilon=1/10\). Since \(0\le b\le256/36993<1/101\), for \(z\ge\varepsilon\), \(H'=1-b-b/z^2\ge1-101b>0\). Below \(\varepsilon\), use (3). Consequently
\[
A\le\mathcal A(Z,y)=\min(1,J(Z,y)),
\quad J=\begin{cases}Z+K,&0<Z\le\varepsilon,\\
\min\{Z+K,\max(\varepsilon+K,H(Z))\},&\varepsilon<Z\le1.
\end{cases}\tag{8}
\]
This bound is continuous at \(\varepsilon\) and nondecreasing in \(Z\). Put \(D=D_\pm\),
\[
G=2-\mathcal A(Z,y)-\overline S(x,y),\qquad V=\max(0,1-D).
\]
Then actual geometry gives \(g>G,v\ge V\). On a region with \(G>0\), either
\[
G^2>2\quad\hbox{or}\quad GV>1\tag{9}
\]
contradicts (1). Only \(x,y,\eta\) remain; \(z,d,N\) and the rotation of \(F\) have been eliminated by necessary bounds.

### 5. Exact interval certificate on the full continuous region

The rational root box is
\[
[3/14,5/7]\times[1/32,4/15]\times[1/8,5/12],
\]
retaining \(x-y\ge3/20,x+y\le3/4,\eta^2+2\eta\le1\), (2), \(\overline S\ge0,X\le1,Y\le u_0\), and (5) for the respective sign. Actual parameters satisfy stricter bounds, so exclusion of this closed enlargement suffices.

The generator encloses root endpoints outward on the \(2^{-60}\) grid and uses integer arithmetic and outward rounding. Each binary node specifies a coordinate; its children cover exactly the parent box, including their common face. Each leaf excludes an input condition, a necessary central width, or one of (9). The source records 497 nodes/249 leaves/depth 14 for the positive sign: 85 width exclusions, 142 diameter/area exclusions, 22 angle or long-leg exclusions. The negative sign has 1847 nodes/924 leaves/depth 17: 380 width exclusions, 484 diameter/area exclusions, 60 angle, long-leg or \(X\le1\) exclusions. The two trees total 2344 bytes. Their SHA-256 values are

- `C1.tree`: `15a48967195bd78183b01a4c876f6dfc6d76ab6e91c48e36c8c7a7453e9e662a`.
- `C-1.tree`: `20600e68ff4c9c069fb69b72e5944209228af3504e64e691087c5ca3f23becf2`.

The independent checker rebuilds every bound with exact fractions, without calling the generator's interval routines. It checks root enclosure, every split, all leaves, and absence of missing or surplus nodes. Each leaf has a strict exclusion margin exceeding \(1/100000\), with exact values in the result file. For the interval upper bound on \(\overline S\), writing \(L_{\min}=(1+3y)/(1+y)\ge1\),
\[
\partial_x\overline S=-\frac{2\{L_{\min}(1+x^2)-2x\}}{(1-x^2)^2}<0,
\quad\partial_y\overline S=-\frac{4x}{(1-x^2)(1+y)^2}<0.
\]
Thus its maximum on a box is at the lower-left \((x,y)\) endpoint. The coefficient \(c\) decreases and \(s\) increases in \(\eta\); other expressions use outward interval bounds. Division occurs only after proving a positive lower denominator bound. These 1173 boxes cover continuous parameter regions, rather than 1173 sample placements or target points. The source's floating optimization served only to discover the route and is not part of the final certificate argument.

<a id="R16A"></a>
## R16A. Gap ownership and intersections with a nonempty near horizontal section

**Scope.** Use \(T_\mu\), \(\mu>1\), near hosts \(V_2,V_3,V_4\) at right, top, left, and free lower-left \(W\). The unique center tile \(C\) owns no outer midpoint. The actual \(F\) contains the bottom midpoint \(B=(0,-\mu)\), but neither center nor other midpoint. Assume right/top joined, a nonempty left gap, and nonempty horizontal central section of \(F\). These hypotheses suffice independently of R16's interval certificate. Neither residual type below is excluded here.

### 1. Two residual types and their limits

By convexity, \(F\)'s horizontal section lies in one open half-axis, including the case of a single tangent point. If negative, the left gap belongs wholly to \(F\), and \(C\) contains the right/upper axial inner endpoints and \(Q_\mu,Q(N),Q_0\). If positive, the left gap belongs wholly to \(C\), and the right axial inner endpoint belongs to \(F\). Extending the point \(Q_0\) does not transfer R15's stronger angle restrictions, which required an empty \(F\) section.

### 2. Horizontal position determines forbidden contacts

If \(F\) contains \(B,P=(-\mu,p)\), \(-\mu\le p\le\mu\), and \((t,0)\), \(t>0\), the triangle's doubled area is \(\mu^2+t(\mu+p)\ge\mu^2>1\). Thus a positive horizontal section forbids any target left-edge contact.

If \(F\) instead contains \(B,H=(-t,0)\), \(t>0\), and a first-quadrant point \(P=(X,Y)\), \(X,Y>0\), put \(E=1+X/t+Y/\mu\). The positive weights
\[
\alpha_P=1/E,\quad\alpha_H=(X/t)/E,\quad\alpha_B=(Y/\mu)/E
\]
sum to one and satisfy \(\alpha_BB+\alpha_HH+\alpha_PP=0\), contrary to \(0\notin F\). Positive-axis contacts are excluded by segment convexity. Hence a negative horizontal section makes \(F\) avoid the entire closed upper-right quadrant. It need not lie wholly below the horizontal line.

### 3. Complete ownership of the left gap

The left gap is between the actual top of \(W\)'s left leg and the lower endpoint of \(V_4\)'s long leg. Since \(L_4\ge\mu\), it lies in the lower half-edge. No corner covers its interior. In the positive type, Section 2 excludes \(F\), so the whole open gap belongs to \(C\), and closedness supplies both endpoints.

In the negative type, limits from outside the short corner sections force
\[
q_R=(\mu-U_2,0)\in C,\quad q_U=(0,\mu-U_3)\in C.
\]
The adjacent right-join budget gives \(x+y<1\), \(U_2<x,U_3<y\), so the actual right and upper reaches obey \(r+u\ge2\mu-U_2-U_3>1\). The two-sign outer-point lemma of R17 says a unit tile containing \((r,0),(0,u),(-\mu,-e)\), \(e\ge0\), must have \(r+u<1\). Therefore \(C\) misses the gap and its whole interval, including endpoints, belongs to \(F\). No empty \(W\) vertical section or forced left seam is used.

In the positive type, its left-gap membership gives \(r+u<1\) for \(C\). If \(q_R\) also belonged to \(C\), then \(q_R,q_U\) would give \(r+u>1\). Thus \(q_R\notin C\), and actual coverage forces \(q_R\in F\).

### 4. Extending the forced intersection in the negative type

Here \(q_R,q_U\in C\) and \(F\) avoids the upper-right quadrant. With \(R_2=s_2/c_2>R_3=s_3/c_3>0\), the same actual inward sides satisfy
\[
s_2X_\mu-c_2Y_\mu=\mu(s_2+c_2)-1,\quad
s_3X_\mu-c_3Y_\mu=\mu(s_3-c_3)+c_3S_3,
\]
and \(\mu-U_2<X_\mu\le\mu,0<Y_\mu<\mu-U_3\). Approaching their intersection through the inward wedge avoids \(V_2,V_3\); diameter excludes \(W\), the triangle bound excludes \(V_4\), and Section 2 excludes \(F\). Hence closedness gives \(Q_\mu\in C\). R14's coordinate monotonicity and convex-quadrilateral argument then give
\[
Q(N)=\left(1-x+\frac{y(1-x^2)(N-x-y)}{(x-y)(1+xy)},
\frac{2xy(N-x-y)}{(x-y)(1+xy)}\right)\in C.
\]
With \(R_0=(1-x,0)\in C\), the convex combination
\[
Q_0=(1-\alpha_0)R_0+\alpha_0Q(N),\quad
\alpha_0=\frac{1-x-y}{N-x-y}\in(0,1)
\]
proves \(Q_0=Q(1)\in C\). It does not set actual \(N\) or \(\mu\) to one and does not assign this point to \(C\) in the positive type. Projection extrema in this extended setting require their own premise audit; R16P's empty-section bounds cannot be imported automatically.

<a id="R17"></a>
## R17. Excluding the negative horizontal branch by overlap and projections

**Scope.** In the near G2 representative, \(V_2,V_3,V_4\) host the right, top, left midpoints, and \(W\) contains the lower-left corner. The unique center tile \(C\) owns no outer midpoint; \(F\) contains \(B=(0,-\mu)\), not the center. Let \(F\) meet the negative horizontal half-axis, possibly only tangentially. Assume right/top joined and, after the anchored normalizations, a true left gap remains. Membership of \(W\) at \(B\) is allowed and will be forced, not excluded.

### 1. Actual sections and corner inputs

Normalize the three anchored corners by target-relative domination, keeping the other tiles fixed. For \(t_i\in(0,1)\),
\[
\mu\le L_i\le\sqrt2,\quad L_i(1-t_i^2)\le1+t_i^2,\quad
2t_iL_i\le1+t_i^2,
\]
\[
S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2}<g(t_i),\quad U_i<t_i.\tag{1}
\]
The actual joins are
\[
L_2+S_3\ge2\mu,\quad L_3+S_4\ge2\mu.\tag{2}
\]
Put \(x=t_2,y=t_3,z=t_4\). Keep the original actual bottom/left legs \(A,D\) of \(W\), with
\[
g_L=2\mu-L_4-D>0.\tag{3}
\]
The parallel budget \(B(\mu)<1\) is used only when both full sections are nonempty, including tangent sections.

### 2. Two hand-checkable lemmas

For an anchored corner define the local angle cap \(\chi=(L-1)/(3-L)\). Monotonicity in \(L\le\sqrt2\) gives
\[
0<\chi\le\frac{\sqrt2-1}{3-\sqrt2}<4/15,
\quad \chi<\min(t,1-t).\tag{4}
\]
The rational comparison is \(19\sqrt2<27\), or \(722<729\). For \(t\le1/3\), the cosine cap gives \(\chi\le t^2/(1-2t^2)<t\), since \(2t^2+t-1<0\), and \(\chi<4/15<1-t\). For \(t\ge1/3\), \(\chi<4/15<t\), while the positive-denominator sine cap gives \(\chi\le(1-t)^2/(6t-1-t^2)<1-t\): this is \(t^2-7t+2<0\), decreasing from \(-2/9\). Joining gives
\[
L_i+g(t_j)>2,\qquad t_j<\chi_i.\tag{5}
\]
In particular \(y<\min(x,1-x)\), without R13's polynomial certificate.

The second lemma states that a unit tile containing \((r,0),(0,u),(-\mu,-e)\), \(r,u,e\ge0,\mu>1\), must satisfy
\[
r+u<1.\tag{6}
\]
Choose normals \((c,\varepsilon s),(-\varepsilon s,c)\), \(c\ge s\ge0,c^2+s^2=1\). Axis alignment is impossible from horizontal span \(\mu+r>1\). For \(\varepsilon=1\), widths give \(c(\mu+r)+se\le1,c\mu+s(e+u)\le1\), so
\[
r+u<(1-c)(1/c+1/s)=\frac{s(c+s)}{c(1+c)}<1,
\]
using \(s\le c,s<1\). For \(\varepsilon=-1\), use \(c(\mu+r)-se\le1,s\mu+c(e+u)\le1\). Multiplying by \(c,s\) and adding eliminates \(e\): \(\mu+c^2r+csu\le c+s\). Thus
\(cs(r+u)\le c^2r+csu<c+s-1\le cs\), where the last comparison is \((1-c)(1-s)\ge0\). The center need not additionally belong to this tile.

### 3. Ownership of the left gap and absence of C from bottom

The negative horizontal section of \(F\) and convexity exclude its contact with the right or upper axial inner endpoints. Limits from outside the short corner sections therefore give \(q_R=(\mu-U_2,0),q_U=(0,\mu-U_3)\in C\). For the actual reaches,
\[
r>1-x,\quad u>1-y,\quad r+u>2-x-y>1.\tag{7}
\]
The left gap lies in the lower half-edge. Equation (6) prevents \(C\) from touching it, so the entire interval, including endpoints, belongs to \(F\). In particular
\[
P=(-\mu,\mu-L_4)\in F.\tag{8}
\]
Since \(y<4/15\), \(q_U\)'s vertical distance to any bottom point exceeds \(2-y>26/15>\sqrt2\); hence \(C\) misses bottom. Any bottom corner gap must also belong entirely to \(F\).

### 4. Two gap endpoints force a bottom join

Top joining gives \(z<\chi_3\le K(y)=y^2/(1-2y^2)\). Put
\[
\delta=\frac{2y^4}{(1-y^2)(1-3y^2)}.
\]
Then
\[
L_4<1+\delta,\qquad0<\delta<y^2<y<x.\tag{9}
\]
Indeed \(\delta<y^2\) follows from \(1-6y^2+3y^4>0\), using \(y<4/15\). Also
\[
S_2<g(x)<1-x<1-\delta.\tag{10}
\]
A bottom gap would put \(R_B=(\mu-S_2,-\mu)\in F\). But
\[
|P-R_B|^2=(2\mu-S_2)^2+(2\mu-L_4)^2
>(1+\delta)^2+(1-\delta)^2\ge2,
\]
contrary to diameter. Therefore
\[
A+S_2\ge2\mu.\tag{11}
\]
Since \(S_2<1<\mu\), \(A>\mu\) and the original \(W\) contains \(B\).

### 5. Dominating parameters without changing the recorded left gap

Normalize \(W\) as bottom host only to obtain upper-bound parameters \(L_1\ge A,S_1\ge D,U_1\ge J\), with half-angle \(w\). Here \(J\) is the original rooted reach from \(B\). The original gap (3) continues to use the original \(D\), even if the dominating tile fills it; none of these inequalities asserts persistence of that gap in the replaced cover. Equations (4), (5), (11) give
\[
x<\chi_1<\min(w,1-w),\qquad x<4/15<1/3.\tag{12}
\]
The original right join yields \(y<x^2/(1-2x^2)<6x^2/5\), because \(1-2x^2>193/225>5/6\). Thus
\[
y+\delta<y+y^2<\frac65x^2+\frac{36}{25}x^4
<\frac{34}{75}x<x/2.\tag{13}
\]
The intermediate estimate uses \(x<1/3\).

### 6. Actual overlap at the same bottom midpoint

Let \(v\) be \(F\)'s rooted upward reach from \(B\). Its left and central vertical sections are nonempty, so \(v+g_L\le B<1\). Equations (3), (9) give
\[
v<1-g_L<D+\delta\le S_1+\delta.\tag{14}
\]
Both original \(W\) and \(F\) contain \(B\) and avoid the center. Their negative vertical sections start at this same point, so their union length is exactly \(\max(J,v)\), not \(J+v\). No other corner meets that open half-axis. Hence \(d+\max(J,v)\ge\mu>1\). Using \(J\le U_1<w,S_1<g(w)\),
\[
d>\min(1-U_1,1-S_1-\delta)
>\min(1-w,2w/(1+w)-\delta)>x-\delta.\tag{15}
\]

### 7. Projection contradiction for both central rotation signs

Write \(\rho=1/c-1\in[0,\sqrt2-1]\subset[0,5/12)\) for principal coefficients \(c\ge s\ge0\). The vertical chord cap \(u+d\le1+\rho\) and (7) give \(d<y+\rho\). Thus
\[
\rho>x-y-\delta>x/2.\tag{16}
\]
One rotation gives \(cr+su\le1\); the other gives \(sr+cu\le1\), which implies the same weaker auxiliary inequality because \(x>y,c\ge s\). Consequently
\[
(1-y)^2\rho(2+\rho)\le(x+\rho)^2.\tag{17}
\]
For \(0<x<1/3,y<x/2,x/2<\rho<5/12\), this is impossible. The concave quadratic
\(F_x(\rho)=(1-x/2)^2\rho(2+\rho)-(x+\rho)^2\) has positive endpoint values
\[
F_x(x/2)=x(1-3x+x^3/16)>0,
\quad F_x(5/12)=5/6-265x/144-431x^2/576>709/5184>0.
\]
The latter decreases in \(x\ge0\), reaching the displayed lower value at \(x=1/3\). Since \((1-y)^2>(1-x/2)^2\), the left side of (17) minus the right side is strictly positive. This excludes the stated negative-horizontal, left-gap branch.

<a id="R18"></a>
## R18. Excluding the positive horizontal type and classifying the remaining near gaps

**Scope.** Use the near G2 family with right, top, left hosts \(V_2,V_3,V_4\), free lower-left \(W\), unique center tile \(C\) owning no outer midpoint, and bottom-midpoint tile \(F\) avoiding the center. Assume right/top joined and a positive nonempty horizontal central section of \(F\), including possible tangency. All endpoints and legs below belong to the same actual tiles; \(W\) is initially unchanged.

### 1. Corner inputs and the residual left gap

The anchored parameters obey \(\mu\le L_i\le\sqrt2\), \(L_i(1-t_i^2)\le1+t_i^2\), \(2t_iL_i\le1+t_i^2\), \(S_i<g(t_i),U_i<t_i\). Put \(x=t_2,y=t_3,z=t_4\). The joins are
\[
L_2+S_3\ge2\mu,\qquad L_3+S_4\ge2\mu.\tag{1}
\]
R17's local angle cap \(\chi_i=(L_i-1)/(3-L_i)\) gives
\[
0<y<\min(x,1-x),\qquad y<4/15.\tag{2}
\]
Top joining yields \(z<\chi_3\le y^2/(1-2y^2)\), so, with
\(\delta=2y^4/((1-y^2)(1-3y^2))\),
\[
L_4<1+\delta,\quad0<\delta<y^2.\tag{3}
\]
If left were joined, R13's three-join/nonempty-horizontal exclusion would apply. Thus retain the actual left gap \(g_L=2\mu-L_4-D>0\), with actual \(W\) left/bottom legs \(D,A\).

### 2. Forced left and upper points of C

A tile \(F\) containing \(B=(0,-\mu)\), a left-edge point \((-\mu,p)\), and a positive horizontal point \((t,0)\) would contain a triangle of doubled area \(\mu^2+t(\mu+p)>1\). Thus \(F\) misses the entire target left edge. The whole left gap belongs to \(C\), including both endpoints. In particular
\[
P=(-\mu,-e)\in C,\qquad0\le e=L_4-\mu<\delta.\tag{4}
\]
Convexity excludes \(F\) from the positive vertical axis, and the corner roles force \(q_U=(0,\mu-U_3)\in C\). Hence
\[
u\ge\mu-U_3>1-y.\tag{5}
\]
Its vertical distance to bottom exceeds \(2-y>26/15>\sqrt2\), so \(C\) misses bottom completely.

### 3. The actual right reach of C is smaller than y squared

Choose principal normals \((c,\varepsilon s),(-\varepsilon s,c)\), \(c\ge s\ge0,c^2+s^2=1\). Axis alignment is excluded by \(P\) and the center. For \(\varepsilon=1\), \(c\mu+s(e+u)\le1\) would give \(c+s(1-y)<1\), yet
\[
c+s(1-y)-1=s\left(1-y-\frac{s}{1+c}\right)>0,
\]
since \(y<1/2\) and \(s/(1+c)\le c/(1+c)<1/2\). Thus only \(\varepsilon=-1\) remains. Its projection gives \(s\mu+c(e+u)\le1\), hence \(s+c(1-y)<1\). For the central half-angle \(\eta=(1-c)/s\), this is
\[
(1-\eta)(\eta(2-y)-y)<0,\qquad\eta<\frac y{2-y}.\tag{6}
\]
Set \(\rho=1/c-1\) and the local slope \(j=s/c\). Monotonicity in \(\eta\) gives
\[
\rho<\frac{y^2}{2(1-y)},\qquad j<\frac{y(2-y)}{2(1-y)}.\tag{7}
\]
The actual right reach \(r\) satisfies \(c(\mu+r)-se\le1\), so
\[
r\le\rho-(\mu-1)+je<\rho+j\delta
<\frac{y^2(1+2y-y^2)}{2(1-y)}<y^2.\tag{8}
\]
The last step is \(1-4y+y^2>0\), decreasing on \([0,4/15]\) to \(1/225\). This bounds the right reach only, not the full horizontal chord.

### 4. Bottom joining is impossible

If \(A+S_2\ge2\mu\), then \(A>\mu\), so the original \(W\) contains \(B\). Its dominating bottom-host parameters satisfy \(L_1\ge A,S_1\ge D\), with half-angle \(w\). The bottom join gives \(x<\chi_1<\min(w,1-w)\), \(x<4/15\), hence
\[
D\le S_1<g(w)<1-w<1-x.\tag{9}
\]
Retain the original left gap throughout this bound. Both \(C\)'s left and central vertical sections are nonempty; with lower reach \(d\), \(g_L+u+d\le B<1\). Thus
\[
D=2\mu-L_4-g_L>1-\delta-y+d\ge1-\delta-y.\tag{10}
\]
The hypothetical bottom join gives \(x<4/15<1/3\); the right cascade yields \(y<6x^2/5\), and
\(y+\delta<y+y^2<6x^2/5+36x^4/25<34x/75<x/2\). Equation (10) now gives \(D>1-x/2\), contrary to (9). Therefore
\[
A+S_2<2\mu.\tag{11}
\]

### 5. Two actual nonempty sections of F exceed their parallel budget

Only \(F\) fills the bottom gap. Closedness gives \(R_B=(b,-\mu)\in F\), where \(b=\mu-S_2\); since \(B\in F\), its full bottom chord is at least \(b\), and
\[
b>1-S_2>2x/(1+x).\tag{12}
\]
Let \(q_R=(r_0,0)\), \(r_0=\mu-U_2>1-x\). Equations (2), (8) give \(r<y^2<y<1-x<r_0\). Other corners cannot cover the intervening positive horizontal interval. Thus \(C,F\) must actually join, and the target horizontal section \([\alpha,\beta]\) of \(F\) satisfies
\[
0<\alpha\le r<y^2,\qquad\beta\ge r_0.\tag{13}
\]
The second condition follows from limits just outside the corner's short section even though \(q_R\) itself is also in \(V_2\). It forces positive length and therefore includes the originally tangent possibility.

Both bottom and horizontal full sections of \(F\) are nonempty at distance \(\mu\). Hence
\[
b+(\beta-\alpha)\le B<1,\qquad b+r_0-\alpha<1.\tag{14}
\]
But
\[
b+r_0-\alpha>\frac{2x}{1+x}+1-x-y^2
=1+\frac{x(1-x)}{1+x}-y^2.\tag{15}
\]
For \(m=\min(x,1-x)>0\), (2) gives \(y^2<(4/15)m<m/3\), while \(x(1-x)/(1+x)\ge m/3\): below \(1/2\), use \((1-x)/(1+x)\ge1/3\); above it, use \(x/(1+x)\ge1/3\). Thus (15) exceeds one, contradicting (14).

### 6. Combined conclusion and certificate limits

Left joining was excluded by R13; Sections 2-5 exclude a left gap in the positive type. R17 excludes the negative type; R14 and R16 exclude the empty type. These exhaust the horizontal central sections of \(F\), so the near right/top-joined branch is excluded for every \(\mu>1\).

The source records nine UNSAT scalar counterexample queries (seven nonlinear, two linear), seven symbolic identities, and three exact constant comparisons in its positive-projection checker. They do not replace the endpoint ownership or section-nonemptiness arguments. A draft relaxation replacing the actual strict condition \(c+s(1-y)<1\) by a weak one admitted \(c=1,s=0,y=1/4\); this is a counterexample to that relaxed query, not a covering or a counterexample to the strict argument. No global bound follows from this module alone.

### 7. Direct classification of the remaining near configurations

Every surviving near cover must have exactly one corner gap among right and top, wholly belonging to \(C\); the other edge is joined. A right gap lies at \((\mu,e)\), \(e>0\), and a top gap at \((-t,\mu)\), \(t>0\). Their distances from \(B\) prevent \(F\) from covering them. Both gaps together with the center would give a triangle in \(C\) of doubled area \(\mu^2+et>1\), impossible.

If \(C\) fills a right gap, it misses the left edge by diameter. If it fills a top-left gap, any lower-half left-edge point would form with that point and the center a triangle of doubled area \(\mu^2+te'>1\). The left gap lies in this lower half; if present, it therefore belongs wholly to \(F\). This classifies two residual representatives but does not exclude either.

<a id="R19"></a>
## R19. Top-gap endpoints replace the old angle cascade

**Scope.** In the near G2 family, \(V_2,V_3,V_4\) host the right, top, left midpoints; \(W=V_1\) is free. The unique center tile \(C\) owns no midpoint and \(F\) contains \(B=(0,-\mu)\), neither center nor another midpoint. Assume right joined and a top corner gap remains after individual dominating normalizations of the three hosts. If that gap disappears, the resulting family is excluded by R18. If a left gap disappears, use the left-joined branch below. Duplicated corner midpoint memberships are allowed.

### 1. Actual top endpoint and left-gap ownership

Put \(x=t_2,y=t_3,z=t_4\). The anchored inequalities are
\[
\mu\le L_i\le\sqrt2,\quad L_i(1-t_i^2)\le1+t_i^2,\quad2t_iL_i\le1+t_i^2,
\]
\[
S_i=\frac{1+t_i^2-2t_iL_i}{1-t_i^2}<g(t_i),\quad U_i<t_i,\quad L_i+S_i+U_i<2.\tag{1}
\]
Right joining \(L_2+S_3\ge2\mu\) and R17's local cap \(\chi_i=(L_i-1)/(3-L_i)\) give
\[
y<\chi_2<\min(x,1-x),\quad\chi_i<\min(t_i,1-t_i),\quad y<4/15.\tag{2}
\]
This does not require a top join. The top gap \(g_T=2\mu-L_3-S_4>0\) belongs wholly to \(C\), since \(F\) cannot reach top from \(B\). Its left endpoint is
\[
P_T=(-T,\mu)\in C,\qquad T=\mu-S_4>0.\tag{3}
\]
If the original \(W\), with actual legs \(A,D\), leaves \(g_L=2\mu-L_4-D>0\), its upper endpoint is \(P_L=(-\mu,-e)\), \(e=L_4-\mu\ge0\). The center, \(P_T\), and any lower-half left-edge point have doubled triangle area \(\mu^2+Te'>1\). Thus \(C\) misses the left gap, which belongs wholly, endpoints included, to \(F\). A positive horizontal point of \(F\) would form with \(P_L,B\) a triangle of doubled area \(\mu^2+p(\mu-e)>1\), since \(e<\mu\). Therefore a left gap forbids every positive horizontal contact of \(F\), while allowing its section to be empty.

### 2. New angle restrictions from the top endpoint

Assume \(g_L>0\). Since \(F\) has no positive horizontal point and cannot meet the positive vertical axis, limits outside the short corner sections force \(q_R=(\mu-U_2,0),q_U=(0,\mu-U_3)\in C\). Thus
\[
r>1-x,\qquad u>1-y.\tag{4}
\]
The diameter between \(P_T\) and \((r,0)\) gives \((r+T)^2+\mu^2\le2\), hence \(r+T<1\) and \(T<x\). Since \(T>2z/(1+z)\),
\[
z<\frac x{2-x}.\tag{5}
\]
Put \(\Delta(x)=x^2/(2(1-x))\). The cosine cap now gives
\[
L_4<1+\Delta.\tag{6}
\]
Neither \(z<\chi_3\) nor the old fourth-order small quantity is available: top is not joined.

### 3. Two outer-gap endpoints force bottom joining

The tile \(C\) containing \(P_T\) misses bottom by vertical distance \(2\mu>\sqrt2\). A bottom corner gap would belong wholly to \(F\), putting \(R_B=(\mu-S_2,-\mu)\) there with \(P_L\). Horizontal span gives \(2\mu-S_2\le\sqrt2<3/2\), while \(S_2<g(x)\) gives \(2\mu-S_2>1+2x/(1+x)\), so \(x<1/3\). On this interval \(\Delta<x/4<1\), and \(1-S_2>2x/(1+x)>3x/2>\Delta\). Hence
\[
|P_L-R_B|^2=(2\mu-S_2)^2+(2\mu-L_4)^2
>(1+\Delta)^2+(1-\Delta)^2\ge2,
\]
impossible. Therefore
\[
A+S_2\ge2\mu.\tag{7}
\]
In particular the original \(W\) contains \(B\), since \(A>\mu\).

### 4. Joint small quantities after the bottom join

Use only dominating parameter bounds for \(W\), denoted \(L_1\ge A,S_1\ge D,U_1\ge J\), with angle \(w\). Here \(J\) is the original rooted upward reach from \(B\). The original gap retains the original \(D\), even if the dominating tile fills it. The bottom join gives
\[
x<\chi_1<\min(w,1-w),\qquad x<4/15.\tag{8}
\]
The current right join implies \(y<\chi_2\le x^2/(1-2x^2)<7x^2/6\), using \(225/193<7/6\); also \(\Delta<15x^2/22\). Thus
\[
y+\Delta<\frac{61}{33}x^2<\frac{244}{495}x<x/2.\tag{9}
\]
These are consequences of the actual top endpoint and bottom join, not of a nonexistent top join.

### 5. The common bottom origin requires a maximum

Let \(v\) be \(F\)'s actual rooted upward reach. Its left gap section and central vertical section are nonempty, so \(v+g_L\le B(\mu)<1\). By (6),
\[
v<1-g_L<D+\Delta\le S_1+\Delta.\tag{10}
\]
The negative vertical sections of the original \(W,F\) both start at \(B\), so their union length is exactly \(\max(J,v)\). Other corners miss that open half-axis; \(d+\max(J,v)\ge\mu>1\). Therefore
\[
d>\min(1-U_1,1-S_1-\Delta)
>\min(1-w,2w/(1+w)-\Delta)>x-\Delta.\tag{11}
\]
Adding \(J+v\) instead would lose the actual overlap and is not used.

### 6. Both central rotation signs contradict projections

Write principal normals \((c,\varepsilon s),(-\varepsilon s,c)\), \(c\ge s\ge0,c^2+s^2=1\), and \(\rho=1/c-1\in[0,\sqrt2-1]\subset[0,5/12)\). Vertical chord length gives \(u+d\le1+\rho\); hence \(d<y+\rho\). Equations (9), (11) imply
\[
\rho>x-y-\Delta>x/2.\tag{12}
\]
One sign gives \(cr+su\le1\), and the other \(sr+cu\le1\); because \(x>y,c\ge s\), both imply \(c(1-x)+s(1-y)\le1\). Thus
\[
(1-y)^2\rho(2+\rho)\le(x+\rho)^2.\tag{13}
\]
For \(0<x<1/3,y<x/2,x/2<\rho<5/12\), the concave quadratic
\(f_x(\rho)=(1-x/2)^2\rho(2+\rho)-(x+\rho)^2\) is positive: its endpoint values are
\[
f_x(x/2)=x(1-3x+x^3/16)>0,
\quad f_x(5/12)=5/6-265x/144-431x^2/576>709/5184>0.
\]
Since \((1-y)^2>(1-x/2)^2\), this contradicts (13). The whole top-gap/right-joined/left-gap branch is excluded, whether \(F\)'s horizontal section is negative or empty.

### 7. Left joining forces an empty F horizontal section

Now let left and right be joined, with the top gap belonging to \(C\). If \(F\)'s horizontal section is nonempty, including tangency, the \(C\) top/horizontal and \(F\) bottom/horizontal parallel budgets are both valid. Four corner grid budgets contribute at most eight; extra side-edge sections are redundant, \(C\) misses bottom, \(F\) misses top, and the central vertical noncorner union has length at most \(2\mu\). Thus
\[
12\mu\le8+2B(\mu)+2\mu<12\mu.
\]
This is R13's grid argument under the present hypotheses. The only residual near top-gap family has left/right joined and \(F\)'s horizontal section empty.

### 8. Necessary conditions for the remaining family

These conditions do not yet exclude that family. Keep the original \(W\) grid lengths \(A,D,H,J\), allowing floating, tangent or empty central sections. R13's audited adjacent-corner certificate at the right join gives
\[
L_3+S_2+U_2+2y-y^2<2.\tag{14}
\]
Write \(h_C\) for the full horizontal length of \(C\). Since \(F\)'s section is empty,
\[
h_C+H+U_2+U_4\ge2\mu,\qquad h_C+g_T\le B<1.
\]
Left joining, \(V_4\)'s strict corner budget, and \(A+D+H+J\le2\) yield
\[
\begin{aligned}
h_C+g_T&\ge4\mu-L_3-S_4-U_2-U_4-H\\
&>6\mu-2-L_3-U_2-D-H\\
&\ge6\mu-4-L_3-U_2+A+J\\
&>6(\mu-1)+A+S_2+J+2y-y^2.
\end{aligned}
\]
Consequently
\[
A+S_2+J+2y-y^2<B-6(\mu-1)<1.\tag{15}
\]
Bottom has a genuine gap wholly belonging to \(F\), and \(W\) does not contain \(B\). Its full bottom chord \(b\) satisfies
\[
b\ge g_B=2\mu-A-S_2>2\mu-B+6(\mu-1)+J+2y-y^2
>1+J+2y-y^2.\tag{16}
\]
The gap straddles \(B\), and the rooted three-ray inequality gives
\[
v^2+J+2y-y^2<B-8(\mu-1)<1.\tag{17}
\]
Now \(J\) may float because \(W\) does not contain \(B\); the maximum-union formula of Section 5 is unavailable. The empty \(F\) section still forces \(q_R\in C\), so (5), (6) remain valid. If \(J>0\), both parallel sections of \(W\) are nonempty and \(D+J\le B\); left joining gives \(J<\Delta\). This also holds when \(J=0\). A final contradiction still requires the actual top endpoint, joint \(C,F\) projections, and the position of the floating section; the long bottom chord alone is not an infeasibility proof.

<a id="R26"></a>
## R26. Closing the entire near G2 top-gap representative

**Scope.** The near hosts \(V_2,V_3,V_4\) are right, top, left. Keep the original lower-left free tile \(W\), center tile \(C\), and bottom-midpoint tile \(F\) fixed. Here \(C\) uniquely contains the center and owns no outer midpoint. After the individual anchored dominations, a vanished top gap enters the already excluded right/top-joined branch. R19 reduces a surviving top gap to right/left joined and an empty horizontal central section of \(F\). This module treats exactly that residual family.

### 1. Actual points and common parameters

Put \(x=t_2,y=t_3,z=t_4\). With the global slope notation \(\lambda(t)=2t/(1-t^2)\), define \(g(t)=(1-t)/(1+t),\delta(t)=2t^2/(1-t^2),q(t)=t/(2-t)\). The anchored parameters satisfy
\[
L_i\ge\mu>1,\quad U_i<t_i,\quad
S_i=g(t_i)-\lambda(t_i)(L_i-1)<g(t_i),\quad L_i\le1+\delta(t_i).\tag{1}
\]
Right joining gives
\[
L_2-1>2y/(1+y),\quad y<\chi(L_2)<\min(x,1-x),\quad y<4/15,
\quad S_2<g(x)-\frac{2\lambda(x)y}{1+y}.\tag{2}
\]
Here \(\chi(L)=(L-1)/(3-L)\) is a local cap. For \(x\ge1/2\),
\[
y<Y(x)=\frac{(1-x)^2}{6x-1-x^2}\le1/7,\quad Y'<0.\tag{3}
\]
The four actual axial reaches \(l,r,u,d\) of \(C\) are positive, since it uniquely covers the center in a finite closed cover. Empty \(F\) horizontal section forces
\[
r\ge\mu-U_2>1-x,\qquad u\ge\mu-U_3>1-y.\tag{4}
\]
The left top-gap endpoint belongs to \(C\):
\[
P=(-T,\mu),\quad T=\mu-S_4>2z/(1+z)>0,\quad z<q(T).\tag{5}
\]
It excludes \(C\) from bottom. We do not assume \(T<1\); the projections below prove it. For two nonempty parallel full sections at distance \(\mu\), write the bound \(B_\mu<1\). Both relevant sections of \(C\) and \(V_4\) are nonempty, giving
\[
l+r+g_T\le B_\mu,\quad S_4+U_4\le B_\mu,\quad g_T=\mu+T-L_3>0.\tag{6}
\]
In particular \(l+r<1\), and
\[
l+T<x+\delta(y),\tag{7}
\]
because \(l+r+T\le B_\mu-\mu+L_3<L_3\le1+\delta(y)\) and \(r>1-x\). No target size has been set to two.

### 2. The original W must bridge the left axial gap

If \(C\) contained the actual \(V_4\) horizontal endpoint \((-\mu+U_4,0)\), then (4), (6) would give \(4\mu-L_3-U_2\le2B_\mu\), hence \(L_3+U_2>2\). But \(\delta(y)<y\) for \(y<4/15\), so \(L_3+U_2<1+y+x<2\). Thus \(l+U_4<\mu\). Only the original \(W\) can fill this true horizontal gap, and closedness forces
\[
(-l,0),(-\mu+U_4,0)\in W.\tag{8}
\]
Its true bottom leg satisfies
\[
A<U_4+q(l)<z+q(l)<q(T)+q(l).\tag{9}
\]
For completeness, in \(W\)'s inward coordinates choose positive normals with coefficients \(c_W,s_W\); the axis-aligned case cannot bridge. Set \(H=c_W/(1+s_W)\in(0,1)\). Projecting the corner and \((\mu-l,\mu)\) gives \(H>1-l\); projecting the actual bottom endpoint \((A,0)\) against \((U_4,\mu)\) gives \(A<U_4+g(H)<U_4+q(l)\). Here \(l<1\) follows from (6). This uses original points without normalizing \(W\) or rooting a floating chord artificially.

### 3. Both central rotation signs

Choose normals \((c,\varepsilon s),(-\varepsilon s,c)\), \(c\ge s>0,c^2+s^2=1\), and put \(\eta=s/(1+c)\in(0,\sqrt2-1]\), \(G=g(\eta),K=\lambda(\eta),\rho=\delta(\eta)\). Axis alignment is excluded by \(O,P\). The endpoint \(\eta=\sqrt2-1\) is allowed; uniformly \(\eta<5/12,K\le1\).

For \(\varepsilon=1\), actual projections give
\[
r+T<\eta,\quad d<\rho-KT=K(\eta-T),\quad
l<G+Ky,\quad x>1-\eta+T.\tag{10}
\]
These use respectively \(s(r+T)+c\mu\le1\), \(sT+c(\mu+d)\le1\), and \(cl+su\le1\). Thus \(0<T<\eta,x>7/12,y<1/7\), and
\[
l+d<G+\rho+Ky=1+K(y-1+2\eta)<1.\tag{11}
\]
For \(\varepsilon=-1\), the actual \(P\)/right, \(P\)/left, left/upper, \(P\)/lower, and vertical-chord projections give
\[
r+T<G,\quad T<x-b_0,\quad b_0=1-G=2\eta/(1+\eta),
\]
\[
l<T+\eta,\quad l<\eta+y/K,\quad
d<\rho+KT=K(\eta+T),\quad d<\rho+y.\tag{12}
\]
Hence \(0<T<G\). If \(\eta<1/4\),
\[
l+d<x+y+\rho-\eta G<1,\tag{13}
\]
since \(\eta G-\rho=\eta(1-4\eta+\eta^2)/(1-\eta^2)>0\). For larger negative rotation only diameter will be needed.

### 4. When the lower endpoint must belong to F

In the ranges (11) or (13), \(W\) cannot contain both the already forced left endpoint and \(C\)'s lower endpoint. Its positive inward normal \((\alpha,\beta)\) would otherwise yield
\[
l+d\ge2\mu-\frac{\alpha+\beta-\mu}{\alpha\beta}>1,
\]
using \(\alpha+\beta-1\le\alpha\beta\). Only \(C,F,W\) can cover the negative vertical half-axis. Limits just below \(C\)'s endpoint therefore give
\[
(0,-d)\in F,\qquad v\ge\mu-d.\tag{14}
\]
No maximum formula for floating \(W\) sections is used. Put \(\Sigma=A+S_2\). Whenever a subsequent bound proves \(\Sigma<1\), bottom has a genuine gap wholly belonging to \(F\), with full chord \(b_F\ge2\mu-\Sigma\). Diameter implies
\[
\Sigma>7/12,\tag{15}
\]
since \(2-\sqrt2>7/12\), or \(17/12>\sqrt2\). If (14) also holds, \(b_F+v^2\le2\) gives, for the branchwise established \(0<d<1\),
\[
\Sigma\ge2(\mu-1)+(\mu-d)^2>(1-d)^2.\tag{16}
\]
Each branch proves the true-gap premise before invoking these bounds.

### 5. A scalar comparison independent of the former G3 placement

Set \(M(\eta)=q(\eta)+q(G)\). Then
\[
0<\eta\le1/3:\quad M<(1-\rho)^2,\qquad
M'=\frac{14(\eta^2+2\eta-1)}{(2-\eta)^2(1+3\eta)^2}\le0.\tag{17}
\]
Thus
\[
M(1/4)=4/7,\quad M(1/3)=8/15,\quad M(7/30)=1576/2703<7/12.\tag{18}
\]
For a self-contained sign proof, the difference \((1-\rho)^2-M\) is
\[
\frac{\eta P_5(\eta)}{(\eta-2)(\eta-1)^2(\eta+1)^2(3\eta+1)},\quad
P_5=31\eta^5-47\eta^4-42\eta^3+34\eta^2+15\eta-7.
\]
On \([0,1/3]\), \(P_5'\ge15+46\eta/9>0\), \(P_5(1/3)=-56/243<0\), while the denominator is negative. This scalar lemma does not import the obsolete G3 midpoint geometry.

### 6. Excluding positive rotation

Since \(x>7/12\), \(\lambda(x)>168/95\), whereas \(K\le1,1+y<19/15\). The derivative of \(q\) is below two on \([0,1)\). Equations (2), (10) give
\[
S_2+q(l)<g(x)-\frac{2\lambda(x)y}{1+y}+q(G)+2Ky<g(x)+q(G).
\]
Combining (9), \(x>1-\eta+T\), and convexity of \(q\),
\[
\Sigma<q(T)+q(\eta-T)+q(G)\le M(\eta).\tag{19}
\]
For \(\eta\le1/3\), \(d<\rho\), so (17) makes \(\Sigma<(1-d)^2<1\), contrary to (16). Above \(1/3\), \(\Sigma<8/15<7/12<1\), contrary to (15).

### 7. Compensation for negative rotation

From (12), \(l<\min(\eta+y/K,\eta+T)\). If
\[
K\lambda(x)\ge\frac{1+KT}{(2-\eta-T)(2-\eta)},\tag{20}
\]
then
\[
S_2+q(l)\le g(x)+q(\eta),\qquad\Sigma<M(\eta).\tag{21}
\]
Indeed, on \(0\le y\le KT\), the function \(-2\lambda(x)y/(1+y)+q(\eta+y/K)\) is convex. Its endpoint increment at \(KT\) relative to zero is
\[
\frac{2T}{(2-\eta-T)(2-\eta)}-\frac{2\lambda(x)KT}{1+KT}\le0.
\]
For \(y\ge KT\), use \(q(l)\le q(\eta+T)\) and the decreasing negative term. Then \(x>T+1-G\) and (9) yield \(\Sigma<q(T)+q(G-T)+q(\eta)\le M\).

Condition (20) holds for \(\eta\ge1/4\): since \(x>b_0+T\), the function \(\lambda(b_0+T)(2-\eta-T)/(1+KT)\) increases in \(T\). Its logarithmic positive derivative exceeds two, while the two subtractive terms sum to at most two because \(K\le1,\eta+T\le\eta+G<1\). At zero,
\[
K\lambda(b_0)(2-\eta)^2>
\frac8{15}\frac{20}{21}(19/12)^2=722/567>1.
\]
Thus \(\Sigma<M\le4/7<7/12\), giving the diameter contradiction without requiring (14).

For \(0<\eta<1/4,x>1-2\eta\), it follows from the stronger sufficient inequality
\[
K\lambda(1-2\eta)(2-\eta-G)(2-\eta)>1+KG.\tag{22}
\]
The difference is \(-(3\eta^4-7\eta^3+4\eta^2+3\eta-1)/((1-\eta)^2(1+\eta)^2)>0\). The numerator increases (derivative at least \(3-21/16\)) and ends at \(-25/256\) at \(1/4\).

### 8. Negative rotation below one quarter, with x at most one half

Let \(m=x-\eta G>0\). Equations (9), (12) imply
\[
z<q(x-b_0),\quad l<m,\quad d<Km,\quad
\Sigma<E_\eta(x):=g(x)+q(x-b_0)+q(x-\eta G).\tag{23}
\]
The function \(F_\eta(x)=(1-K(x-\eta G))^2-E_\eta(x)\) on \([b_0,1/2]\) is strictly concave, since
\(F_\eta''\le2K^2-4/(1+x)^3\le128/225-32/27<0\). At \(x=b_0\) it equals \((1-\rho)^2-M>0\). At \(x=1/2\) it equals
\[
\frac{\eta P_8(\eta)}{3(\eta-3)(\eta-1)^2(\eta+1)^4(2\eta+1)(7\eta+3)},
\]
\[
P_8=424\eta^8-716\eta^7-1032\eta^6-555\eta^5
+594\eta^4+594\eta^3+56\eta^2-67\eta-18<0.
\]
All positive terms sum to at most \(123765/8192<18\) for \(\eta\le1/4\); the denominator is negative. Concavity gives \(F_\eta>0\), hence \(\Sigma<(1-Km)^2<(1-d)^2<1\), contrary to (16).

### 9. Negative rotation with x above one half and eta at most (1-x)/2

Put \(w=1-x\in(0,1/2)\), \(Y=w^2/(4-4w-w^2)\), \(R=2w^2/(4-w^2)\). Then \(0<y<Y\le1/7\), \(\rho\le R\), \(d<R+y<1\). Also \(Y\le2w/7,\delta(Y)\le w^2/6<w\), so \(x+\delta(y)<1\). Using \(q(a)+q(b)\le q(a+b)\) for nonnegative arguments of sum below two, (7), (9), (2) give
\[
\Sigma+2d-d^2<\Phi(y):=g(x)-\frac{2\lambda(x)y}{1+y}
+q(x+\delta(y))+2(R+y)-(R+y)^2.\tag{24}
\]
This is convex on \([0,Y]\): the composite \(q\circ(x+\delta)\) is convex, and \(4\lambda(x)/(1+y)^3-2\ge343/96-2>0\). At the upper endpoint \(2\lambda(x)Y/(1+Y)=g(x)\). The two endpoint deficits are
\[
1-\Phi(0)=\frac{w(11w^4+11w^3-34w^2-28w+24)}{(w-2)^2(w+1)(w+2)^2}>0,\tag{25}
\]
since the parenthesis is at least \(3/2\), and
\[
1-\Phi(Y)=\frac{wQ_{11}(w)}{(w-2)^2(w+2)^2(w^2+4w-4)^2
(3w^4+8w^3-12w^2-8w+8)}>0,\tag{26}
\]
where
\[
\begin{aligned}
Q_{11}={}&51w^{11}+440w^{10}+508w^9-3656w^8-4792w^7+15424w^6\\
&+8384w^5-32128w^4+4480w^3+26624w^2-19456w+4096.
\end{aligned}
\]
The final denominator factor is at least one. An exact sign certificate is
\[
Q_{11}''\ge R_4=310904w^4+167680w^3-385536w^2+26880w+53248>0.
\]
The first comparison follows from \(151816-201264w-204736w^2\ge0\) and three positive higher terms. In the Bernstein basis at \(v=2w\), \(R_4\)'s coefficients are \(53248,56608,43904,20376,21391/2\), all positive. Since \(Q_{11}'(1/2)=-767615/1024<0\) and \(Q_{11}(1/2)=58835/2048>0\), it decreases and stays positive. Convexity proves \(\Phi<1\), yielding \(\Sigma<(1-d)^2<1\), contrary to (16).

### 10. The final negative-rotation interval

For \(\eta<1/4,x>1/2,\eta>(1-x)/2\), one has \(x>1-2\eta\), so (21) gives \(\Sigma<M\). If \(\eta\ge7/30\), (18) gives \(\Sigma<7/12\), contrary to (15). Otherwise
\[
y<Z(\eta)=\frac{\eta^2}{1-2\eta-\eta^2},\qquad d<\rho+Z<1,
\]
and
\[
(1-\rho-Z)^2-M=
\frac{\eta P_9(\eta)}{(\eta-2)(\eta-1)^2(\eta+1)^2(3\eta+1)(\eta^2+2\eta-1)^2}>0,\tag{27}
\]
\[
P_9=52\eta^9+78\eta^8-290\eta^7-344\eta^6+431\eta^5+231\eta^4
-224\eta^3-38\eta^2+47\eta-7.
\]
For \(a_0=7/30\), \(P_9''\le(C_0-1344)\eta-76<0\), with
\(C_0=3744a_0^6+4368a_0^5+8620a_0^2+2772a_0=472388812/421875<1344\). Also \(P_9'(a_0)=55151949841/6075000000>0\), so \(P_9\) increases, ending at \(-75452942887/2460375000000<0\). The denominator in (27) is negative. Thus \(\Sigma<M<(1-\rho-Z)^2<(1-d)^2<1\), contrary to (16). All negative-rotation intervals are exhausted. Together with R19, this closes the entire near top-gap representative in the candidate route.

<a id="R27"></a>
## R27. One rotation branch each for near right gaps and far top gaps

**Scope.** Sections 2-4 concern the near right-gap representative; Sections 5-8 concern the far top-gap representative. Their coordinates and signs must not be exchanged. Throughout \(C\) is the unique center tile and owns no outer midpoint; \(F\) contains \(B=(0,-\mu)\), not the center. Actual reaches \(l,r,u,d\) are positive. Individually normalize only anchored corners, keeping original \(W,C,F\). A disappearing gap is reclassified on the actual resulting family or mapped to an established exclusion.

### 1. Common inputs

Use \(g(t)=(1-t)/(1+t),q(t)=t/(2-t),\lambda(t)=2t/(1-t^2),\delta(t)=2t^2/(1-t^2)\). For an anchored tile,
\[
L\ge\mu>1,\quad S=g(t)-\lambda(t)(L-1)<g(t),\quad U<t,
\quad L\le1+\delta(t),\quad2tL\le1+t^2.\tag{1}
\]
A join \(L_i+S_j\ge2\mu\) gives \(t_j<\chi(L_i)<\min(t_i,1-t_i)\), \(\chi<4/15\), and, only with positive denominators,
\[
t_j<Y_c(t_i)=\frac{t_i^2}{1-2t_i^2},\qquad
t_j<Y_s(t_i)=\frac{(1-t_i)^2}{6t_i-1-t_i^2}.\tag{2}
\]
Here \(\chi(L)=(L-1)/(3-L)\). Two nonempty parallel full sections at distance \(\mu\) obey the bound \(B_\mu<1\); a corner's six-line grid budget is at most two. Actual rooted bottom geometry gives \(b+v^2\le2,b\le\sqrt2\). This module does not use R13's 266-coefficient adjacent certificate; the far nonempty-horizontal exclusion uses only R13 Section 6's grid/parallel argument.

### 2. Near right gap with positive central rotation

The near hosts are \(V_2\) right, \(V_3\) top, \(V_4\) left, \(W=V_1\). Top is joined, and \(C\) fills a true upper-half right gap. For \(x=t_2,y=t_3,z=t_4\),
\[
P=(\mu,e)\in C,\quad e=\mu-S_3>2y/(1+y),\quad u\ge\mu-U_3>1-y.\tag{3}
\]
The tile \(C\) misses bottom (R21 Section 8) and left (diameter); any gaps there belong to \(F\). For positive normals \((c,s),(-s,c)\), put \(\eta=s/(1+c),K=\lambda(\eta),G=g(\eta),\rho=\delta(\eta)\). Axis alignment is excluded by \(O,P\). Actual projections give
\[
e<\eta,\quad d<\eta-e,\quad l<K(\eta-e),\quad u<e+G.\tag{4}
\]
These come from \(c\mu+se\le1,c\mu+s(e+d)\le1,c(\mu+l)+se\le1,s\mu+c(u-e)\le1\). Thus \(e+y>1-G\), giving \(\eta G<y<q(\eta)\). Comparing gives \(\eta^2-4\eta+1<0\), hence \(\eta>4/15\). As \(\eta G\) increases up to \(\sqrt2-1\),
\[
y>44/285>3/20,\quad y<q(\eta)<4/15.\tag{5}
\]
Uniformly,
\[
\eta-e<1/12,\quad l<1/12,\quad d<1/12,\quad e-y>1/10.\tag{6}
\]
The final bound follows from \(e-y>y(1-y)/(1+y)>51/460\). For the first, (3) gives \(y<q(e)\); thus \(e+q(e)>2\eta/(1+\eta)\). If \(e\le\eta-1/12\), this contradicts
\[
\frac{2\eta}{1+\eta}-(\eta-1/12)-q(\eta-1/12)
=\frac{144\eta^3-600\eta^2+181\eta+37}{12(1+\eta)(25-12\eta)}>0.
\]
The numerator is concave on \([1/12,5/12]\), with endpoint values \(48,56/3\). Top joining also gives
\[
z<Y_c(y)<16/193<1/12,\quad U_4<1/12,\quad L_4<145/143.\tag{7}
\]
The right/central vertical sections of \(C\) are nonempty, so with \(g_R=\mu+e-L_2\), \(g_R+u+d\le B_\mu\). Hence \(L_2>1+e-y+d>11/10\), and
\[
S_2<2/3.\tag{8}
\]
Otherwise \(S_2<g(x)\) forces \(x<1/5\), whence \(L_2<13/12<11/10\).

### 3. Near positive rotation when F avoids the negative horizontal half-axis

This includes an empty section or a positive section, with tangency allowed. The depth of \(V_4\)'s horizontal inner endpoint exceeds \(11/12\), while \(l<1/12\). Only original \(W\) can bridge the intervening gap, so it contains that endpoint and \(C\)'s left endpoint. The actual bridge bound gives
\[
A<U_4+q(l)<1/12+1/23=35/276.\tag{9}
\]
If \(W\) also contained the lower endpoint of \(C\), its positive corner projection would give \(l+d>1\), contrary to (6). Closedness therefore forces this lower endpoint into \(F\), with \(v\ge\mu-d\). For \(\Sigma=A+S_2\),
\[
\Sigma<73/92<(11/12)^2<(1-d)^2<1.
\]
There is a genuine bottom gap, wholly in \(F\); \(b\ge2\mu-\Sigma\) and \(b+v^2\le2\) require \(\Sigma>(1-d)^2\), a contradiction. No shared-origin formula for a floating \(W\) section is used.

### 4. Near positive rotation with a negative F horizontal section

Let \(b,f\) be the full bottom/horizontal lengths of \(F\). Both are nonempty, including tangency, so
\[
b+f\le B_\mu<1.\tag{10}
\]
If original \(W\) contained \((0,-d)\), choose positive inward coefficients \(c_W,s_W\), and set \(H=s_W/(1+c_W)\). The corner/lower-endpoint projection gives \(H>\mu-d>11/12\), hence \(s_W>264/265\). Therefore \(A<265/264\), and every horizontal-section point of \(W\) has inward coordinate \(X<(1-s_W)/c_W=g(H)<1/23\). Since the left host reaches less than \(1/12\) and \(C\)'s left reach is less than \(1/12\), \(F\) must fill a horizontal interval of length \(f>5/6\). Also \(A+S_2<265/264+2/3<2\), so a true bottom gap gives \(b>29/88\). This violates (10). Thus \(W\) misses \(C\)'s lower endpoint and \(F\) contains it, \(v\ge\mu-d\).

Let original \(W\)'s left leg and horizontal length be \(D,H_W\), and put \(g_L=\max(0,2\mu-L_4-D)\). If positive, the whole gap belongs to \(F\); its nonempty left/central sections give \(g_L+v\le B_\mu\), hence \(g_L<d\). This also holds when \(g_L=0\). Therefore
\[
D>2\mu-L_4-d.\tag{11}
\]
Always \(b\ge2\mu-A-S_2\): if no bottom gap exists, the right side is nonpositive. Negative horizontal coverage gives \(f+H_W+l+U_4\ge\mu\). Combining (10), \(A+D+H_W\le2\), (11) yields
\[
A+H_W>3\mu-1-S_2-l-U_4,\quad
A+H_W<2-2\mu+L_4+d,
\]
\[
L_4+S_2+U_4+l+d>5\mu-3>2.\tag{12}
\]
But (6)-(8) bound the left side by \(145/143+2/3+1/12+1/6<2\). Thus all positive central rotations in the near right-gap representative are excluded.

### 5. Far top gap with negative central rotation

Now \(V_1,V_2,V_4\) host left, right, top, and \(W=V_3\) is original. The top gap lies in the right half and belongs to \(C\). R13 Section 6 makes \(F\)'s horizontal section empty, including when \(C\) also fills a right gap. A left-upper gap cannot belong to \(C\), by the center/top-gap triangle area, or to \(F\), by distance from \(B\); hence
\[
L_1+S_4\ge2\mu.\tag{13}
\]
Put \(a=t_1,x=t_2,z=t_4,\omega=1-a\). The unique left-axis join gives
\[
l\ge\mu-U_1>\omega.\tag{14}
\]
The actual top exit is \(P=(E,\mu)\in C\), \(E=L_4-\mu\ge0\). For negative normals \((c,-s),(s,c)\), use the same definitions \(\eta,G,K,\rho\). Projection with left/right/lower endpoints gives
\[
l+E<\eta,\quad r<G+E,\quad d<\rho-KE\le\rho.\tag{15}
\]
Thus \(0<\omega<\eta\). No corner contributes to the negative vertical half-axis, so \(F\) directly joins the lower endpoint, \(v\ge\mu-d\). Both bottom short legs are below \(\mu\); the true bottom gap crosses \(B\) and belongs wholly to \(F\). For \(\Sigma=S_1+S_2\), the square and diameter bounds give
\[
\Sigma>(1-d)^2>(1-\rho)^2,\qquad\Sigma>7/12.\tag{16}
\]
Here \(\Sigma<2<2\mu\) already proves the gap; \(\Sigma<1\) is unnecessary.

### 6. The true small excess of the top long leg

Put \(\epsilon_4=L_4-1>0\); then \(E<\epsilon_4\). From \(a>1-\eta\) and the left join,
\[
z<Y_s(a)<\frac{\eta^2}{4-4\eta-\eta^2},\quad\epsilon_4\le\delta(z).\tag{17}
\]
In particular \(z<\eta^2/2,\epsilon_4<\eta/12\), and \(G+\epsilon_4<G+\eta<1\). Sharper bounds are
\[
0<\eta\le1/3:\quad\epsilon_4<27\eta^4/88,\quad4\epsilon_4<\eta/22<\eta/20;\tag{18}
\]
\[
1/3\le\eta\le3/8:\quad z<9/151,\quad\epsilon_4<81/11360;\tag{19}
\]
\[
3/8\le\eta<5/12:\quad z<25/311,\quad\epsilon_4<625/48048.\tag{20}
\]
For (18), the denominator in (17) is at least \(23/9\), so \(z<(9/23)\eta^2,z^2<1/529\), giving the displayed excess bound. It is an upper bound for \(E=L_4-\mu\), not the assertion \(\mu=1\).

### 7. Exhausting direct right joining and an original W bridge

Define \(M=q(\eta)+q(G),A=1-G-q(\eta),T_0=g(A),A_b=1-\eta-q(G)\). On the physical interval, \(A_b\ge A>\eta/2\), and \(M,T_0\) decrease.

If \(r+U_2\ge\mu\), then \(x>1-G-\epsilon_4\), and \(|g'|\le2,\omega<\eta\) give
\[
\Sigma<q(\omega)+g(1-G-\epsilon_4)<M+2\epsilon_4.\tag{21}
\]
Otherwise original \(W\) uniquely bridges the true right axial gap. Its true top leg \(D\) obeys \(D<U_2+q(r)<x+q(G+\epsilon_4)\). The other top-gap endpoint \((T,\mu)=(\mu-D,\mu)\in C\) satisfies \(T+l<\eta\), so
\[
D>1-\eta+\omega,\quad x>A_b+\omega-\Delta_q,\quad
\Delta_q=q(G+\epsilon_4)-q(G)<2\epsilon_4.
\]
The \(g\)-arguments stay positive since \(A_b>\eta/2,2\epsilon_4<\eta/6\). Thus
\[
\Sigma<q(\omega)+g(A_b+\omega)+4\epsilon_4.\tag{22}
\]
The sum of the first two terms is convex on \([0,\eta]\). Its endpoints are \(g(A_b)\le T_0\) and \(q(\eta)+q(q(G))<M\). Therefore both cases yield
\[
\Sigma<\max(M,T_0)+4\epsilon_4.\tag{23}
\]
The original \(W\) is never replaced or assigned an artificial rooted vertical section.

### 8. Scalar contradictions throughout the negative rotation range

For \(0<\eta\le1/3\),
\[
\max(M,T_0)+\eta/20<(1-\rho)^2.\tag{24}
\]
The two differences have positive denominators and respective numerators \(\eta P_M\), \(\eta P_T\), with denominators \(20(2-\eta)(1-\eta^2)^2(1+3\eta)\) and \(20(1-\eta^2)^2(1+2\eta-2\eta^2)\), where
\[
P_M=3\eta^6-625\eta^5+932\eta^4+850\eta^3-673\eta^2-305\eta+138,
\]
\[
P_T=2\eta^6-382\eta^5+375\eta^4+444\eta^3-276\eta^2-142\eta+59.
\]
On \([0,1/3]\), \(P_M'\le2/27-305-736\eta/9<0\), \(P_T'\le-9914/81<0\), and their endpoint values are \(160/81,368/729>0\). Thus (18), (23), (24) contradict (16). On \([1/3,3/8]\), (19) gives \(\Sigma<7/13+81/2840<7/12\), since \(M(1/3)=8/15<T_0(1/3)=7/13\). On \([3/8,\sqrt2-1]\), (20) gives \(\Sigma<116/221+625/12012<7/12\), since \(M(3/8)=116/221>T_0(3/8)=49/94\). This excludes all negative central rotations in the far top-gap family.

### 9. Exact endpoint identities for the two remaining rotations

These are structural identities, not further exclusions. In the near right-gap family with negative normals \((c,-s),(s,c)\), write the actual intervals as \([\alpha,\alpha+1],[\beta,\beta+1]\). The center is interior, so both lower bounds are negative. If the upper endpoint first met the second upper support, \(\beta+1=cu\), the point \((\mu,e)\) and the first width would force \(\mu\le c\le1\). Similarly, if the lower endpoint first met the first upper support, \(\alpha+1=sd\), projections force \(\mu\le s\le1\). Both are impossible. Hence \(\alpha=-su,\beta=-cd\), and the actual horizontal reaches are
\[
l=\min(Ku,d/K),\qquad r=\min(1/c-Ku,1/s-d/K).\tag{25}
\]
For the far top-gap family with positive rotation, interchange coordinates in this local lemma, giving
\[
d=\min(Kr,l/K),\qquad u=\min(1/c-Kr,1/s-l/K).\tag{26}
\]
These retain the same actual \(C\); optimizing separate minimum branches independently must not discard that coupling.

<a id="R28"></a>
## R28. Excluding the entire near G2 representative

**Scope.** The near hosts \(V_2,V_3,V_4\) are right, top, left, and original \(W=V_1\) is free. The same \(C\) uniquely contains the center and owns no outer midpoint; \(F\) contains \(B=(0,-\mu)\), not the center. Top is joined, and a true upper-half right gap belongs wholly to \(C\), which misses left and bottom. Individual anchored dominations that remove this gap enter R18's exclusion; original \(W,C,F\) remain fixed. R27 excludes positive central rotation; this module treats negative rotation and then reselects hosts in the far case.

### 1. A new actual long-leg lower bound

Use \(x=t_2,y=t_3,z=t_4\), \(U_i<t_i,L_i+S_i+U_i<2,L_i\le1+\delta(t_i)\), \(\delta(t)=2t^2/(1-t^2)\). For negative normals \((c,-s),(s,c)\), \(c\ge s>0,c^2+s^2=1\), put \(\eta=s/(1+c)\le\sqrt2-1<5/12,K=s/c=\lambda(\eta),G=g(\eta)\). R27's actual supports \(\alpha=-su,\beta=-cd\) give
\[
l=\min(Ku,d/K).\tag{1}
\]
Both right-gap closed endpoints belong to \(C\):
\[
P=(\mu,e),\ e=\mu-S_3,\qquad Q=(\mu,L_2-\mu).\tag{2}
\]
The first projection of \(Q\) is at most \(1-su\). Since \(\mu>1\),
\[
L_2>1+w,\qquad w=u-\eta.\tag{3}
\]
The second projection of \(P\) against the lower endpoint gives \(e+d<G\). Also \(e+u\ge2\mu-S_3-U_3>L_3\). Since \(1-G=\eta+\eta G\),
\[
0<L_3-1<w-d-\eta G=:N.\tag{4}
\]
Top joining yields \(z<\chi(L_3)=q(L_3-1)\), hence
\[
N>0,\quad d<w,\quad0<w<\sqrt2-1<5/12,\quad z<q(N),\quad U_4<q(N).\tag{5}
\]
Positivity of \(w\) is derived here; its upper bound follows from \(L_2\le\sqrt2\) and (3).

### 2. Angle balance inside the same C

From (1), \(K\le1\), and \(u=w+\eta\),
\(l-d\le(1-K)l\le K(1-K)(w+\eta)\). On the full domain,
\[
K(1-K)(w+\eta)<6\eta G/5.\tag{6}
\]
Using \(w<5/12\), the difference is bounded below by
\[
-\frac{\eta P(\eta)}{30(1-\eta^2)^2},\quad
P=36\eta^4-132\eta^3-145\eta^2+82\eta-11.
\]
The polynomial is concave on \([0,5/12]\), since \(P''=432\eta^2-792\eta-290<0\). Its tangent at \(2/9\) gives \(P(\eta)\le-293/243-(34/81)\eta<0\). Consequently
\[
l<d+6\eta G/5<6w/5-d/5,\quad l+d<2w<1,\quad N+l<6w/5.\tag{7}
\]

### 3. A short-leg bound depending only on the long-leg excess

Let \(T(w)=\sqrt{w(2+w)}\), \(\Phi(w)=(1+w)(1-T(w))\). Every normalized corner with \(L\ge1+w>1\) satisfies
\[
S\le\Phi(w).\tag{8}
\]
Indeed, for positive normal coefficients \(a,b\), \(a^2+b^2=1,aL\le1\), its short leg is \((1-bL)/a\). At fixed \(L\) this increases in \(a\), so \(S\le L(1-\sqrt{L^2-1})\); this decreases for \(1<L\le\sqrt2\). No nearest-horizontal assumption on that corner is needed. By (3),
\[
S_2\le\Phi(w).\tag{9}
\]
The scalar comparisons needed below, all for \(0<w<\sqrt2-1<5/12\), are
\[
\Phi(w)+q(6w/5)<(1-w)^2,\tag{10}
\]
\[
\Phi(w)+6w/5+q(w)<1,\quad
\Phi(w)+w+q(w)+\Delta(w)<1,\quad\Delta(t)=\frac{t^2}{2(1-t)},\tag{11}
\]
\[
\Phi(w)+2w<1.\tag{12}
\]
Section 8 supplies exact proofs.

### 4. F avoids the negative horizontal half-axis

This includes an empty section or a positive section, even tangency. Diameter gives \(l<\sqrt2-1\), while the left host's horizontal inner endpoint has depth above \(11/15\), since top joining gives \(z<4/15\). Thus only original \(W\) can bridge their true gap. Its actual bottom leg obeys \(A<U_4+q(l)\). Using (5), (7), and the superadditivity of \(q\),
\[
A+S_2<\Phi(w)+q(N)+q(l)\le\Phi(w)+q(N+l)
<\Phi(w)+q(6w/5)<(1-w)^2<(1-d)^2<1.\tag{13}
\]
The tile \(W\) already contains \(C\)'s left endpoint; if it also contained the lower endpoint, positive corner projections would give \(l+d>1\), contrary to (7). Thus actual closed coverage forces \((0,-d)\in F\), with \(v\ge\mu-d\). Equation (13) proves a genuine bottom gap wholly in \(F\). The bound \(b+v^2\le2\), \(b\ge2\mu-A-S_2\), requires \(A+S_2>(1-d)^2\), a contradiction. No maximum formula for a floating vertical section is used.

### 5. In the negative horizontal type, W still cannot reach the lower endpoint

The bottom and horizontal sections of \(F\) are nonempty, so
\[
b+f\le B_\mu<1.\tag{14}
\]
If original \(W\) contained \((0,-d)\), its positive inward normal coefficients would give \(H=s_W/(1+c_W)>\mu-d>1-d\), without requiring \(c_W\ge s_W\). Hence
\[
A<1+\Delta(d),\qquad X<q(d)\text{ for every horizontal-section point of }W.\tag{15}
\]
The first follows from \(s_WA\le1\) and \(1/s_W<[1+(1-d)^2]/[2(1-d)]\); the second from \(c_WX+s_W\mu\le1\) and \(g(H)<q(d)\). Thus \(F\) must fill length \(f\ge\mu-l-M\), \(M=\max(U_4,q(d))\). Always \(b\ge2\mu-A-S_2\), including the automatic nonpositive bound if bottom is joined. Therefore
\[
b+f>2-[S_2+l+M+\Delta(d)].\tag{16}
\]
The bracket is at most
\[
\Phi(w)+6w/5-d/5+\max(q(w-d),q(d))+\Delta(d).
\]
For fixed \(w\), both functions inside this maximum, with the added quadratic-rational and linear terms, are convex on \([0,w]\). Their maximum is bounded at the endpoints, giving at most
\(\Phi(w)+\max(6w/5+q(w),w+q(w)+\Delta(w))<1\) by (11). Equation (16) contradicts (14). Thus \(F\) contains the lower endpoint and \(v\ge\mu-d\). This argument assumes neither \(W\) nor \(F\) contains the left endpoint and gives no artificial common horizontal root.

### 6. Final joint left/bottom/horizontal budget

Let original \(W\)'s left leg and horizontal length be \(D,H_W\). Any true left gap belongs to \(F\), since \(C\) misses left. Its nonempty left/central sections and \(v\ge\mu-d\) imply \(g_L<d\); the same strict inequality holds when \(g_L=0\). Thus \(D>2\mu-L_4-d\). Combine
\[
f+H_W+l+U_4\ge\mu,\quad A+D+H_W\le2,
\quad b\ge2\mu-A-S_2,
\]
with (14), exactly as in R27, to obtain
\[
L_4+S_2+U_4+l+d>5\mu-3>2.\tag{17}
\]
Put \(v_0=d+\eta G\in(0,w)\). Equations (5), (7) give the opposite upper bound
\[
L_4+S_2+U_4+l+d
<1+\Phi(w)+\delta(q(w-v_0))+q(w-v_0)+2v_0.
\]
The final function is convex in \(v_0\); its endpoint values are \(\delta(q(w))+q(w)\) and \(2w\). Since \(\delta(q(w))=\Delta(w)\) and
\[
\frac{q(w)+\Delta(w)}w\le12/19+5/14=263/266<1,
\]
the maximum is \(2w\). Equation (12) makes the upper bound less than two, contrary to (17). All horizontal types for negative central rotation are excluded. Together with R27's positive rotation and R26's top-gap representative, this closes the entire near G2 representative.

### 7. A host restriction for every remaining far family

For far hosts \(V_1\) left, \(V_2\) right, \(V_4\) top and original free \(W=V_3\),
\[
W\text{ cannot contain the right midpoint; its actual right leg }A<\mu.\tag{18}
\]
Otherwise reselect \(W\) as right host, retain \(V_1,V_4\), and reflect horizontally. The selected hosts become exactly the excluded near pattern. Duplicated midpoint memberships permit this reselection. If a far top gap remains, \(W\) also misses the top midpoint, so it has no outer midpoint. Far negative central rotation with a top gap was excluded in R27; positive rotation and other far edge patterns require further work.

### 8. Exact scalar square-difference proofs

Let \(t=\sqrt{w(2+w)}>0\), \(0<w<5/12\). For (10), rearrange to \(t>V>0\), with
\[
V=\frac{w(3w^2-14w+18)}{(1+w)(5-3w)},\quad
t^2-V^2=\frac{w(3w-2)R_3(w)}{(1+w)^2(3w-5)^2}>0,
\]
\(R_3=30w^3-98w^2+92w-25\). Its derivative is at least \(31/3>0\), yet \(R_3(5/12)=-145/96<0\), and \(3w-2<0\).

The first part of (11) is \(t>V_0>0\), where
\[
V_0=\frac{w(27-11w)}{5(2-w)(1+w)},\quad
t^2-V_0^2=\frac{wP_5(w)}{25(w-2)^2(w+1)^2},
\]
\(P_5=25w^5-296w^3+544w^2-429w+200>0\), since \(w^2(544-296w)\ge0\) and \(200-429w\ge85/4\).

The second part is \(t>V_1>0\), where
\[
V_1=\frac{w(3w^2-12w+10)}{2(w-2)(w-1)(w+1)},\quad
t^2-V_1^2=\frac{wP_7(w)}{4(w-2)^2(w-1)^2(w+1)^2},
\]
\(P_7=4w^7-8w^6-33w^5+120w^4-168w^3+168w^2-116w+32\). Group \(w^4(120-33w-8w^2)+4w^7\ge0\); the remainder is at least \(98w^2-116w+32\ge49/72>0\). Finally (12) is \(t>3w/(1+w)\), with square difference
\[
\frac{w\{w^3+4(w-1/2)^2+1\}}{(1+w)^2}>0.
\]
All sides squared are positive, and every denominator is positive on the stated domain. These are full-interval algebraic proofs, not angle samples or placement searches.

<a id="technical-part-F"></a>
# Technical Part F. Far-end gaps and horizontal sections

Modules: [R29](#R29), [R29N](#R29N), [R30](#R30), [R31](#R31), [R32](#R32), [R33](#R33), [R34](#R34), [R35](#R35), [R36](#R36), [R37](#R37), [R38](#R38), [R39](#R39).

<a id="R29"></a>
## R29. Excluding every standardized far top-gap representative

**Scope.** In \(T_\mu\), \(\mu>1\), the far hosts \(V_1,V_2,V_4\) are left, right, top, and original \(W=V_3\) is free. The actual \(C\) uniquely contains the center and no outer midpoint; \(F\) contains the bottom midpoint but not the center. A true right-half top gap belongs wholly to \(C\). R27 establishes an empty horizontal section of \(F\), left joining, and direct \(C/F\) joining on the negative vertical axis. R27 excludes negative central rotation; this module treats positive rotation. Neither the swapped-direction caps withdrawn in R30 nor a one-shot clamp is a premise.

### 1. Actual endpoints and feedback from left joining

The actual top exit is \(P=(E,\mu)\in C\), \(E=L_4-\mu\ge0\). For positive normals \((c,s),(-s,c)\), \(c\ge s>0\), put \(\eta=s/(1+c)\le\sqrt2-1<5/12\), \(K=\lambda(\eta)\), \(G=g(\eta)\). Projections give
\[
l+E<G,\qquad r<\eta+E.\tag{1}
\]
R27's actual-support identity gives
\[
d=\min(Kr,l/K)\le Kr<K(\eta+E).\tag{2}
\]
Left joining \(L_1+S_4\ge2\mu\) implies \(z=t_4<\chi(L_1)<4/15\), so
\[
0\le E<L_4-1\le\delta(z)<32/209<1/6.\tag{3}
\]
R28's long-leg tool gives \(S_4\le\Phi(E)=(1+E)(1-\sqrt{E(2+E)})\). For \(0<E\le1/6\), \(\Phi(E)+3E<1\), since
\[
E(2+E)-\left(\frac{4E}{1+E}\right)^2
=\frac{E(E^3+4E^2-11E+2)}{(1+E)^2}>0,
\]
using \(2-11E\ge1/6\); at zero a weak comparison suffices. Empty \(F\) horizontal section gives \(l\ge\mu-U_1\). Combining the same tile's \(L_1+S_1+U_1<2\) with left joining yields \(S_1<l+S_4-1\le l-3E\). Also \(t_1>1-l\), so
\[
l>3E,\qquad S_1<q(l).\tag{4}
\]
These are coupled bounds from the same \(V_1\), not independently chosen legs.

### 2. The actual long bottom chord of F

Both bottom short legs are below \(1<\mu\), so the true bottom gap straddles its midpoint and belongs wholly, endpoints included, to \(F\). Only \(C,F\) meet the negative vertical axis; hence \(F\) contains \(C\)'s lower endpoint, \(v\ge\mu-d\). Its actual chord obeys \(b\ge2\mu-S_1-S_2,b+v^2\le2,b\le\sqrt2\). Thus
\[
\Sigma=S_1+S_2>(1-d)^2,\qquad\Sigma>7/12.\tag{5}
\]
For
\[
R(\eta,E)=[1-K(\eta)(\eta+E)]^2,
\]
the facts \(K\le1,\eta+E<7/12<1\), (2), and \(d>0\) give
\[
\Sigma>R(\eta,E).\tag{6}
\]
Both budgets concern the same original \(F\).

### 3. Direct right joining or a complete original W bridge

If \(r+U_2\ge\mu\), then \(S_2<q(r)\), and (1), (4) imply
\[
\Sigma<D(\eta,E):=q(G-E)+q(\eta+E).\tag{7}
\]
Otherwise only original \(W\) fills the true right axial gap. Its actual top leg satisfies \(D_W<U_2+q(r)\). The other top-gap endpoint \((T,\mu)\in C\), \(T=\mu-D_W\), obeys \(T+l<G\), so \(t_2>1-G+l-q(r)\). Put \(A=1-G\). The argument is positive because
\[
A+l-q(r)>A+3E-q(\eta+E)\ge A-q(\eta)
=\frac{3\eta(1-\eta)}{(1+\eta)(2-\eta)}>0,
\]
using \(q(\eta+E)-q(\eta)<2E\). Hence \(\Sigma<q(l)+g(A+l-q(\eta+E))\). This is convex in \(l\), whose actual range is \(3E<l<G-E\). Endpoint maximization gives
\[
\Sigma<\max\{W(\eta,E),U(\eta,E)\},\tag{8}
\]
\[
W=q(3E)+g(A+3E-q(\eta+E)),\qquad
U=q(G-E)+q(E+q(\eta+E)).
\]
The term \(q(3E)\) must be retained. The source's abandoned candidates either omitted it or incorrectly treated \(\min(q(l),l-3E)\) as convex. Only the genuine bound \(q(l)\) is used here.

### 4. Small central angles: separate concavity and exact vertex deficits

Consider \(0\le\eta\le4/15,0\le E\le1/6\). All arguments are legal: \(G-E>0,\eta+E<1,E+q(\eta+E)<1\), and
\[
0\le v:=A+3E-q(\eta+E)<A+3E\le35/38<1.
\]
The functions \(D,U,W\) are separately convex in \(\eta,E\). In \(\eta\), this follows from convexity of \(G\), monotone convex \(q\), and concavity of \(A-q(\eta+E)\) composed with decreasing convex \(g\); in \(E\) it follows by differentiation. Meanwhile
\[
R_{\eta\eta}=\frac{8P}{(1-\eta^2)^4},
\]
\[
P=3E^2\eta^4+8E^2\eta^2+E^2+3E\eta^5+18E\eta^3+3E\eta+9\eta^4+4\eta^2-1.
\]
All coefficients of \(P+1\) are nonnegative, and \(P\le P(1/3,1/6)=-1/9\). Thus each \(R-D,R-U,R-W\) is concave in \(\eta\). In \(E\),
\[
R_{EE}=2K^2\le28800/43681<3/4,\quad D_{EE}\ge1,\quad U_{EE}\ge15/8,
\]
and
\[
\partial_E^2g(v)=g''(v)(3-q'(\eta+E))^2-g'(v)q''(\eta+E)>3/4.
\]
Indeed \(g''\ge1/2,-g'\ge1/2,q'<2,q''\ge1/2\). Adding convex \(q(3E)\) gives \(W_{EE}>3/4\). Thus the three differences are separately concave. Their lower bounds are the bilinear interpolants of these exact vertex values, listed in the order \(R-(D,U,W)\):

- At \((0,0)\): \((0,0,0)\).
- At \((0,1/6)\): \((15/77,111/805,23/93)\).
- At \((4/15,0)\): \((2391322/15332031,1068439/4717548,1899716/13672153)\).
- At \((4/15,1/6)\): \((10416321/371594267,69032193/3470848579,57363/3887609)\).

Except at the origin they are positive; actual \(\eta>0\) gives positive weight to right-hand vertices. Therefore
\[
\max(D,U,W)<R(\eta,E),\tag{9}
\]
contradicting (6)-(8).

### 5. Large central angles contradict diameter

On \([4/15,5/12]\times[0,1/6]\), the same functions remain separately convex. Their domains follow from \(G-E\ge25/102\), \(\eta+E\le7/12\), \(E+q(\eta+E)\le59/102<1\), and positivity of \(v\) from the shifted \(q\)-bound above. All \(g\)-denominators are positive. The exact vertex values of \(7/12-(D,U,W)\) are:

- At \((4/15,0)\): \((31/1404,5/54,19/3756)\).
- At \((4/15,1/6)\): \((4805/102084,37117/953508,397/11748)\).
- At \((5/12,0)\): \((125/2052,205/1188,95/1284)\).
- At \((5/12,1/6)\): \((1165/36516,11453/311460,13/228)\).

Separate convexity bounds each function by the bilinear vertex interpolant, so
\[
\max(D,U,W)<7/12.\tag{10}
\]
This contradicts (5). Together with R27's negative rotation, the standardized far top-gap representative is excluded in the candidate argument.

<a id="R29N"></a>
## R29N. Three far edge states and the corrected parallel directions

**Scope.** Use the corrected continuation of 15 October 2026: top pairs with the central horizontal segment \(H_0\), and right with the central vertical segment \(V_0\). The former swapped-direction caps are withdrawn; R30 documents that correction. In the far family \(V_1,V_2,V_4\) host left, right, top, original \(W=V_3\) is free, \(C\) uniquely contains the center but no outer midpoint, and \(F\) contains the bottom midpoint but not the center.

### 1. Exactly three remaining outer-edge states

R28 excludes the right midpoint from \(W\). R29 excludes every standardized true top gap, so top is joined in every remaining family. Any left/right corner gap is above its corresponding midpoint. Its points are at distance strictly above \(\sqrt2\) from the bottom midpoint in \(F\); thus the whole gap, including both closed endpoints, belongs to \(C\). Since \(C\) cannot meet both side edges at distance \(2\mu>\sqrt2\), the exhaustive states are: left gap in \(C\) with right/top joined; right gap in \(C\) with left/top joined; or all three joined. Bottom is handled separately, retaining all \(C/F\) coverage and corner overlap. Empty, positive and negative horizontal sections of \(F\) remain possible at this stage.

### 2. A nonempty F horizontal section excludes every bottom contact of C

Here nonempty includes tangency. Let \(B=B_\mu<1\). If a side gap is present and \(C\) also meets bottom, then \(C\)'s side/central-vertical pair and bottom/central-horizontal pair are both nonempty, contributing at most \(2B\). The bottom/horizontal pair of \(F\) contributes at most \(B\); its rooted central vertical length is \(v_F<\mu\). Other \(C/F\) outer contributions are redundant under corner coverage; lower side contributions of \(F\) are already covered by \(V_1,V_2\). The corner grid sum is at most eight. Hence
\[
12\mu\le8+3B+v_F<11+\mu<12\mu,
\]
impossible, even for a tangent bottom contact of \(C\). If no side gap is present, R13's grid argument gives \(12\mu\le8+2B+2\mu<12\mu\). Thus every state with a nonempty horizontal section of \(F\) has \(C\) completely disjoint from bottom. No such assertion is made when that section is empty.

### 3. Three budgets for the same F

A left/right midpoint host cannot meet the central vertical line: its corner, side midpoint and any such point form a triangle of area \(\mu^2/2>1/2\). The top host cannot meet the negative vertical half-axis, and the upper-right \(W\) cannot reach it by diameter. Thus only \(C,F\) cover that half-axis, forcing \(F\) to contain \(C\)'s lower endpoint, \(v\ge\mu-d\).

With nonempty \(F\) horizontal section, Section 2 assigns the whole bottom gap to \(F\). For its full bottom/horizontal lengths \(b,f\), and \(\Sigma=S_1+S_2\),
\[
b\ge2\mu-\Sigma,\quad b+f\le B<1,\quad b+v^2\le2,\quad b\le\sqrt2.
\]
Consequently
\[
\Sigma>1+f,\qquad\Sigma>(1-d)^2,\qquad\Sigma>7/12.\tag{1}
\]
For \(a=t_1,x=t_2\), the bounds \(S_1<g(a),S_2<g(x)\) imply
\[
a+x+3ax<1.\tag{2}
\]
This is a joint restriction on the actual bottom corners, not a transferred G3 midpoint bound.

### 4. Under three joins and nonempty F section, W cannot duplicate the top midpoint

Suppose original \(W\) contains it. Normalize \(W\) individually by domination. Three joins persist, and the unchanged \(F\) still has its nonempty section. R28 excludes the right midpoint from \(W\). Write its top long leg/right short leg/root/angle as \(L_3,S_3,U_3,t\), and write \(z=t_4,a=t_1,x=t_2\). The top-midpoint triangle argument makes both top-host horizontal sections empty. Their positive vertical sections have the same actual top-midpoint origin, so
\[
u+\max(U_4,U_3)\ge\mu,\qquad u>1-\max(z,t).\tag{3}
\]
This maximum is valid specifically because both tiles share that midpoint. For \(C\)'s actual full horizontal length \(h_C\), bottom/horizontal coverage gives
\[
h_C\ge4\mu-B-\Sigma-U_1-U_2.\tag{4}
\]
At the left/right joins, R13's audited adjacent-corner lemma gives
\[
L_4+S_1+a+2z-z^2\le2,\quad L_3+S_2+x+2t-t^2\le2.\tag{5}
\]
The dependency on its 266 rational Bernstein coefficients is retained. Since \(L_3+L_4\ge2\mu,U_1<a,U_2<x\),
\[
h_C>6\mu-B-4+2z-z^2+2t-t^2>1+2z-z^2+2t-t^2.\tag{6}
\]
Put \(m=\max(z,t),n=\min(z,t)\). Then \(h_C+u^2>2+2n-n^2>2\), contrary to the actual same-tile horizontal-chord/upper-root bound. This excludes only the duplicate-top-midpoint subclass. A side-gap state lacks one join premise for (5).

### 5. Correct caps for the last floating sections

Let original \(W\)'s actual top/right legs be \(D,A\), and central horizontal/vertical lengths \(H,J\). Top joining gives \(D\ge2\mu-L_4\). When \(H_0\cap W\) is nonempty, the true parallel pair is top/horizontal, so \(D+H\le B\); when empty, \(H=0\). Uniformly,
\[
0\le H<\delta(z),\qquad\delta(t)=2t^2/(1-t^2).\tag{7}
\]
Likewise, **only when right is joined**, the right/vertical pair gives \(0\le J<\delta(x)\). A true right gap does not permit this cap. The former \(J<\delta(z),H<\delta(x)\) bounds were swapped and are withdrawn; an algebraic UNSAT result under them cannot establish geometric validity.

R13 already gives \(J>0\) under three joins and nonempty \(F\) section. Combining Section 4 and R28, that residual family satisfies
\[
W\text{ has no outer midpoint},\quad0<J<\delta(x),\quad
0\le H<\delta(z),\quad a+x+3ax<1.
\]
Its vertical section is genuinely floating. It cannot be rooted at the top midpoint or combined with \(U_4\) using a maximum. The actual endpoint positions and the \(C/F\) junction still require control.

<a id="R30"></a>
## R30. Correcting parallel directions and strengthening actual far axial constraints

**Scope.** Far hosts \(V_1,V_2,V_4\) are left, right, top; original free \(W=V_3\), \(C\), and \(F\) remain actual unit tiles. The tile \(C\) uniquely contains the center, owns no outer midpoint, and has actual reaches \(0<l,r,u,d<\mu\); \(F\) contains the bottom midpoint but not the center. Top is joined, leaving a left gap, a right gap, or three joins. Conditions concerning a nonempty horizontal section of \(F\) do not transfer to its empty-section case.

### 1. Explicit withdrawal of the wrong parallel caps

For \(W\)'s right/top legs \(A,D\), horizontal/vertical central lengths \(H,J\), the correct pairs are
\[
D+H\le B_\mu\quad\text{(top and central horizontal)},\qquad
A+J\le B_\mu\quad\text{(right and central vertical)}.
\]
Each requires both sections actually nonempty. Top joining gives \(H<\delta(z)\); right joining gives \(J<\delta(x)\). The old swapped caps \(J<\delta(z),H<\delta(x)\) are withdrawn. A true right gap does not permit \(J<\delta(x)\).

The source preserves the original continuation and an early failed three-join candidate separately. Its 13 UNSAT queries were consequences of a false geometric premise and are not proof evidence. R28 used valid bottom/horizontal, right/vertical and left/vertical pairs; R29 used actual projections and valid \(F\) sections. Their main chains did not use the withdrawn pairing. Historical frozen packages are unchanged.

### 2. Valid common constraints

For anchored angles \(a=t_1,x=t_2,z=t_4\), write long/short legs and roots \(L_i,S_i,U_i\), with
\[
L_i+S_i+U_i<2,\quad U_i<t_i,\quad L_i\le1+\delta(t_i),
\quad\delta(t)=2t^2/(1-t^2).
\]
All side gaps belong wholly to \(C\); \(F\) cannot reach upper side-edge points. If \(F\)'s horizontal section is nonempty, including tangency, R29N excludes \(C\) from bottom and assigns the entire bottom gap to \(F\). For \(h_C=l+r\), the triangle-area and diameter bounds give
\[
h_Cu\le1,\qquad h_C\le\sqrt2<99/70.\tag{1}
\]
The triangle bound follows by maximizing the separately affine determinant at square vertices; it is not sampled geometry.

### 3. A valid subtraction of C/F overlap on the negative vertical axis

Suppose a side gap is present and \(F\)'s horizontal section is nonempty. The actual side/central-vertical sections of \(C\) give \(\text{side length}+u+d\le B\); the bottom/horizontal sections of \(F\) give \(b+f\le B\), where \(B=B_\mu<1\). Only \(C,F\) meet the negative vertical half-axis. After removing the overlap with \(C\), the effective length needed from \(F\) is exactly \(\mu-d\), although its full original length remains at least that value. Other outer contributions are redundant under corner coverage. The grid therefore satisfies
\[
12\mu\le8+2B+h_C+\mu-d,
\quad h_C-d\ge11\mu-8-2B>\mu.\tag{2}
\]

### 4. An asymmetric axial-chord lemma

**Lemma.** A unit square containing the center in its interior, with actual roots \(l,r,u,d>0\), \(l,r<\mu\), \(\mu>1\), satisfies \(u<1/2\) whenever \(h_C-d>\mu\).

Axis alignment has \(h_C=1\), so is impossible. Reflect horizontally if needed and take normals \((c,-s),(s,c)\), \(c\ge s>0\), \(c^2+s^2=1\), \(K=s/c\), support intervals \([\alpha,\alpha+1],[\beta,\beta+1]\), \(\alpha,\beta\in(-1,0)\). The actual lower root is \(d=\min((\alpha+1)/s,-\beta/c)\). If the first term is active, \(r\le Kd\le d\), so \(h_C-d\le l<\mu\), a contradiction. Hence the second is active, giving
\[
l\le d/K,\qquad cr+su\le1,\qquad ch_C\le1.\tag{3}
\]
Put \(R=1/c-\mu\). Then \(0<d<R\), and
\[
Ku\le1/c-r<R-d+l\le R-d+d/K\le R/K.
\]
Thus \(u<R/K^2<(1/c-1)/K^2=c/(1+c)<1/2\). This proves the lemma using the same tile's active supports.

Together with (2), every side-gap state with nonempty \(F\) horizontal section has \(u<1/2\). In fact the grid count only needs actual contact of \(C\) with one side line; a redundant side section can still be included in a covering upper bound and paired with its central vertical section. Thus any actual side contact under these residual hypotheses forces \(u<1/2\).

### 5. Under three joins, retain the floating length J

Now assume three joins and nonempty \(F\) horizontal section. Keep original \(W\), with \(A,D,H,J\ge0\),
\[
L_2+A\ge2\mu,\quad L_4+D\ge2\mu,\quad L_1+S_4\ge2\mu,
\quad A+D+H+J\le2.
\]
Combine \(b\ge2\mu-S_1-S_2,b+f\le B\) and \(h_C+f+U_1+U_2+H\ge2\mu\) to obtain
\[
h_C\ge8\mu-B-2-(L_2+S_2+U_2)-(L_4+S_1+U_1)+J.
\]
At the left join R13 gives \(L_4+S_1+a+2z-z^2\le2\). Its 266-coefficient historical dependency is explicitly retained. Since \(U_1<a,L_2+S_2+U_2<2\),
\[
h_C>1+2z-z^2+J.\tag{4}
\]
Upper-axis coverage gives
\[
u>1-z-J,\qquad h_C+u>2+z-z^2.\tag{5}
\]
Left joining gives \(0<z<4/15\). No cap \(J<\delta(z)\) is used.

### 6. Excluding the continuous large-z subclass

If \(z\ge1/7\), then \(z<4/15<1/2\) and \(h_C+u>104/49\). Since \(1<h_C<99/70\),
\(h_Cu>h_C(104/49-h_C)\). This concave quadratic has endpoint values \(55/49>1\) and \((99/70)(104/49-99/70)=34353/34300>1\). This contradicts (1), so
\[
0<z<1/7.\tag{6}
\]
This excludes only the indicated continuous subclass.

### 7. Small z requires a square-root-sized floating section

If \(J\le\sqrt z/3\), both lower bounds in (4)-(5) are positive, and
\[
h_Cu>(1+2z-z^2+J)(1-z-J).
\]
The right side decreases in \(J\). Put \(v=\sqrt z<1/\sqrt7<5/12\) and substitute \(J=v/3\). This gives \(h_Cu>1+zP(v)\), where
\[
P(v)=8/9-v-3v^2+v^3/3+v^4,
\quad P'\le-29/54<0,\quad P(5/12)=13/2304>0.
\]
Thus (1) is contradicted. Therefore
\[
J>\sqrt z/3,\qquad9J^2>z,\qquad z<9\delta(x)^2.\tag{7}
\]
The last inequality uses the correct right/vertical cap \(J<\delta(x)\). Replacing \(x\) by \(z\) would recreate the withdrawn false self-feedback. Also (5) and \(h_C<99/70\) give
\[
u>41/70>1/2.\tag{8}
\]
By Section 4, \(C\) therefore misses both side edges in this three-join state. If it met top, its top/horizontal pair and \(F\)'s bottom/horizontal pair, together with the central vertical union and corner grid, would give \(12\mu\le8+2B+2\mu<12\mu\). Thus it misses top too; bottom was already excluded. The three-join/nonempty-horizontal residual has \(C\) wholly disjoint from all four target edges.

### 8. Further position conditions for side-gap states

Top joining always gives \(H<\delta(z)\). In a side-gap/nonempty-horizontal state, \(u<1/2\) and upper-axis coverage imply \(J>1/2-z\). For a right gap, left joining gives \(z<4/15\), hence
\[
J>7/30,\qquad H<32/209.
\]
There is no cap \(J<\delta(x)\) when right has a gap. For a left gap, right joining does give that cap, so
\[
z+\delta(x)>1/2.
\]
There is no general \(z<4/15\) when left has a gap. The empty-horizontal case lacks the \(F\) bottom/horizontal pair and may allow \(C\) to meet bottom; none of these height or bottom-angle conclusions transfers to it.

Finally, a side-gap/nonempty-horizontal state cannot have \(C\) meet top: its side/vertical and top/horizontal pairs plus \(F\)'s bottom/horizontal pair and effective lower-axis contribution \(\mu-d\) would give \(12\mu\le8+3B+\mu-d<12\mu\). Thus every nonempty-horizontal residual has \(C\) disjoint from top/bottom; in a side-gap state it meets only the corresponding side, and in a three-join state it meets no outer edge.

<a id="R31"></a>
## R31. Excluding far three joins with a nonempty F horizontal section

**Scope.** Far hosts \(V_1,V_2,V_4\) are left, right, top; original \(W=V_3\) is free. The actual \(C\) uniquely contains the center and no outer midpoint; \(F\) contains the bottom midpoint but not the center. Assume all three nonbottom edges joined and \(F\)'s horizontal section nonempty, including tangency. Only valid top/horizontal and right/vertical parallel pairs are used.

### 1. Valid three-join inputs

For anchored angles \(a,x,z\), the parameters satisfy \(U_i<t_i,L_i+S_i+U_i<2\). Write \(h_C=l+r\) for \(C\)'s actual full horizontal length and \(u\) for its upper reach. The original \(W\) has right/top legs \(A,D\) and horizontal/positive-vertical lengths \(H,J\). R30 gives
\[
0<z<1/7,\quad J>0,\quad9J^2>z,\quad
h_C>1+2z-z^2+J,\quad h_C+u^2\le2.\tag{1}
\]
It also makes \(C\) disjoint from all four outer edges. The whole bottom gap, including endpoints, belongs to \(F\), whose actual bottom/horizontal lengths satisfy
\[
b\ge2\mu-S_1-S_2,\quad b+f\le B_\mu<1.\tag{2}
\]
The three joins are
\[
L_1+S_4\ge2\mu,\quad L_2+A\ge2\mu,\quad L_4+D\ge2\mu.\tag{3}
\]

### 2. The original W must take both upper axial bridge endpoints

Let \(Q_U=(0,\mu-U_4)\). If \(Q_U\in C\), then \(u>1-z\), and (1) gives \(h_C+u^2>2+J>2\). Hence it is outside \(C\). Only \(C,V_4,W\) meet the positive vertical half-axis. A true gap separates their central and top-host intervals, and closedness forces
\[
Q_U,(0,u)\in W,\qquad u<\mu-U_4.\tag{4}
\]
Nonemptiness of a section alone would not establish these endpoint memberships.

### 3. A dominating form for W and its actual position

In inward coordinates \(X=\mu-x,Y=\mu-y\), choose a positive-quadrant normal and shift only its projection interval to \([0,1]\), leaving the other interval \([-\beta,1-\beta]\). The corner makes the old lower bound nonpositive and upper bound at most one; the inward quadrant already has nonnegative projection. Thus this individual replacement preserves every old target point.

If it creates right-midpoint membership, reselect hosts and reflect to the excluded near representative (R28). If it creates top-midpoint membership, use the duplicate-top-host exclusion R29N Section 4. Both exclusions precede and avoid the withdrawn caps. All other branches retain neither midpoint. Keep the name \(W\) for the surviving dominating tile, with \(C,F\) and the anchored hosts unchanged; recompute (1)-(4) on this family. Its form is
\[
0\le cX+sY\le1,\quad-\beta\le-sX+cY\le1-\beta,
\quad c,s>0,\quad c^2+s^2=1.
\]
Positive \(J\) excludes axis alignment and gives \(c\mu<1\). The missing top midpoint gives actual \(D=\beta/s<\mu\), and nonempty \(J\) forces actual \(A=(1-\beta)/c<\mu\). Therefore
\[
sD+cA=1,\quad Y_{\min}=s(\mu-D)/c>0,\quad
Y_{\max}=(1-c\mu)/s<\mu.
\]
With \(K_\mu=(c+s-\mu)/(cs)<1\),
\[
J=Y_{\max}-Y_{\min}=K_\mu-A>0.\tag{5}
\]
If the horizontal central section is nonempty, including tangency, its actual endpoints are in the target and
\[
H=K_\mu-D\ge0.\tag{6}
\]
Equation (6) is not used as a nonempty-section identity when that section is empty.

### 4. The upper endpoint and right join force c greater than s

The second lower support at \(Q_U\) gives \(s(\mu-D)\le cU_4\). Using \(sD+cA=1\),
\[
A\le(1-s\mu)/c+U_4<(1-s)/c+z=c/(1+s)+z.\tag{7}
\]
Right joining and \(L_2\le\sqrt2<17/12\) give \(A>7/12\). If \(c\le s\), then \(c/(1+s)\le\sqrt2-1<5/12\), so \(A<47/84<7/12\), impossible. Hence
\[
c>s,\quad c>1/2,\quad t=s/(1+c)<\sqrt2-1<5/12.\tag{8}
\]
Top joining and \(L_4\le1+\delta(z)\) give
\[
D>1-\delta(z)>23/24.\tag{9}
\]

### 5. The horizontal central section of W is completely empty

If it were nonempty, (5)-(6) and \(sD+cA=1\) would give
\[
cJ+sH=(c+s)K_\mu-1<1-K_\mu,
\]
because \(2-(1+c+s)K_\mu=(1+c+s)(\mu-1)/(cs)>0\). Thus, using \(H\ge0,K_\mu=D+H\ge D,c>1/2\),
\(J<2(1-K_\mu)\le2(1-D)<2\delta(z)\). But for \(0<z<1/7\), \(2\delta(z)<\sqrt z/3\): with \(v=\sqrt z<2/5\), this is \(v^4+12v^3<1\), bounded by \(496/625<1\). This violates (1). Consequently
\[
W\cap\{y=0\}=\varnothing,\qquad H=0.\tag{10}
\]
Tangency has been excluded too; \(F\)'s section remains nonempty.

### 6. An extended adjacent-corner lemma

Use \(\lambda(y)=2y/(1-y^2),b(y)=(1+y^2)/(1-y^2)\). Let an anchored corner have angle \(x\in(0,1)\), \(L\ge1\), the two projection caps, and \(S=b(x)-\lambda(x)L\). Let another corner have \(0<t\le\sqrt2-1\), \(23/24\le D\le1\), \(A=b(t)-\lambda(t)D\). If \(L+A\ge2\), then
\[
D+S+x+2t-t^2\le2.\tag{11}
\]
To describe its full certificate domain, set \(\chi=(L-1)/(3-L)\). Joining is equivalent to
\[
(1-t)[(L-1)-(3-L)t]+2t(1-D)\ge0.
\]
Since \(L\le\sqrt2<17/12,t<5/12,1-D\le1/24\),
\(t\le\chi+(12/133)t\), hence \(t\le(133/121)\chi<(11/10)\chi\). The two valid cap domains are
\[
0<x\le2/5:\ \chi\le Y_c=\frac{x^2}{1-2x^2},\qquad
2/5\le x<1:\ \chi\le Y_s=\frac{(1-x)^2}{6x-1-x^2}.\tag{12}
\]
Define
\[
F_1=1-\lambda(x)\lambda(t)+b(x)-2\lambda(x)+\lambda(x)b(t)+x+2t-t^2,
\]
\[
P=(2-F_1)(1-x^2)(1-t^2),\quad Q=(1-x^2)(1-t^2)-4xt.
\]
Substitute \(x=2v/5,t=(11/10)Y_c(x)w\), or \(x=2/5+3v/5,t=(11/10)Y_s(x)w\), \(0\le v,w\le1\), and clear the positive \(Y\)-denominator powers. Each region has degrees \((11,4)\) for \(P\), \((6,2)\) for \(Q\). All 60+21 Bernstein coefficients per region are nonnegative, 162 in total. The minima for \(P\) are zero; for \(Q\) they are \(267044/15625\) in the first region and zero in the second. The source checker reconstructs all four polynomials, the full Bernstein identities and each sign. This proves \(F_1\le2,1-\lambda(x)\lambda(t)\ge0\) throughout the enlarged domain.

Finally joining gives \(L\ge2-b(t)+\lambda(t)D\), so
\[
D+S+x+2t-t^2
\le[1-\lambda(x)\lambda(t)]D+b(x)-2\lambda(x)+\lambda(x)b(t)+x+2t-t^2
\le F_1\le2.
\]
The second step uses \(D\le1\) and the established coefficient sign.

### 7. Two adjacent budgets and an envelope of actual endpoints

At the left join R13 gives \(L_4+S_1+a+2z-z^2\le2\). At the right join, if \(D\ge1\), R13's original lemma applies to the actual two-projection and short-leg constraints of \(W\); if \(23/24<D<1\), Section 6 applies. Both give \(D+S_2+x+2t-t^2\le2\). This does not misidentify a free top leg below one as a midpoint-anchored long leg.

By (10), horizontal coverage and (2) give \(h_C\ge4\mu-B_\mu-S_1-S_2-U_1-U_2\). With \(U_1<a,U_2<x,L_4+D\ge2\mu\),
\[
h_C>1+2z-z^2+2t-t^2.\tag{13}
\]
On the positive vertical axis, all \(V_4\) points have inward depth at most \(U_4\), and all \(W\) points at most \(Y_{\max}\). Their union lies in the envelope \([0,M]\), \(M=\max(U_4,Y_{\max})\); this does not give \(W\) a shared root or use \(\max(J,U_4)\). Since \(Y_{\max}<(1-c)/s=t,U_4<z\),
\[
u\ge\mu-M>1-\max(z,t).\tag{14}
\]
For \(m=\max(z,t),n=\min(z,t)>0\), (13)-(14) imply
\(h_C+u^2>1+2m-m^2+2n-n^2+(1-m)^2=2+2n-n^2>2\), contrary to (1). This closes the far three-join/nonempty-horizontal branch.

<a id="R32"></a>
## R32. Excluding a right gap with a positive F horizontal section

**Scope.** In the far family \(V_1,V_2,V_4\) host left, right, top; original \(W=V_3\) is free. The same \(C\) uniquely contains the center and no midpoint; \(F\) contains the bottom midpoint but not the center. A true right gap, including both endpoints, belongs to \(C\); left/top are joined. Assume a positive nonempty horizontal section of \(F\), including tangency. All roots and legs refer to actual tiles.

### 1. Valid geometric inputs

R30's corrected grid and active-support lemma give
\[
h_C-d>\mu,\quad u<1/2,\quad C\text{ misses top and bottom}.\tag{1}
\]
The actual roots satisfy \(0<l,r,u,d<\mu\). The bottom gap belongs wholly to \(F\), and its full bottom/horizontal lengths satisfy
\[
b\ge2\mu-S_1-S_2,\quad b+f\le B_\mu<1,\quad S_1+S_2>1.\tag{2}
\]
The right-gap endpoints are
\[
Q=(\mu,L_2-\mu)\in C,\quad P=(\mu,e)\in C,\quad e=\mu-A>0.\tag{3}
\]
Here \(A<\mu\) is the original right leg of \(W\), by R28's host-reselection exclusion of the whole near family.

### 2. Positive central rotation is impossible

For normals \((c,s),(-s,c)\), \(c\ge s>0\), write actual intervals \([\alpha,\alpha+1],[\beta,\beta+1]\), with \(\alpha,\beta\in(-1,0)\). The missing right midpoint and present point \(P\) force exclusion of that midpoint by the second lower support. Thus \(r=-\beta/s<\mu\), \(d=\min(-\alpha/s,-\beta/c)\). Put \(K=s/c\). If the first term is active, \(l\le Kd\le d\), contrary to \(h_C-d>\mu\). Otherwise \(d=Kr\). The first upper support at \(P\) gives \(l\le1/c-\mu-Ke<1/c-\mu\). Hence
\[
h_C-d<1/c-\mu+(1-K)r\le1/c-K\mu<1/c-K=(1-s)/c<1,
\]
again impossible. Axis alignment cannot contain both the center and a right-edge point. This sign exclusion used no positive/negative choice for \(F\)'s nonempty section; reflecting \(C\)'s point set also excludes negative central rotation in a left-gap/nonempty-horizontal state.

### 3. Actual supports for negative central rotation

Now use \((c,-s),(s,c)\), \(\eta=s/(1+c)\), \(K=s/c=\lambda(\eta)\le1\), \(G=g(\eta)\). The lower root is \(d=\min((\alpha+1)/s,-\beta/c)\). The first active term would give \(r\le Kd\le d\), impossible, so \(d=-\beta/c\). From \(ch_C\le1\) and (1), \(d<1/c-\mu\), making the second upper-axis support \(1/c-d>\mu\). Since \(C\) misses the top midpoint, its actual upper root must activate the first lower support: \(\alpha=-su\). Thus
\[
l=\min(Ku,d/K),\quad l\le Ku,\quad0<l<1/2.\tag{4}
\]
In particular \(\eta\le\sqrt2-1<5/12\). Put \(w=u-\eta\), not yet assumed positive. Projections of the two actual right-gap endpoints give
\[
c\mu-s(L_2-\mu)\le1-su,\qquad L_2>1+w,\tag{5}
\]
\[
s\mu+c(e+d)\le1,\qquad e+d<G.\tag{6}
\]
No near-family cascade or positive-excess assumption has been imported.

### 4. Positive F section forces a direct left join

Only \(C,V_1\) cover the negative horizontal axis: \(F\) is positive, \(W\) cannot reach that half-axis by diameter, and the top host misses the horizontal line. Thus \(l\ge\mu-U_1>1-a\), with \(a=t_1>1-l>1/2\), giving
\[
S_1<q(l).\tag{7}
\]
Left joining and the sine cap yield \(z=t_4<Y_s(a)\), where
\(Y_s'(a)=4(a^2-1)/(6a-1-a^2)^2<0\). Consequently
\[
z<Y_s(1-l)=\frac{l^2}{4-4l-l^2}<\frac47l^2<\frac27u.\tag{8}
\]
The denominator exceeds \(7/4\) since \(l<1/2\), and \(l\le Ku\le u<1/2\). Thus \(z<1/7\).

### 5. The same bottom long leg controls the central height

If \(w\le0\), then \(u\le\eta<9\eta/7\). If \(w>0\), (5) and \(L_2\le\sqrt2\) give \(0<w<\sqrt2-1\), so R28 gives \(S_2\le\Phi(w)=(1+w)(1-\sqrt{w(2+w)})\). For any \(w>0\),
\[
1-\Phi(w)>\sqrt w,\tag{9}
\]
because the equivalent comparison \((1+w)\sqrt{2+w}>1+\sqrt w\) has positive sides and square difference
\((1-\sqrt w)^2+3w+4w^2+w^3>0\). Equations (2), (7) imply \(\sqrt w<q(l)\), so
\(w<q(l)^2<4l^2/9\le4K^2u^2/9<2u/9\). Since \(u=\eta+w\), both signs of \(w\) give
\[
u<9\eta/7.\tag{10}
\]
With (8) and \(q(u)<2u/3\),
\[
z+q(u)<(2/7+2/3)u<\frac{60}{49}\eta
<\frac{24}{17}\eta<\frac{2\eta}{1+\eta}=1-G.\tag{11}
\]
The constant difference is \(156/833>0\), and the last inequality uses \(\eta<5/12\).

### 6. The original W bridge forces the reverse inequality

Since \(u<1/2,z<1/7\), \(Q_U=(0,\mu-U_4)\notin C\). Only \(C,V_4,W\) meet the positive vertical half-axis, so original \(W\) contains both actual bridge endpoints \((0,u),Q_U\). No normalization of \(W\) is needed. In inward coordinates choose a positive normal \((c_W,s_W)\), with other interval \([-\beta_W,1-\beta_W]\). Axis alignment cannot span \(\mu>1\). The corner bounds the first upper projection by one, so
\(c_W\mu+s_W(\mu-u)\le1\). For \(T=(1-c_W)/s_W\in(0,1)\), this gives \(T>1-u\). The second lower support at \(Q_U\) gives \(\beta_W\ge s_W\mu-c_WU_4\), and the actual right leg therefore obeys
\[
A\le\frac{1-\beta_W}{c_W}\le\frac{1-s_W\mu}{c_W}+U_4
<g(T)+U_4<q(u)+U_4<q(u)+z.\tag{12}
\]
Thus \(e=\mu-A>1-z-q(u)>G\), by (11), contradicting (6). The full positive-horizontal right-gap branch, including tangency, is excluded without rooting \(W\)'s floating vertical section.

### 7. A conditional duplicate-midpoint exclusion on the left

If a left-gap/negative-horizontal family had original \(W\) containing the top midpoint, reselect it as top host, keep the side hosts, and reflect horizontally. This becomes exactly the excluded right-gap/positive-horizontal family. Thus that duplicate-top-midpoint subclass is also excluded. The argument does not discard left-gap families whose original \(W\) lacks the top midpoint.

<a id="R33"></a>
## R33. Excluding every right gap with a nonempty F horizontal section

**Scope.** Retain R32's actual far right-gap family, with left/top joined and a nonempty horizontal section of \(F\). R32 already excludes positive central rotation and the positive-horizontal case. Here \(C\) has negative normals \((c,-s),(s,c)\), \(0<s\le c\). This module completes the negative-horizontal case, including tangency.

### 1. Actual endpoints and a necessary bridge inequality

Use
\[
\eta=s/(1+c),\quad K=\lambda(\eta),\quad G=g(\eta),\quad
0<\eta\le\sqrt2-1<29/70.
\]
The same actual \(C\) satisfies \(0<u<1/2,l\le Ku,h_C-d>\mu\). Both right-gap endpoints give
\[
L_2>1+w,\quad w=u-\eta,\qquad e+d<G,\quad e=\mu-A.\tag{1}
\]
The actual bottom legs satisfy \(\Sigma=S_1+S_2>1\). For \(a=t_1,z=t_4\), left joining and \(L_1\le\sqrt2<99/70\) give
\[
z<29/111<4/15.\tag{2}
\]
Thus \(Q_U=(0,\mu-U_4)\) lies above \(u\), and the original \(W\) bridge proof of R32 applies using only \(u<1/2,z<1/2\). It gives \(A<U_4+q(u)<z+q(u)\). Together with (1),
\[
z+q(u)>1-G+d>1-G.\tag{3}
\]

### 2. The same F bridges the left axis and bottom

If \(C\) contained the actual left-host inner endpoint \(Q_L=(-\mu+U_1,0)\), R32 Sections 4-6 would apply without needing positive \(F\), giving a contradiction. Hence the residual has \(l<p=\mu-U_1\). Only \(C,V_1,F\) meet the negative horizontal axis, so the same original \(F\) contains \(Q_L\) and \(C\)'s left endpoint. Its full horizontal length is at least \(p-l>1-a-l\). Its full bottom length is at least \(2\mu-\Sigma\), so the actual nonempty parallel pair gives
\[
\Sigma>2-a-l.\tag{4}
\]
Set \(\rho_a=a(1-a)/(1+a)>0\). Since \(S_1<g(a),S_2<1\) and \(1-a-g(a)=\rho_a\),
\[
\rho_a<l\le Ku.\tag{5}
\]
If \(w>0\), then \(0<w<\sqrt2-1\) by (1) and diameter, so \(S_2\le\Phi(w)\). Equation (4) gives
\[
1-\Phi(w)<l-\rho_a.\tag{6}
\]
All these constraints couple actual sections of the same original \(F\).

### 3. Two explicit continuous bounds

For any \(w>0\),
\[
1-\Phi(w)>\frac54\sqrt w.\tag{7}
\]
Writing \(v=\sqrt w\), the equivalent positive-side comparison \((1+w)\sqrt{2+w}>5/4+\sqrt w\) has square difference
\(4(v-5/16)^2+3/64+4v^4+v^6>0\). Therefore, when \(w>0\),
\[
\rho_a+5v/4<l\le Ku,\quad u=\eta+v^2,\quad0<v<(4/5)Ku<2/5.\tag{8}
\]
For all \(a\in(0,1)\), left joining also gives
\[
z<\frac85\rho_a.\tag{9}
\]
For \(a\le5/12\), use \(Y_c=a^2/(1-2a^2)\); the difference has positive numerator \(a(8-13a-21a^2+16a^3)\), whose parenthesis decreases to \(41/432>0\). For \(a\ge5/12\), use \(Y_s=(1-a)^2/(6a-1-a^2)\); the numerator is \((1-a)(-8a^3+53a^2-8a-5)\), whose parenthesis increases from \(125/432>0\). Both denominators are positive in their full stated intervals.

### 4. A scalar lemma on the complete continuous domain

Let \(0<\eta\le\sqrt2-1,K=\lambda(\eta),0<u<1/2,0<z<Z=29/111\). If either \(u\le\eta,z<(8/5)Ku\), or \(u=\eta+v^2,0<v<2/5,z<(8/5)Ku-2v\), then
\[
z+q(u)<\frac{2\eta}{1+\eta}=1-G.\tag{10}
\]
For its proof define
\[
A_0=\frac{16\eta^2}{5(1-\eta^2)},\quad
R=\frac{2\eta}{1+\eta}-q(\eta)=\frac{3\eta(1-\eta)}{(1+\eta)(2-\eta)},\quad D=A_0-R.
\]
The sign of \(D\) is that of \(-15+62\eta-31\eta^2\), so \(D<0\) for \(\eta\le7/25\). Above this point \(A_0'>224/125>1>R'\), so \(D\) increases; also \(R'>0,R''<0,A_0''>0,D''>0\). At \(b=29/70\),
\[
D(7/25)=-77/30960,\quad D(b)=84709/250305<31/90,
\quad31/90-D(b)=9043/1501830.\tag{11}
\]
Thus \(D\) has one zero \(\eta_0\in(7/25,b)\). Where \(D>0\),
\[
R>Z,\qquad R(7/25)-Z=1027/76368>0.\tag{12}
\]
There \(T=R-(450/961)D^2\) is strictly concave, since
\(T''=R''-(900/961)((D')^2+DD'')<0\). At \(\eta_0\), \(T=R>Z\); at \(b\),
\(T(b)-Z=23375336726/2408365675881>0\). Hence throughout that interval,
\[
R>Z+(450/961)D^2.\tag{13}
\]
If \(u\le\eta\), then \(z+q(u)<q(\eta)+\min(Z,A_0)\). For \(D\le0\), use \(A_0\le R\); for \(D>0\), use \(Z<R\), proving (10).

For \(u=\eta+v^2\), put \(f(v)=(8/5)K(\eta+v^2)-2v+q(\eta+v^2)\). On its actual domain \(\eta+v^2<1/2,0\le v\le2/5\),
\[
f'(v)=\left(\frac{16}5K+\frac4{(2-\eta-v^2)^2}\right)v-2
\le\frac{224}{45}v-2\le-2/225<0,
\]
and
\[
q(\eta+v^2)-q(\eta)=\frac{2v^2}{(2-\eta-v^2)(2-\eta)}<8v^2/9.\tag{14}
\]
If \(D\le0\), monotonicity gives \(f(v)<f(0)=q(\eta)+A_0\le q(\eta)+R\). If \(D>0,v\ge1/4\), the actual domain also permits \(v=1/4\), and (14) gives \(f(v)\le f(1/4)<q(\eta)+A_0-31/90<q(\eta)+R\). Finally suppose \(D>0,v<1/4\). Then \(f(v)<q(\eta)+A_0-(62/45)v\). For \(v\ge(45/62)D\), this suffices. Otherwise use the genuine bound \(z<Z\), (13), (14):
\[
z+q(u)<Z+q(\eta)+\frac89(45D/62)^2
=q(\eta)+Z+\frac{450}{961}D^2<q(\eta)+R.
\]
This exhausts the domain and proves (10).

### 5. Closing the right nonempty-horizontal family

When \(w\le0\), (5), (9) give the scalar lemma's first case. When \(w>0\), (8), (9) give \(z<(8/5)\rho_a<(8/5)Ku-2v\), its second case. Thus (10) always contradicts the actual endpoint requirement (3). The negative-horizontal right-gap case is excluded; R32 supplies the positive case, so every right-gap/nonempty-horizontal family is closed.

If a left-gap/nonempty-horizontal family had original \(W\) at the top midpoint, reselect it as top host and reflect horizontally to this excluded right-gap family. Thus that \(W\) also cannot duplicate the top midpoint, and R28 already excludes the right midpoint. The precise residual families at this stage are: nonempty \(F\) horizontal section with a left gap, positive central rotation, and \(W\) owning no midpoint; or empty \(F\) horizontal section with a left gap, right gap, or three joins. The latter may have bottom contact of \(C\), so neither \(u<1/2\) nor nonempty-horizontal budgets may be transferred. The new chain here does not use R13's adjacent certificate, while R31 and the global historical argument retain their own dependencies.

<a id="R34"></a>
## R34. Excluding a left gap with a negative F horizontal section

**Scope.** Far hosts \(V_1,V_2,V_4\) are left, right, top; original \(W=V_3\) is free. The actual \(C\) contains the center but no outer midpoint; \(F\) contains the bottom midpoint but not the center. Left has a true gap; right/top are joined. Retain \(C,F,W\). The nonempty-horizontal hypotheses give \(C\) positive rotation and its actual support identities below. The exclusion includes tangent negative sections of \(F\).

### 1. Actual supports in the left-gap family

For \(\eta=s/(1+c)\), \(K=\lambda(\eta)\), \(G=g(\eta)\),
\[
0<u<1/2,\quad r\le Ku\le u,\quad K\le1,\quad
0<\eta\le\sqrt2-1<5/12.\tag{1}
\]
Indeed, for positive normals \((c,s),(-s,c)\) with intervals \([\alpha,\alpha+1],[\beta,\beta+1]\), the inequality \(h_C-d>\mu\) excludes the active lower root \(-\alpha/s\), since it would give \(l\le Kd\le d\). Thus \(d=-\beta/c\). The horizontal cap \(ch_C\le1\) gives \(d<1/c-\mu\); the second upper root is beyond \(\mu\), so absence of the top midpoint makes the first upper root active, \(\alpha=su-1\). Hence \(r=\min(Ku,d/K)\).

For \(a=t_1,x=t_2,z=t_4\), both actual left-gap endpoints yield
\[
L_1>1+w,\quad w=u-\eta,\qquad e+d<G,\quad e=\mu-S_4.
\]
Since \(S_4<g(z)\),
\[
z<q(G)=\frac{1-\eta}{1+3\eta}.\tag{2}
\]
Nonempty \(F\) horizontal section makes \(C\) miss bottom; the actual two-section budget gives \(\Sigma=S_1+S_2>1\). Let \(Q_R=(\mu-U_2,0),Q_U=(0,\mu-U_4)\), and let \(R_C=(r,0),U_C=(0,u)\) be actual endpoints.

### 2. An original corner tile cannot contain both short positive endpoints

Any unit square containing \((\mu,\mu),(r,0),(0,u)\), \(\mu>1\), satisfies
\[
r+u>\mu.\tag{3}
\]
For a positive inward unit normal \((c_W,s_W)\), the corner bounds its upper projection by one. The two points give \(c_Wr\ge(c_W+s_W)\mu-1\), \(s_Wu\ge(c_W+s_W)\mu-1\), so
\[
r+u-\mu\ge\frac{(\mu-1)(1+c_Ws_W)+(1-c_W)(1-s_W)}{c_Ws_W}>0.
\]
Axis alignment cannot span \(\mu>1\) to the other axis and is separately excluded. But (1) gives \(r+u<1<\mu\); therefore original \(W\) cannot contain both \(R_C,U_C\). No common origin of its sections is assumed.

### 3. C cannot directly reach the right inner endpoint

This step is valid for either horizontal sign of \(F\). Suppose \(Q_R\in C\). Then \(r>1-x\), \(x>1-r>1/2\). The same \(V_2\) gives
\[
S_2<g(x)<q(r),\quad L_2-1\le\frac{(1-x)^2}{2x}<\Delta(r),
\quad\Delta(v)=\frac{v^2}{2(1-v)}.\tag{4}
\]
If \(w>0\), the valid domain \(L_1>1+w,L_1\le\sqrt2\) permits \(S_1\le\Phi(w)\). Then \(\Sigma>1\) gives \(\sqrt w<q(r)<2r/3\), exactly as in R32; if \(w\le0\), directly use \(u\le\eta\). Both cases give
\[
u<9\eta/7.\tag{5}
\]
If \(Q_U\in C\), then \(z>1-u\), and (2) gives \(u>4\eta/(1+3\eta)>16\eta/9>9\eta/7\), impossible. Otherwise original \(W\) bridges the true upper axial gap and contains \(U_C,Q_U\). The actual bridge lemma gives \(A<U_4+q(u)<z+q(u)\). Right joining and (4) give \(A\ge2\mu-L_2>1-\Delta(r)\), hence
\[
1<z+q(u)+\Delta(r).\tag{6}
\]
But \(r\le u<1/2\), (5), and \(\Delta(r)<r^2\) give \(q(u)<6\eta/7\), \(\Delta(r)<9\eta/14\). Therefore the right side is below \((1-\eta)/(1+3\eta)+3\eta/2<1\), since \(4/(1+3\eta)>16/9>3/2\). Thus \(Q_R\notin C\), irrespective of the horizontal sign of \(F\).

### 4. Negative F section forces an impossible double bridge

Now \(F\) has no positive horizontal contribution. Only \(C,V_2,W\) cover that half-axis. Since \(Q_R\notin C\), original \(W\) contains both \(R_C,Q_R\). By (3) it misses \(U_C\); only \(C,V_4,W\) cover the upper half-axis, so closed coverage forces \(C\) to contain \(Q_U\). Consequently
\[
z>1-u,\quad u>\frac{4\eta}{1+3\eta},\quad
\eta<\frac{u}{4-3u}<\frac25u<1/5.\tag{7}
\]
Combining with (1),
\[
K<5u/6,\quad r<5u^2/6,\quad q(r)<5u^2/9.\tag{8}
\]
Here \(1-\eta^2>24/25\) and \(q(r)<2r/3\). Also \(w=u-\eta>3u/5>u^2>0\). The actual long-leg bound and \(\Sigma>1\) give \(S_2>1-S_1\ge1-\Phi(w)>\sqrt w>u\). Hence
\[
x<g(u).\tag{9}
\]
The horizontal bridge \(R_C,Q_R\) of original \(W\), obtained by interchanging coordinates in the vertical bridge lemma, gives its actual **top leg**, not a root length,
\[
D<U_2+q(r)<x+q(r).\tag{10}
\]
Since \(z>1-u>1/2\), the top host's long-leg projection gives \(L_4-1\le(1-z)^2/(2z)<\Delta(u)\). Top joining then requires \(D>1-\Delta(u)\), so
\[
1<x+q(r)+\Delta(u).\tag{11}
\]
Yet (8)-(9) and \(u<1/2\) bound this by \(g(u)+5u^2/9+u^2<g(u)+7u/9<1\), since \(1-g(u)=2u/(1+u)>4u/3>7u/9\). This contradiction excludes the entire left-gap/negative-horizontal family, including a single tangent point.

<a id="R35"></a>
## R35. The last nonempty-horizontal family requires a two-tile relay

**Scope.** Treat only the residual left-gap/positive-horizontal family of R34. Keep actual \(C,F,W\). The central tile has positive rotation, \(0<u<1/2,r\le Ku\), \(K=\lambda(\eta)\le1\), \(z<q(G)=(1-\eta)/(1+3\eta)\), and does not contain the right-host horizontal endpoint \(Q_R\). Original \(W\) cannot contain both actual endpoints \(R_C=(r,0),U_C=(0,u)\). This module forces a relay; R36 supplies the final exclusion.

### 1. The same original F cannot contain both right axial gap endpoints

Suppose \(R_C,Q_R\in F\). It also contains both bottom-gap endpoints. Its actual nonempty bottom/horizontal parallel sections give
\[
\Sigma>2-x-r,\qquad \rho_x:=\frac{x(1-x)}{1+x}<r\le Ku.
\]
If \(w=u-\eta>0\), the actual long leg \(L_1>1+w\) permits \(S_1\le\Phi(w)\), while \(S_2<g(x)\). Thus
\[
1-\Phi(w)<r-\rho_x,\qquad \rho_x+5\sqrt w/4<r\le Ku.
\]
If \(Q_U\in C\), R34 gives \(\eta<2u/5,r<5u^2/6,w>u^2\). The loss is then above \(\sqrt w>u\), while \(r<u\), impossible. Hence \(Q_U\notin C\), and original \(W\) actually bridges \(U_C,Q_U\), giving \(A<z+q(u)\).

Define the local angle cap \(\chi=(L_2-1)/(3-L_2)>0\). The two anchored projection caps give
\[
\chi<Z=29/111,\qquad\chi<8\rho_x/5.
\]
The second statement is exactly R33 Section 3.2's two-domain cap proof, with no left-join premise. Thus for \(w\le0\), \(\chi<(8/5)Ku\); for \(w>0\), writing \(v=\sqrt w\),
\[
u=\eta+v^2,\quad0<v<2/5,\qquad\chi<(8/5)Ku-2v.
\]
Right joining requires \(A\ge2\mu-L_2>2-L_2=g(\chi)\). Consequently the actual bridge and top-angle cap require
\[
g(\chi)<q(G)+q(u).\tag{*}
\]

### 2. A full-domain scalar proof of the opposite inequality

Under these conditions, in fact \(g(\chi)>q(G)+q(u)\). Put
\[
A_0=\frac{16\eta^2}{5(1-\eta^2)},\quad
B(v)=\frac85K(\eta+v^2)-2v,\quad M(\eta)=q(G)+q(\eta).
\]
The derivative \(M'=-4/(1+3\eta)^2+2/(2-\eta)^2\le0\) is equivalent to \(\eta^2+2\eta\le1\). Also \(q(\eta+v^2)-q(\eta)<8v^2/9\), and \(B'<0\) on the actual \(0<v<2/5,u<1/2\) domain. When \(0<B\le3/10\),
\[
\frac d{dv}\{g(B(v))-q(\eta+v^2)\}
=\frac{4-(32/5)Kv}{(1+B)^2}-\frac{4v}{(2-u)^2}
\ge144/169-32/45>0.
\]
The numerator of the first fraction is at least \(36/25\), its denominator at most \(169/100\), and the last term at most \(32/45\).

For \(0<\eta\le7/25\), \(A_0\le A_0(7/25)<3/10\), and
\[
g(A_0)-M=
\frac{\eta(19\eta^3-83\eta^2-99\eta+35)}{(2-\eta)(3\eta+1)(11\eta^2+5)}>0.
\]
The parenthesis decreases and is positive at \(7/25\). For \(w\le0\), use \(\chi<A_0,u\le\eta\). For \(w>0\), the derivative bound lifts the zero-endpoint inequality to \(v>0\).

For \(7/25\le\eta\le3/8\), set \(v_*=3/16\). If \(v\le v_*\), the true cap \(\chi<Z\) and monotonicity of \(M\) give
\[
g(\chi)-q(G)-q(u)>41/70-M(7/25)-1/32=409/1107680>0.
\]
If \(v>v_*\), feasibility \(B(v)>\chi>0\) gives \(B(v_*)>0\), and
\[
B(v_*)\le\frac85\frac{48}{55}(3/8+9/256)-3/8
=Z-3103/48840<Z<3/10.
\]
At the threshold the same cap has positive margin; thereafter apply the derivative bound.

For \(3/8\le\eta\le\sqrt2-1<29/70\), use \(v_*=13/50\). Below it,
\[
g(\chi)-q(G)-q(u)>41/70-M(3/8)-(8/9)(13/50)^2
=12853/17403750>0.
\]
Above it, feasibility again gives \(B(v_*)>0\), while
\[
B(v_*)<\frac85(29/70+169/2500)-13/25
=Z-24874/2428125<Z<3/10,
\]
and the same derivative bound applies. Nonpositive \(w\) in the middle/large \(\eta\) ranges only needs \(g(Z)>M(7/25)\), with margin larger than the first threshold margin. Thus all continuous cases contradict (*).

### 3. Consequences and the exhaustive relay classification

The preceding contradiction proves that original \(F\) cannot contain both \(R_C,Q_R\). If original \(W\) contained both, R34's two-positive-endpoint lemma would exclude \(U_C\) from \(W\); closed upper-axis coverage would force \(Q_U\in C\). R34 Section 4's top join, actual horizontal bridge, and bottom long-leg argument then gives a contradiction without any remaining negative-horizontal premise on \(F\). Thus \(W\) also cannot contain both endpoints.

Only \(F,W\) fill the actual positive horizontal gap \([r,q_R]\), where \(q_R=\mu-U_2>r\). Their full horizontal intervals \([f_0,f_1],[h_0,h_1]\) therefore have exactly one of the following orders:
\[
f_0\le r<h_0\le f_1<q_R\le h_1\quad\text{(F first)},
\]
\[
h_0\le r<f_0\le h_1<q_R\le f_1\quad\text{(W first)}.
\]
Equality at the common joining endpoints is allowed, as is overlap. Both sections have positive length: neither tile can span both endpoints, and a tangent point cannot by itself fill the remaining open interval. In particular an empty or singleton horizontal section of original \(W\) would force \(F\) to cover the full gap; a finite closed interval cover cannot leave only a single isolated uncovered interior point. That entire subclass is excluded.

The source records 20 UNSAT scalar queries (19 nonlinear, one linear), seven identities, and nine constant checks; endpoint ownership is audited separately. R35 is packaged with R36, with no separate R35 archive. Its output is the relay classification, not a standalone exclusion of all left-gap/positive-horizontal families. R36 closes those; empty-horizontal families continue in R37-R64.

<a id="R36"></a>
## R36. Excluding all nonempty F horizontal mechanisms

**Scope.** Keep original \(C,F,W\) in the last far left-gap/positive-horizontal family. Hosts \(V_1,V_2,V_4\) are left, right, top. The actual \(C\) uniquely contains the center but no midpoint; \(F\) contains the bottom midpoint, not the center. Right/top are joined. R34 gives positive central rotation, \(0<u<1/2,r\le Ku\), \(K=\lambda(\eta)\le1\), \(0<\eta\le\sqrt2-1<5/12\), and \(z<q(G)=(1-\eta)/(1+3\eta)\). Both top/bottom are disjoint from \(C\), and the actual right-host horizontal endpoint \(Q_R=(q_R,0)\), \(q_R=\mu-U_2>r\), is outside \(C\).

### 1. Actual relay endpoints and a joint F budget

Let \(U_C=(0,u),R_C=(r,0),Q_U=(0,\mu-U_4)\). R35 excludes either original \(F\) or \(W\) spanning \(R_C,Q_R\). The full horizontal intervals therefore have positive lengths and one of the orders
\[
\mathrm{I}:f_0\le r<h_0\le f_1<q_R\le h_1,
\qquad\mathrm{II}:h_0\le r<f_0\le h_1<q_R\le f_1.\tag{1}
\]
Closed joining and overlap remain allowed. Original \(W\) cannot contain both \(R_C,U_C\). For the same \(F\)'s actual bottom/horizontal lengths,
\[
b\ge2\mu-\Sigma,\quad b+f\le B_\mu<1,\qquad\Sigma=S_1+S_2>1+f.\tag{2}
\]
The actual left endpoints also give \(L_1>1+u-\eta\).

### 2. Both relay orders fail when C reaches the top-host endpoint

Suppose \(Q_U\in C\). R34 gives
\[
z>1-u,\quad\eta<2u/5<1/5,\quad r<5u^2/6,\quad q(r)<5u^2/9,
\quad w=u-\eta>u^2>0.\tag{3}
\]
The actual long leg validates \(S_1\le\Phi(w)<1-u\), hence
\[
\Sigma<1-u+g(x).\tag{4}
\]
Also \(L_4-1<\Delta(u)\), \(\Delta(v)=v^2/(2(1-v))\), and top joining forces the original top leg
\[
D>1-\Delta(u).\tag{5}
\]
In order I, \(f\ge h_0-r\), so (2)-(4) give
\[
h_0<r+g(x)-u<g(x)-t,\quad t=u-5u^2/6>0.\tag{6}
\]
Thus \(h_0<1,x<g(t)\). Original \(W\) contains \((h_0,0),Q_R\); its actual horizontal bridge bound gives \(D<U_2+q(h_0)<x+q(h_0)\). Hence
\[
1<x+q(h_0)+\Delta(u)<x+q(g(x)-t)+\Delta(u).\tag{7}
\]
On \(0\le x\le g(t)\), the convex function
\[
x+q(g(x)-t)=x+\frac{1-t-(1+t)x}{1+t+(3+t)x}\le g(t)\tag{8}
\]
has second derivative \(8(3+t)/[1+t+(3+t)x]^3>0\) and equal endpoint values \(g(t)\). Meanwhile \(t>7u/12,1+t<3/2\), so \(1-g(t)>7u/9\), while \(\Delta(u)<u^2<u/2\). Thus (7) is impossible.

In order II, original \(W\) contains \(R_C\) and its actual right horizontal endpoint \((h_1,0)\). The bridge projection gives \(D<\mu-h_1+q(r)\). Using top joining,
\[
h_1<L_4-\mu+q(r)<\Delta(u)+q(r)<14u^2/9<7u/9.\tag{9}
\]
But \(F\) contains \(Q_R\), and \(f_0\le h_1\), so \(f\ge q_R-h_1>1-x-h_1\). Equations (2), (4) imply \(h_1>u+1-x-g(x)=u+\rho_x>u\), contrary to (9). Thus the last nonempty-horizontal family cannot have \(Q_U\in C\).

### 3. The original W vertical bridge forces a stronger actual relay budget

Since \(Q_U\notin C\), only \(C,V_4,W\) cover the upper axis, forcing \(U_C,Q_U\in W\). The two-positive-endpoint lemma excludes \(R_C\) from \(W\), leaving only order I: \(R_C\in F,Q_R\in W,h_0\le f_1\).

For a positive inward unit normal \((c_W,s_W)\) of original \(W\), the corner bounds its first upper projection by one. Membership of \(U_C\) gives \(c_W\mu+s_W(\mu-u)\le1\), hence \(\tau=(1-c_W)/s_W>1-u\). Every actual horizontal point \((h,0)\in W\) satisfies \(c_W(\mu-h)+s_W\mu\le1\), so
\[
h>1-(1-s_W)/c_W=1-g(\tau)>1-q(u),\qquad h_0>1-q(u).\tag{10}
\]
The actual left endpoint, rather than its floating section length, now gives
\[
\Sigma>1+h_0-r>2-q(u)-r,
\qquad2-\Sigma<q(u)+r\le q(u)+Ku.\tag{11}
\]
The same \(W\)'s two vertical bridge endpoints give \(A<U_4+q(u)\). Right joining therefore yields \(L_2>2-z-q(u)>2-q(G)-q(u)\). Define actual long-leg excesses \(\epsilon_i=L_i-1\); then
\[
\epsilon_1>u-\eta,\quad\epsilon_2>\frac{4\eta}{1+3\eta}-q(u),
\quad0<\epsilon_i\le\sqrt2-1.\tag{12}
\]
Apply the fixed-long-leg short-leg bound to each of the same anchored tiles and R33's strong loss inequality:
\[
2-\Sigma>\frac54(\sqrt{\epsilon_1}+\sqrt{\epsilon_2})
>\frac54\sqrt{\epsilon_1+\epsilon_2}.\tag{13}
\]

### 4. A joint two-variable loss inequality on a full rectangle

For \(0\le\eta\le5/12,0\le u\le1/2\), put
\[
\mathcal E=u-\eta+\frac{4\eta}{1+3\eta}-q(u),\quad
\mathcal P=\mathcal E-\frac{16}{25}(q(u)+K(\eta)u)^2,
\quad K(\eta)=\frac{2\eta}{1-\eta^2}.
\]
For \(u>0\), \(\mathcal P>0\), in particular \(\mathcal E>0\). To prove this, use nonnegative increasing convex \(q,K\). With \(Y=q(u)+K(\eta)u\),
\[
\mathcal P_{uu}=-q''-\frac{32}{25}\{(q'+K)^2+Yq''\}<0,
\]
\[
\mathcal P_{\eta\eta}=-\frac{24}{(1+3\eta)^3}
-\frac{32}{25}\{(uK')^2+YuK''\}<0.
\]
Separate concavity bounds the function below by its bilinear vertex interpolant. Its exact vertex values are
\[
\mathcal P(0,0)=0,\quad\mathcal P(5/12,0)=35/108,
\quad\mathcal P(0,1/2)=43/450,
\quad\mathcal P(5/12,1/2)=1598333/38234700>0.
\]
When \(u>0\), the upper-edge vertices have total positive weight \(2u\); thus positivity is strict. This is a rectangle-wide concavity proof, not finite sampling. Applying it with (12),
\(\epsilon_1+\epsilon_2>\mathcal E>(16/25)(q(u)+Ku)^2\). Equation (13) gives \(2-\Sigma>q(u)+Ku\), contrary to (11). The remaining order I is excluded.

### 5. Completed nonempty-horizontal exclusion and exact residual scope

The two cases \(Q_U\in C\) and \(Q_U\notin C\) exhaust the last family. Section 2 closes both direct-join relay orders; Sections 3-4 close the bridge case. Together with R31's three joins, R32-R33's right gaps, and R34's left negative-horizontal case, every nonempty horizontal section of \(F\) is excluded. The output to R37-R64 is exactly the empty-horizontal left-gap, right-gap, and three-join families.

### 6. A new bottom-contact lemma for empty-horizontal side gaps

Any unit tile containing the center and a side-upper point \(P=(-\mu,e)\), \(\mu>1,e\ge0\), misses bottom. If it also contained \(B'=(p,-\mu)\), then for \(p\le0\), the triangle \(0,P,B'\) would have doubled area \(\mu^2-ep>1\). For \(p>0\), the squared distance \(|P-B'|^2=(\mu+p)^2+(\mu+e)^2>2\) violates diameter. Reflection gives the right-side version.

Thus in both empty-horizontal side-gap families, \(C\) still misses bottom, and the true bottom gap and its closed endpoints belong wholly to \(F\). This newly covers the empty-horizontal case, but it does not transfer nonempty-horizontal parallel budgets, the height bound \(u<1/2\), or rotation exclusions. The three-join family has no such forced side point and must retain possible bottom contact of \(C\).

<a id="R37"></a>
## R37. A global axial-root cap and two empty-horizontal side-gap rotation exclusions

**Scope.** The global root cap in Section 1 depends only on the prior exclusions of G5, center-owned-midpoint G2, G3 and G4, not on later gap exclusions. Sections 2-5 treat empty-horizontal left gaps with negative central rotation; Section 6 treats empty-horizontal right gaps with positive rotation. Section 7 supplies necessary constraints for the remaining left positive rotation. The source's missing-one failed candidate is explicitly withdrawn and is not used.

### 1. Every actual central axial root lies between mu minus one and two minus mu

The prior global inputs are: uniqueness of the center tile \(C\) after G5; the closed central square \([-(\mu-1),\mu-1]^2\subset C\) from R9 Section 7; and the exclusions in R12, R23, R25 establishing that, in **any** six-tile cover of a square of side above two, its center tile contains no outer midpoint. This is independent of how hosts or the remaining tile are reselected for another target.

Suppose the actual right root \(r>2-\mu\). Consider the inscribed square
\[
[-\mu,r]\times[-\nu,\nu],\qquad \nu=(\mu+r)/2>1,
\quad P=((r-\mu)/2,0).
\]
Since \(r<\mu\), \(\nu<\mu\), so this square is inside the target. Also \(|P_x|=(\mu-r)/2<\mu-1\), hence \(P\in C\). The same \(C\) contains its right midpoint \((r,0)\), violating the global no-midpoint theorem applied to this new square. Therefore, by rotation,
\[
\mu-1\le l,r,u,d\le2-\mu<1.\tag{1}
\]
For this application corner hosts may change; the original \(F\) need not retain its role. Only the globally quantified center-tile conclusion is used.

### 2. Actual supports for an empty-horizontal left gap with negative C

Far hosts \(V_1,V_2,V_4\) are left, right, top, original \(W=V_3\) is free, \(F\) contains the bottom midpoint and has completely empty horizontal section. A true left gap belongs to \(C\); right/top are joined. R36's side-point lemma excludes \(C\) from bottom. For the same actual \(F\), \(b\ge2\mu-\Sigma\), \(\Sigma=S_1+S_2\), and \(v\ge\mu-d\). Hence
\[
\Sigma\ge2\mu-2+(\mu-d)^2>(1-d)^2.\tag{2}
\]
The strict comparison uses \(d<1\). Actual nonempty left/central-vertical sections give
\[
u+d<1.\tag{3}
\]
Empty \(F\) horizontal section forces \(l\ge\mu-U_1>1-a\), \(a=t_1\). With (1),
\[
S_1<q(l).\tag{4}
\]
Use negative normals \((c,-s),(s,c)\), \(0<s\le c\), \(K=s/c=\lambda(\eta),\eta=s/(1+c)\le\sqrt2-1<5/12\). Write actual support intervals \([\alpha,\alpha+1],[\beta,\beta+1]\). The left-upper gap endpoint \(P=(-\mu,e)\in C\), \(e=\mu-S_4>0\), has first projection below that of the excluded left midpoint. Only the second lower support can exclude that midpoint, so \(l=-\beta/s\). The first support at \(P\) puts the first upper-axis root beyond \(\mu\), giving \(u=(\beta+1)/c=1/c-Kl\).

The first right-axis root satisfies \((\alpha+1)/c<1/c-\mu\); the second is \((\beta+1)/s=1/s-l>1/s-\mu\ge1/c-\mu\). Thus \(r=(\alpha+1)/c\), and \(d=\min(r/K,Kl)\). The second branch would give \(u+d=1/c>1\), contrary to (3). Consequently
\[
d=r/K,\quad r=Kd\le d,\quad u+r<1,\quad u>G=g(\eta).\tag{5}
\]
The final inequality uses \(l<1\). Projecting \(P\) gives \(e+d\le1/s-\mu/K<\eta\). As \(e>1-g(z)\),
\[
0<d<\eta,\qquad z<q(\eta-d).\tag{6}
\]
These support identities are specific to this rotation and are not transferred wholesale to another host representative.

### 3. The same F bottom chord forces u plus q(eta-d) below one

Suppose \(u+q(\eta-d)\ge1\). Equation (3) gives \(q(\eta-d)>d\); since \(q(\eta-d)<5/19<1/3\), \(d<1/3\), and algebra gives \(\eta>d(3+d)/(1+d)>5d/2\). Thus
\[
d<1/6,\qquad r\le d<1/6.\tag{7}
\]
Also \(u>1-q(\eta)\). From \(l=(1/c-u)/K\),
\[
l<\eta+q(\eta)/K=\eta+\frac{1-\eta^2}{2(2-\eta)}.
\]
This increases on \([0,5/12]\), with derivative \(6(\eta-1)(\eta-3)/(4-2\eta)^2>0\), ending at \(103/152<7/10\). Hence
\[
S_1<q(l)<7/13.\tag{8}
\]
If \(C\) contains the actual right inner endpoint \(Q_R\), then \(x>1-r\), \(S_2<q(r)<1/11\). Otherwise only original \(W\) can horizontally bridge that endpoint and \(C\)'s right endpoint; its actual top leg obeys \(D<x+q(r)\). Top joining gives \(D>1-\delta(z)\), so \(x>1-\delta(z)-q(r)\). Under the present supposition, \(z<5/19,\delta(z)<25/168,q(r)<1/11\); therefore both cases satisfy
\[
S_2<q(25/168+1/11)=443/3253.
\]
Together with (2), (7), (8), this gives \(\Sigma<7/13+443/3253<25/36<(1-d)^2\), impossible. Thus
\[
u+q(\eta-d)<1.\tag{9}
\]
Since \(z<q(\eta-d)\), \(C\) cannot contain the actual top-host endpoint \(Q_U\), whose height exceeds \(1-z\).

### 4. Original W's vertical bridge forces a direct right join of C

Only \(C,V_4,W\) meet the upper axis, so \(U_C,Q_U\in W\). If \(W\) also contained \(R_C\), the original-corner two-positive-endpoint lemma would give \(u+r>\mu\), contrary to (5). Hence \(W\) misses \(R_C\). Since \(F\)'s horizontal section is empty, failure of \(C\) to contain \(Q_R\) would force just that forbidden horizontal bridge by \(W\). Thus \(Q_R\in C\), and \(x>1-r,L_2-1<\Delta(r)\). Right joining and the actual vertical bridge bound give \(A>1-\Delta(r)\), \(A<z+q(u)\), hence
\[
z+q(u)+\Delta(r)>1.\tag{10}
\]

### 5. Two scalar comparisons give the opposite bound

Under (3), (5), (6),
\[
q(u)+\Delta(r)<u.\tag{11}
\]
For \(u\ge4/7\), use \(r\le d<1-u\), monotonicity of \(\Delta\), and
\[
u-q(u)-\Delta(1-u)=\frac{(1-u)(u^2+3u-2)}{2u(2-u)}>0,
\]
since the quadratic increases from \(2/49>0\) at \(4/7\). For \(u\le4/7\), \(v-q(v)\) increases on that interval with derivative at least \(1/50\), and \(u>G\). Also \(r=Kd<K\eta=\delta(\eta)\), while
\[
G-q(G)-\Delta(\delta(\eta))=
\frac{2\eta P(\eta)}{(1-\eta^2)(1-3\eta^2)(1+3\eta)},
\quad P=1-2\eta-2\eta^2+5\eta^3-6\eta^4>0.
\]
The denominator is positive. The derivative \(P'=-2-\eta(24\eta^2-15\eta+4)<0\), because the parenthesis is \(24(\eta-5/16)^2+53/32>0\); \(P(5/12)=1/3456>0\). Thus \(\Delta(r)<G-q(G)<u-q(u)\), proving (11). Now (6), (9), (11) give \(z+q(u)+\Delta(r)<q(\eta-d)+u<1\), contrary to (10). This closes the entire empty-horizontal left-gap/negative-rotation direction.

### 6. Empty-horizontal right gaps with positive rotation

Keep the right-gap family, with left/top joined. The corresponding **local central point-set** support argument, without reflecting the host pattern, gives for positive \(C\)
\[
l=Kd\le d<\eta,\quad u=1/c-Kr,\quad u+d<1,
\quad e+d<\eta,\quad e=\mu-A.\tag{12}
\]
Indeed the missing right midpoint activates the second lower support, \(r=-\beta/s\); the right-upper point makes the first upper-axis support exceed \(\mu\), so the second is active. The left root uses the first lower support, and the other possible lower-root branch would force \(u+d=1/c>1\). Thus \(d=l/K\).

Empty \(F\) horizontal section forces the direct left join, \(a>1-l>1/2,S_1<q(l)\). Actual left joining gives
\[
z<Y_s(a)<\frac{l^2}{4-4l-l^2}<4l^2/7<2d/7<d.\tag{13}
\]
Here \(l\le d<\eta<1/2\). Thus \(u+z<1\), so \(C\) misses \(Q_U\), and original \(W\) bridges \(U_C,Q_U\). Its actual bound \(A<z+q(u)\), combined with \(e=\mu-A\), (12), (13), gives
\[
A>1-\eta+d,\quad q(u)>1-\eta+d-z>1-\eta+5d/7.\tag{14}
\]
Therefore \(u>1-q(\eta)\), and the same increasing bound from Section 3 yields
\[
r<103/152<11/16.\tag{15}
\]
Since \(u+d<1\), \(d<q(\eta)<5/19<1/3\), and \(q(u)<q(1-d)=g(d)\). Equation (14) implies \(\eta>2d/(1+d)+5d/7>31d/14\), hence
\[
d<35/186<1/5,\quad l\le d<1/5,\quad S_1<1/9.\tag{16}
\]
Equation (13) sharpens to \(z<4/175<1/20,\delta(z)<2/399\). If \(Q_R\in C\), then \(S_2<q(r)<11/21\). Otherwise original \(W\) bridges horizontally, and top joining gives \(x>1-\delta(z)-q(r)\), whence
\[
S_2<q(\delta(z)+q(r))<q(2/399+11/21)=211/587<11/21.
\]
Thus always \(\Sigma<1/9+11/21=40/63<16/25<(1-d)^2\), contrary to (2). The exact constant margin is \(8/1575\). No restriction on original \(W\)'s top-midpoint membership was needed; the \(z\)-cap came from this actual left join and small left root.

### 7. Actual supports and unresolved double bridging in the left positive rotation

This section supplies necessary conditions only. Positive \(C\) has missing left midpoint activated by the first lower support, \(l=-\alpha/c\). If its lower root used \(l/K\), then an upper root from the same support would give \(u+d=1/s>1\); the other upper support, together with the left-upper point, gives \(u\ge K\mu+e,e\ge\mu/K-d\), hence \(u+d\ge\mu(K+1/K)>1\). Both violate the actual side/vertical budget. Thus the lower root uses \(-\beta/c\), and the upper root cannot use that same support. Therefore
\[
\alpha=su-1,\quad l=1/c-Ku,\qquad r=\min(Ku,d/K).\tag{17}
\]
The two actual left-gap endpoints still give \(L_1>1+u-\eta,e+d<G,z<q(G-d)\), and \(l<1\) gives \(u>\eta\).

If \(C\) contains neither \(Q_R\) nor \(Q_U\), the empty horizontal section of \(F\) forces original \(W\) to bridge both positive axes, containing \(R_C,U_C\). Its positive normal gives \(r>1-q(u)=2(1-u)/(2-u)\). Combined with \(r\le Ku,Kr\le d<1-u\),
\[
Ku>\frac{2(1-u)}{2-u},\qquad K<1-u/2.
\]
Hence \(u^3-4u^2+8u-4>0\). This polynomial increases on \([0,2/3]\) and ends at \(-4/27\), so \(u>2/3\); then \(K<2/3,\eta<1/3\), and \(w=u-\eta>1/3\). This is not yet a contradiction: \(L_1>1+w,L_1\le\sqrt2\) only adds \(u<\eta+\sqrt2-1\). Original \(W\)'s double bridge remains in this module's residual set.

The source's early attempted implication from (2) and \(S_2<1\) to \(1-\Phi(w)<2d-d^2\) omitted one. The correct consequence is only \(1-\Phi(w)<1+2d-d^2\). The stronger candidate is withdrawn and cannot close the double-bridge case. R38 uses the full actual bottom-chord diameter budget to supply a different closure.

<a id="R38"></a>
## R38. Closing all right gaps and the left double-bridge subclass

**Scope.** Far hosts \(V_1,V_2,V_4\) are left, right, top; original \(W=V_3\) is free. The actual \(C\) uniquely contains the center and no outer midpoint. The same \(F\) contains the bottom midpoint and has completely empty horizontal central section \(H_0\). Sections 1-4 concern a right gap with negative central rotation; Sections 5-7 concern the remaining left gap with positive rotation. All replacements or host reselections preserve the actual branch premises as specified, and no failed missing-one inequality is used.

### 1. Actual supports in the negative-rotation right-gap family

The true right gap belongs wholly to \(C\), and left/top are joined. R37 gives \(0<l,r,u,d\le2-\mu<1\). R36's actual side-point lemma excludes \(C\) from bottom; the nonempty right/central-vertical pair gives \(u+d<1\). The whole \(F\) lies below \(y=0\).

For negative normals \((c,-s),(s,c)\), \(0<s\le c\), write intervals \([\alpha,\alpha+1],[\beta,\beta+1]\), with \(\alpha,\beta\in(-1,0)\). Put \(\eta=s/(1+c),K=s/c=\lambda(\eta),G=g(\eta)\), \(0<\eta\le\sqrt2-1<5/12\). The lower root is \(\min((\alpha+1)/s,-\beta/c)\). If the first branch is active, an upper root from the same support gives \(u+d=1/s>1\); the other upper branch and the right-upper point \(P=(\mu,e)\) give \(e\ge\mu/K-d,u\ge K\mu+e\), hence \(u+d\ge\mu(K+1/K)>1\). Thus \(d=-\beta/c\), and the upper root cannot use the second support, so \(\alpha=-su\).

The missing right midpoint, together with \(O\) interior and \(P\in C\), forces its exclusion by the first upper support. Therefore
\[
r=1/c-Ku,\qquad l=\min(Ku,d/K),\qquad u>\eta.\tag{1}
\]
The last statement uses \(r<1\). This derivation concerns \(C\)'s local point set without reflecting the host graph. The actual right lower/upper gap endpoints give
\[
L_2>1+w,\quad w=u-\eta>0,\qquad e+d<G.\tag{2}
\]
Since \(L_2\le\sqrt2\), \(w<\sqrt2-1\), validating the later \(\Phi\)-bound.

### 2. Original W must bridge the upper axis

From \(l\le Ku,Kl\le d\), \(l^2\le ud\) and \(u+d\ge l(K+1/K)\ge2l\), so \(l<1/2\). Empty \(F\) horizontal section forces \(C\) to join the left host directly, \(a>1-l>1/2,S_1<q(l)\). The actual left join gives
\[
z<\frac{l^2}{4-4l-l^2}<4l^2/7<1/7.\tag{3}
\]
It also gives \(z<4ud/7<d\). By (2), \(u<\eta+\sqrt2-1\le2(\sqrt2-1)<6/7\), so \(u+z<1\). Thus \(C\) misses the actual top-host endpoint \(Q_U=(0,\mu-U_4)\). Only \(C,V_4,W\) meet the upper axis; closedness forces both \(U_C=(0,u),Q_U\in W\), with a positive-length bridge. R32's original-tile bridge argument is valid for all \(0<u<1\), giving \(A<U_4+q(u)<z+q(u)\). Since \(e=\mu-A\),
\[
\frac{2\eta}{1+\eta}+d<z+q(u).\tag{4}
\]
As \(z<d\),
\[
u>\frac{4\eta}{1+3\eta},\qquad
w>\frac{3\eta(1-\eta)}{1+3\eta}.\tag{5}
\]

### 3. The same F bottom-chord diameter forces w below two sevenths

The bottom gap and its closed endpoints belong wholly to \(F\); its chord \(b\ge2\mu-\Sigma\), \(\Sigma=S_1+S_2\), obeys diameter, so
\[
\Sigma>2-\sqrt2.\tag{6}
\]
From the actual \(L_2>1+w\), \(S_2\le\Phi(w)=(1+w)(1-\sqrt{w(2+w)})\). The function strictly decreases: its derivative is \(1-(1+4w+2w^2)/\sqrt{w(2+w)}<0\), as the square difference is \(1+6w+19w^2+16w^3+4w^4>0\). If \(w\ge2/7\), then \(S_1<q(l)<1/3\), hence
\[
\Sigma<1/3+\Phi(2/7)=34/21-36\sqrt2/49<2-\sqrt2.
\]
The positive margin is \(8/21-13\sqrt2/49\): it reduces to \(56>39\sqrt2\), with squared difference 94. This contradicts (6), so
\[
0<w<2/7.\tag{7}
\]
If \(\eta\ge1/4\), the concave quadratic \(15\eta-21\eta^2-2\) is positive on \([1/4,5/12]\), with endpoint values \(7/16,29/48\). Equation (5) then gives \(w>2/7\), impossible. Therefore
\[
\eta<1/4,\quad K<8/15,\quad u=\eta+w<15/28.\tag{8}
\]
These bounds are newly derived, not borrowed from the nonempty-horizontal height bound.

### 4. The original W bridge contradicts the same F square budget

Equations (3), (8) give \(z<4ud/7<15d/49\), \(q(u)<28u/41\), and \(2\eta/(1+\eta)>8\eta/5\). Thus (4) requires
\[
8\eta/5+34d/49<28u/41.\tag{9}
\]
Also \(S_1<q(l)<2l/3\le2Ku/3<16u/45\), so
\[
2d+S_1<\left(\frac{1372}{697}+\frac{16}{45}\right)u
-\frac{392}{85}\eta<\frac73(u-\eta)=7w/3.\tag{10}
\]
The coefficient margins are \(293/31365>0\) and \(581/255>0\), respectively. The same \(F\) has actual rooted reach \(v_F\ge\mu-d\); \(b+v_F^2\le2\) gives the valid bottom budget \(\Sigma>(1-d)^2\). With \(S_2\le\Phi(w)\), keeping all constants,
\[
1-\Phi(w)<2d-d^2+S_1<2d+S_1<7w/3.\tag{11}
\]
But R33's explicit strong loss gives \(1-\Phi(w)>5\sqrt w/4\); its positive-side square difference is
\[
(1+v^2)^2(2+v^2)-(5/4+v)^2
=4(v-5/16)^2+3/64+4v^4+v^6>0,
\quad v=\sqrt w.
\]
For \(0<w<2/7\), \(5\sqrt w/4>7w/3\), since \(25/16-(49/9)(2/7)=1/144>0\). This contradicts (11), closing the negative-rotation empty-horizontal right-gap family. With R37's positive rotation and R32-R33's nonempty-horizontal exclusions, the entire standardized far right-gap representative is closed. No top-midpoint restriction on original \(W\) or shared root of floating sections was used.

### 5. Original W cannot bridge both positive axes in the left positive rotation

Now let left have the true gap, with empty \(F\) horizontal section. R37's actual support identities give
\[
l=1/c-Ku,\quad r=\min(Ku,d/K),\quad u+d<1,
\quad w=u-\eta>0,\quad L_1>1+w,
\]
\[
e+d<G,\quad e=\mu-S_4,\quad z<q(G-d).\tag{12}
\]
If \(C\) contained neither \(Q_R\) nor \(Q_U\), original \(W\) would bridge both positive axes, containing \(R_C,U_C,Q_R,Q_U\). Its positive normal gives \(r>2(1-u)/(2-u)\). Together with \(r\le Ku,Kr\le d<1-u\),
\[
Ku>\frac{2(1-u)}{2-u},\qquad K<1-u/2.
\]
Thus \(u^3-4u^2+8u-4>0\). The polynomial increases on \([0,1]\), and its value at \(7/10\) is \(-17/1000\); hence \(u>7/10\). Then \(K<13/20\), and \(K(3/10)=60/91>13/20\) gives \(\eta<3/10\). Thus \(w>2/5\), while the actual long leg gives \(w<\sqrt2-1<5/12\). Consequently
\[
17/60<\eta<3/10,\quad7/10<u<43/60,
\quad S_1\le\Phi(w)<\Phi(2/5)<1/30.\tag{13}
\]
The last comparison is \(\Phi(2/5)=7/5-14\sqrt6/25<1/30\), certified by \(6\cdot84^2-205^2=311>0\).

The actual bottom-chord diameter budget (6) gives \(\Sigma>2-\sqrt2>7/12\), so \(S_2>11/20>1/2\). Since \(S_2<g(x)\), \(x<1/3\), whence \(L_2\le1+\delta(x)<5/4\). Right joining forces
\[
A>3/4.\tag{14}
\]
On the other hand, (13) gives \(q(u)<43/77,r>34/77,K>2\eta>17/30\). Thus \(d\ge Kr>289/1155\), \(G<43/77\), so \(G-d<356/1155,z<178/977\). The original \(W\) vertical bridge gives
\[
A<z+q(u)<178/977+43/77<3/4,
\]
with margin \(2819/300916>0\), contradicting (14). Hence \(C\) must directly contain at least one of \(Q_R,Q_U\). This repairs the double-bridge subclass using the full bottom-chord diameter; it does not use the withdrawn missing-one loss.

### 6. C cannot contain both positive inner endpoints either

If \(Q_R\in C\), then \(S_2<q(r)\). By (12), \(r\le Ku,Kr\le d,u+d<1\), giving \(r<1/2,r^2\le ud\). If also \(Q_U\in C\), then \(u>1-z\), while \(z<q(G-d)\), so
\[
1-G+d<q(u).\tag{15}
\]
This is stronger than (4). Reuse only the explicit scalar argument of Sections 3-4, replacing the short leg \(S_1\), short root \(l\), and long-leg-controlled \(S_2\) by the actual \(S_2,r,S_1\), respectively. The sum \(\Sigma\) and same original \(F\) budgets are unchanged; the actual \(L_1>1+w\) gives \(S_1\le\Phi(w)\). All scalar premises hold, and (15) can be weakened to \(1-G+d<q(u)+4r^2/7\). The argument again gives \(w<2/7,\eta<1/4\), then
\[
1-\Phi(w)<2d-d^2+S_2<7w/3<5\sqrt w/4,
\]
contrary to the strong loss. No host reflection or transferred left-join cap is involved. Thus in the left residual \(C\) contains **exactly one** of \(Q_R,Q_U\).

### 7. Excluding the top midpoint from the original left-gap W and recording the residual set

If original \(W\) contained the top midpoint, reselect it as top host, retain original \(V_4\) as the new free tile, and reflect horizontally. The new top host admits the valid individual midpoint domination. The old \(V_4\), now free and unmoved, has no larger relevant leg than the old standardized \(V_4\); therefore the original true left gap is not filled by this role change. Its reflection remains a true right gap with \(F\)'s horizontal section empty, belonging to the family excluded above and in R37. Any alternative duplicated host selection producing a near representative is already excluded by R28.

Exactly the following empty-horizontal families remain after this module: a left gap with positive \(C\), original \(W\) lacking the top midpoint, and \(C\) containing exactly one of \(Q_R,Q_U\); or three joins, retaining possible bottom contact of \(C\), duplicate top-midpoint membership of \(W\), and both central rotation signs. Their further exclusion lies outside this module.

<a id="R39"></a>
## R39. Closing the LEFT true gap and excluding BOTTOM contact in the three-contact form

**Scope and inputs.** The target is \([-\mu,\mu]^2\), \(\mu>1\). The selected hosts are \(V_1\) at the left midpoint, \(V_2\) at the right midpoint, \(V_4\) at the top midpoint, and the original \(W=V_3\). The unique origin host \(C\) contains no outer midpoint. The original \(F\) contains the bottom midpoint, misses the origin, and has empty horizontal central chord. Sections 1--5 concern the remaining LEFT true-gap representatives, with TOP and RIGHT contact; Sections 6--7 concern three contacts. All geometric statements concern the same actual \(C,F,W\).

### 1. Common premises for the two remaining LEFT representatives

R38 excludes two \(W\) bridges, two direct \(C\) contacts, and a repeated TOP midpoint in \(W\). Thus \(C\) contains exactly one of \(Q_R,Q_U\). It has positive rotation. Write
\[
K=\frac{2\eta}{1-\eta^2},\quad G=\frac{1-\eta}{1+\eta},\quad
q(t)=\frac{t}{2-t},\quad \Delta(t)=\frac{t^2}{2(1-t)},\quad
\Phi(w)=(1+w)(1-\sqrt{w(2+w)}).
\]
The actual support equations and closed-end projection estimates give
\[
l=\sec\theta-Ku,\quad r=\min(Ku,d/K),\quad u+d<1, \tag{1}
\]
\[
w=u-\eta>0,\quad L_1>1+w,\quad S_1\le\Phi(w),\quad
z<q(G-d),\quad G-d>0. \tag{2}
\]
Here \(\eta=\tan(\theta/2)\), \(0<\eta\le\sqrt2-1<5/12\), and \(0<w<\sqrt2-1<5/12\). Every axial reach is at most \(2-\mu<1\). Equation (1) yields \(r<1/2\) and \(r^2\le ud\).

Since \(C\) misses BOTTOM, the complete bottom gap and its endpoints belong to the original \(F\). With \(\Sigma=S_1+S_2\), the same tile gives
\[
\Sigma>2-\sqrt2,\qquad \Sigma>(1-d)^2. \tag{3}
\]
The long-leg loss and monotonicity calculation of R38 gives
\[
1-\Phi(w)>\frac54\sqrt w. \tag{4}
\]
The bound is on \(r\), not \(l\); neither \(u<1/2\) nor \(\eta<1/4\) is an input.

### 2. Direct contact only at \(Q_R\): rationalizing the original vertical bridge

Since \(Q_R\in C\),
\[
x>1-r,\quad S_2<q(r),\quad L_2-1<\Delta(r).
\]
Since \(Q_U\notin C\) and \(F\) contributes nothing on the positive vertical axis, the original \(W\) contains both the upper exit of \(C\) and \(Q_U\). RIGHT contact and this bridge give
\[
1-\Delta(r)<A<z+q(u),
\quad q(G-d)+q(u)+\Delta(r)>1. \tag{5}
\]
The diameter comparison in R38, Section 3, applies with \(S_2<q(r)<1/3\), (3), and \(S_1\le\Phi(w)\), yielding \(w<2/7\).

Put \(E=1-G+d\in(0,1)\) and \(T=q(u)+\Delta(r)\). Since \(u=\eta+w<5/7\),
\[
T<5/9+1/4<1,\qquad q(G-d)=\frac{1-E}{1+E}.
\]
Thus (5) is equivalent to
\[
E<q(T)<T. \tag{6}
\]
Also \(\Delta(r)<r^2\le ud<d\), so \(1-G<q(u)\), giving
\[
u>\frac{4\eta}{1+3\eta},\qquad
w>\frac{3\eta(1-\eta)}{1+3\eta}.
\]
Combining \(w<2/7\) with the concave quadratic comparison of R38 gives the newly derived bounds
\[
\eta<1/4,\quad K<8/15,\quad u<15/28,\quad r<2/7. \tag{7}
\]
Now
\[
T<15/41+2/35=607/1435<1/2,
\]
so \(q(T)<2T/3\), while \(\Delta(r)<7r^2/10\le7ud/10\). Equation (6) becomes
\[
\frac{2\eta}{1+\eta}+d<\frac23q(u)+\frac7{15}ud.
\]
Using (7),
\[
\frac85\eta+\frac34d<\frac{56}{123}u. \tag{8}
\]
Moreover \(S_2<2r/3\le2Ku/3<16u/45\). Hence
\[
2d+S_2<\left(\frac{448}{369}+\frac{16}{45}\right)u-\frac{64}{15}\eta
<\frac85(u-\eta)=\frac85w. \tag{9}
\]
The positive coefficient margins are \(56/1845\) and \(8/3\). Equations (3) and (2) imply
\[
1-\Phi(w)<2d-d^2+S_2<\frac85w.
\]
This contradicts (4), because for \(w<2/7\),
\[
\frac{25}{16}-\frac{64}{25}\frac27=\frac{2327}{2800}>0.
\]
The representative with only \(Q_R\in C\) is excluded.

### 3. Direct contact only at \(Q_U\): a short-reach lemma for the same \(C\)

Direct TOP contact gives \(u\ge\mu-U_4>1-z\). Together with (2),
\[
\frac{2\eta}{1+\eta}+d<q(u), \tag{10}
\]
and in particular \(u>4\eta/(1+3\eta)\). The original \(W\) supplies the full horizontal bridge between the right exit of \(C\) and \(Q_R\).

We prove
\[
r<\frac23w. \tag{11}
\]
Only \(0<\eta,w\le5/12\), \(u=\eta+w\), \(r\le Ku\), and
\(Kr\le d<q(u)-2\eta/(1+\eta)\) are used. If \(r\ge2w/3\), then
\[
K(\eta+w)\ge2w/3,\qquad
q(\eta+w)-\frac{2\eta}{1+\eta}-\frac23Kw>0.
\]
After multiplication by the positive denominator \(3(1-\eta^2)(2-\eta-w)\), the latter numerator is
\[
P=-9\eta^3-5\eta^2w+18\eta^2+4\eta w^2-2\eta w-9\eta+3w.
\]
It is strictly increasing in \(w\), since
\[
P_w=3-2\eta-5\eta^2+8\eta w\ge187/144>0.
\]
For \(\eta\ge1/5\),
\[
P\le P(\eta,5/12)=-Q(\eta)/36,\quad
Q=324\eta^3-573\eta^2+329\eta-45.
\]
On \([1/5,5/12]\), \(Q''<0\), \(Q'\ge Q'(5/12)=81/4>0\), and \(Q(1/5)=59/125>0\). Thus \(P<0\), a contradiction.

For \(\eta\le1/5\), the first inequality forces
\[
w\le\frac{3\eta^2}{1-3\eta-\eta^2},\qquad1-3\eta-\eta^2\ge9/25>0.
\]
Monotonicity in \(w\) then gives
\[
P\le-\frac{3\eta R(\eta)}{(\eta^2+3\eta-1)^2},
\]
\[
R=3\eta^6+7\eta^5-41\eta^4-40\eta^3+71\eta^2-27\eta+3.
\]
On \([0,1/5]\), \(142\eta-120\eta^2\le118/5\) and \(18\eta^5+35\eta^4\le193/3125\), whence
\[
R'\le-27+118/5+193/3125=-10432/3125<0.
\]
As \(R(1/5)=888/15625>0\), again \(P<0\). This proves (11) by two analytic intervals with explicit derivatives and endpoints.

### 4. Shrinking the domain using the actual horizontal bridge and bottom diameter

TOP contact and \(L_4\le\sqrt2\) imply \(D>2-\sqrt2\). The actual bridge gives \(D<x+q(r)\), so
\[
x>1-(\sqrt2-1+q(r)),\qquad
S_2<q(\sqrt2-1+q(r)). \tag{12}
\]
The argument of \(q\) is verified to be less than one at each use. First, (11) gives \(r<5/18\), \(q(r)<5/31\), and
\[
S_2<q(5/12+5/31)=215/529<5/12.
\]
If \(w\ge1/3\), monotonicity and \(\sqrt7>21/8\) give \(S_1\le\Phi(1/3)<1/6\). Then \(\Sigma<7/12<2-\sqrt2\), contradicting (3). Thus \(w<1/3\).

Now \(r<2/9\), \(q(r)<1/8\), and \(S_2<q(5/12+1/8)=13/35\). If \(w\ge9/28\), then \(\sqrt{65}>8\) yields
\[
S_1\le\Phi(9/28)<37/196<1/5,
\]
and \(\Sigma<1/5+13/35=4/7<7/12<2-\sqrt2\). Therefore
\[
w<9/28. \tag{13}
\]
Equation (10) gives \(w>3\eta(1-\eta)/(1+3\eta)\). On \([1/4,5/12]\),
\[
57\eta-84\eta^2-9\ge0
\]
by concavity and endpoint values \(0,1/6\). That would give \(w>9/28\). Consequently
\[
\eta<1/4,\quad K<8/15,\quad u<4/7. \tag{14}
\]

### 5. Strengthening the bridge by exact TOP contact

The genuine direct TOP contact gives \(z>1-u\), hence \(L_4-1<\Delta(u)\) by the second long-leg projection. Thus
\[
1-\Delta(u)<D<x+q(r).
\]
Put \(T=\Delta(u)+q(r)\). Equations (1) and (14) give
\[
T<\frac76u^2+\frac{16}{45}u<\frac{46}{45}u<\frac{184}{315}<2/3.
\]
Hence \(x>1-T>0\) and \(S_2<q(T)<3T/4<23u/30\). Also
\[
d<q(u)-\frac{2\eta}{1+\eta}<\frac7{10}u-\frac85\eta.
\]
Therefore
\[
2d+S_2<\frac{13}{6}u-\frac{16}{5}\eta
<\frac{13}{6}(u-\eta)=\frac{13}{6}w, \tag{15}
\]
with positive \(\eta\)-coefficient margin \(31/30\). The bottom budget implies
\[
1-\Phi(w)<2d-d^2+S_2<\frac{13}{6}w.
\]
This contradicts (4) and (13), because
\[
\frac{25}{16}-\frac{169}{36}\frac9{28}=\frac3{56}>0.
\]
The representative with only \(Q_U\in C\) is excluded. Together with R38, this closes the standardized far LEFT true-gap case.

### 6. The three-contact form: a uniform upper reach and no BOTTOM contact

Now LEFT, TOP, and RIGHT all have contact, and \(F\) still has empty horizontal chord. Both rotations of \(C\) and repetition of TOP midpoint by the original \(W\) remain allowed. The earlier LEFT active face, \(w\), small-angle bounds, and \(u+d<1\) are not inputs here.

Actual LEFT contact gives \(z<\kappa_0(L_1)<4/15\), where \(\kappa_0\) denotes the source's long-leg angle bound, not the midpoint count. RIGHT contact gives
\[
A\ge2\mu-L_2>2-\sqrt2>7/12.
\]
If \(Q_U\in C\), then \(u\ge\mu-U_4>1-z>11/15\). Otherwise closedness forces the original \(W\) to contain the entire bridge from the upper exit of \(C\) to \(Q_U\), since \(F\subset\{y<0\}\). Its actual supports give \(A<z+q(u)\), without any prohibition on repeated TOP midpoint. Hence
\[
q(u)>7/12-4/15=19/60,\qquad u>38/79. \tag{16}
\]
This lower bound holds in both cases; the global reach cap supplies \(u<1\).

If \(C\) met BOTTOM at \((x,-\mu)\), its distance from the actual point \((0,u)\in C\) would exceed \(117/79\), while
\[
(117/79)^2-2=1207/6241>0.
\]
That exceeds the unit-square diameter. Thus \(C\) misses BOTTOM.

### 7. Three bottom budgets from the same original \(F\)

The top corner hosts cannot meet BOTTOM, and neither can \(C\). Both bottom short legs are less than \(1<\mu\), so the genuine bottom gap is nonempty and, with its endpoints, belongs entirely to the original \(F\). Let \(b\) be its actual bottom chord and \(v\) its actual upward reach from bottom midpoint. Then
\[
b\ge2\mu-\Sigma,\quad v\ge\mu-d,\quad0<d<1.
\]
The diameter and square budget give
\[
\Sigma>2-\sqrt2,\qquad \Sigma>(1-d)^2. \tag{17}
\]
The triangle formed by the bottom endpoints and the highest vertical point has area \(bv/2\le1/2\). Thus
\[
\Sigma\ge2\mu-\frac1{\mu-d}>2-\frac1{1-d}. \tag{18}
\]
Strictness follows because \(2\mu-1/(\mu-d)\) strictly increases in \(\mu\). The area budget is stronger than the square budget when \(d<(3-\sqrt5)/2\), since their difference is
\[
\frac{d(1-3d+d^2)}{1-d}.
\]
The remaining problem is the three-contact form, retaining both rotations, repeated TOP midpoint, and floating \(W\) chords. No exclusion of TOP or side contact by \(C\), and no bound \(u+d<1\), has been established here. The source records 29 UNSAT checks (26 NRA and 3 LRA), six identities, and 19 constant checks; these audit arithmetic, while geometric premises remain separate review obligations. R40--R64 continue the argument.

<a id="technical-part-G"></a>
# Technical Part G. Actual seams, contacts and lower exits

Modules: [R40](#R40), [R41](#R41), [R42](#R42), [R43](#R43), [R44](#R44), [R45](#R45), [R46](#R46), [R47](#R47), [R48](#R48).

<a id="R40"></a>
## R40. A forced interior seam point in the three-contact form

**Scope and inputs.** Work on \([-\mu,\mu]^2\), \(\mu>1\), with the same selected hosts \(V_1,V_2,V_4,W=V_3\), the unique origin tile \(C\) with no outer midpoint, and the original bottom-midpoint tile \(F\subset\{y<0\}\). The actual contacts are
\[
L_1+S_4\ge2\mu,\qquad L_2+A\ge2\mu,\qquad L_4+D\ge2\mu.
\]
The tiles \(C,F\) stay fixed. The normalized \(V_1,V_4\) are representatives obtained by legal target-relative covering replacements.

### 1. Exact corner supports

For a half-angle \(t\), define
\[
c_t=\frac{1-t^2}{1+t^2},\quad s_t=\frac{2t}{1+t^2},\quad
b_t=1/c_t,\quad K_t=s_t/c_t=\lambda(t),\quad g(t)=\frac{1-t}{1+t}.
\]
A long leg \(L\ge\mu\) obeys \(c_tL\le1\), \(s_tL\le1\); its short leg is \(S=(1-s_tL)/c_t<g(t)\).

For \(V_1\), with half-angle \(a\) and inward coordinates \(X=x+\mu,Y=y+\mu\),
\[
0\le s_aX+c_aY\le1,\qquad
-s_aL_1\le c_aX-s_aY\le1-s_aL_1. \tag{1}
\]
For \(V_4\), with half-angle \(z\), use \(X=x+\mu,Y'=\mu-y\):
\[
0\le c_zX+s_zY'\le1,\qquad
-s_zL_4\le-s_zX+c_zY'\le1-s_zL_4=c_zS_4. \tag{2}
\]
No TOP/horizontal and RIGHT/vertical pairing is exchanged, and no shared-origin formula is applied to a floating chord.

### 2. LEFT contact forces \(z<a\) and \(a+2z<1\)

From \(L_1+S_4\ge2\mu>2\), \(S_4<g(z)\), and both projections of \(L_1\),
\[
0<a\le2/5:\quad z<Y_c(a)=\frac{a^2}{1-2a^2},
\]
\[
2/5\le a<1:\quad z<Y_s(a)=\frac{(1-a)^2}{6a-1-a^2}. \tag{3}
\]
Both denominators are positive. On the first interval,
\[
Y_c/a\le10/17<1,\qquad1-a-2Y_c\ge11/85>0.
\]
On the second, \(Y_s<a\) is equivalent to \(a^3-5a^2-a+1<0\), whose derivative is negative on \([2/5,1]\), with left value \(-17/125\). Likewise \(2Y_s<1-a\) is equivalent to \(a^2-8a+3<0\), decreasing there with left value \(-1/25\). Hence
\[
z<a,\qquad a+2z<1. \tag{4}
\]
This calculation does not require the 266-coefficient certificate of R13.

### 3. The actual seam point

Intersect the first upper support of \(V_1\) with the second upper support of \(V_4\):
\[
X_*=\frac{b_a+S_4-2\mu}{K_a-K_z},\quad
e_*=\mu-S_4-K_zX_*,\quad P_*=(-\mu+X_*,e_*). \tag{5}
\]
The denominator is positive. Since \(b_a\ge L_1\), LEFT contact gives \(X_*\ge0\). Moreover
\[
b_a+S_4-2\mu-a(K_a-K_z)
<\frac{2z(a+z-1)}{1-z^2}<0,
\]
so \(X_*<a\). Also
\[
e_*>1-g(z)-K_za=\frac{2z(1-z-a)}{1-z^2}>0,
\]
while \(S_4>0\) gives \(e_*<\mu\). Thus
\[
0\le X_*<a<1<\mu,\qquad0<e_*<\mu. \tag{6}
\]
The endpoint \(X_*=0\) is allowed.

For membership in \(V_1\), the first projection is one. Its upper boundaries switch at
\[
X_0=\frac{b_a-L_1}{K_a+1/K_a}=s_a(1-c_aL_1)\ge0.
\]
There the difference between the upper boundary of \(V_1\) and lower boundary of \(V_4\) is
\[
L_1+S_4-2\mu+(1/K_a+K_z)X_0\ge0.
\]
It subsequently decreases with slope \(-(K_a-K_z)\), reaching zero at \(X_*\); hence \(X_*\ge X_0\), proving the second lower support. On the first upper support the second projection is \(X_*/c_a-K_a\). Its upper bound is equivalent to
\[
X_*\le c_a+s_a-c_as_aL_1.
\]
The right side is at least \(s_a>a>X_*\), because \(s_aL_1\le1\).

For membership in \(V_4\), its second projection is exactly \(c_zS_4\). Its first projection is \(X_*/c_z+s_zS_4>0\). Since \(X_*<a<1-2z\), and
\[
c_z(1-s_zg(z))-(1-2z)
=\frac{2z^2(z^3-z^2+z+1)}{(1+z^2)^2}>0,
\]
we have \(X_*<c_z(1-s_zS_4)\), so the first projection is strictly below one. Thus \(P_*\in V_1\cap V_4\); the calculation verifies all supports of the actual squares.

### 4. Full coverage forces \(P_*\in C\)

At \(X=X_*+h\), for sufficiently small \(h>0\), the two relevant boundaries are
\[
y_1=e_*-K_ah,\qquad y_4=e_*-K_zh.
\]
The nonempty interval \(y_1<y<y_4\) violates the upper supports of both tiles. Its midpoint gives a positive-height target-interior sequence converging to \(P_*\).

Tiles containing opposite target corners are disjoint: an intersection would make those corners at distance at most \(2\sqrt2\), while their distance is \(2\mu\sqrt2>2\sqrt2\). Since \(P_*\in V_1\), a neighborhood misses the opposite tile \(W\); since \(P_*\in V_4\), a neighborhood misses \(V_2\). Closedness supplies these neighborhoods. The tile \(F\subset\{y<0\}\) cannot cover the positive-height sequence. Full coverage therefore puts the sequence in \(C\); closedness gives
\[
P_*\in C. \tag{7}
\]
The lemma applies to all four remaining direct/bridge combinations, both rotations of \(C\), and repeated TOP midpoint in \(W\). It needs actual LEFT contact and the empty horizontal chord of \(F\), rather than a LEFT true gap.

### 5. Joint budgets for this same \(C\)

Write \(\rho=\mu-X_*>0\) and \(e=e_*\). The same \(C\) contains \(P=(-\rho,e)\), \(R=(r,0)\), \(U_C=(0,u)\), and \(D_C=(0,-d)\). Diameter and triangle-area bounds give
\[
(\rho+r)^2+e^2\le2,\qquad \rho^2+(e+d)^2\le2, \tag{8}
\]
\[
|u(\rho+r)-re|\le1,\qquad d(\rho+r)+re\le1. \tag{9}
\]
The two triangles with common vertical base \(U_CD_C\), and third vertices \(P,R\) on opposite sides, have disjoint interiors in \(C\). Their total area gives
\[
(\rho+r)(u+d)\le2. \tag{10}
\]
No inequality \(e\le u\) or active support of \(C\) has been assumed. These necessary conditions are combined with the same original \(F\)'s complete bottom-chord bounds:
\[
\Sigma>2-\sqrt2,\quad\Sigma>(1-d)^2,\quad
\Sigma>2-\frac1{1-d}. \tag{11}
\]

If the original \(W\) also contains TOP midpoint, a legal dominating replacement makes it top-anchored with half-angle \(\tau\). The reflected RIGHT argument then yields
\[
X_R=\frac{b_x+A-2\mu}{K_x-K_\tau},\quad
e_R=\mu-A-K_\tau X_R,\quad P_R=(\mu-X_R,e_R)\in C. \tag{12}
\]
Consequently
\[
(2\mu-X_*-X_R)^2+(e_*-e_R)^2\le2. \tag{13}
\]
This is a necessary condition for the repeated-midpoint subclass, not its exclusion; any replacement must be followed by the prescribed reclassification. Independently, if \(Q_U\in C\), then \(u\ge\mu-U_4>1-z\), so \(g(z)<q(u)\) and
\[
L_1>2-q(u). \tag{14}
\]
This long-leg loss does not authorize the old LEFT active-face equations or \(u+d<1\).

<a id="R41"></a>
## R41. Near-diagonal double-direct contact and auxiliary seam comparisons

**Scope and inputs.** The target, actual tiles, and three contacts are those of R40. The original \(F\subset\{y<0\}\) owns the complete bottom gap, including its endpoints, and \(C\) misses BOTTOM. Thus
\[
\Sigma=S_1+S_2>2-\sqrt2>7/12. \tag{1}
\]
This module's exclusion assumes direct \(Q_U\) contact and then direct \(Q_R\) contact. Its angle band is auxiliary to the later argument; no direct-contact premise transfers to an upper bridge.

### 1. Projection of the actual seam point

Use \(b_a=(1+a^2)/(1-a^2)\), \(K_a=2a/(1-a^2)\), \(K_z=2z/(1-z^2)\), and \(g(z)=(1-z)/(1+z)\). LEFT contact gives \(z<a\), \(a+2z<1\), and the earlier global cap \(z<4/15\). R40 gives the actual point
\[
X_\mu=\frac{b_a+S_4-2\mu}{K_a-K_z},\quad
e_\mu=\mu-S_4-K_zX_\mu,\quad
P=(-\rho,e_\mu)\in C,\quad\rho=\mu-X_\mu. \tag{2}
\]
This is an interior seam point, not an old LEFT outer-gap point.

Write \(c=\cos\theta\ge s=\sin\theta\ge12/17\). The two orientations have normals \((c,s),(-s,c)\) and \((c,-s),(s,c)\). Suppose \(Q_U\in C\). Then \(u\ge\mu-U_4>1-z>11/15\). Since \(P\in V_1\) together with the lower-left corner, \(e_\mu+\mu\le\sqrt2\), so \(e_\mu<\sqrt2-1<5/12<u\). Projection of \(P\) and \((0,u)\) gives respectively
\[
c\rho+s(u-e_\mu)\le1\quad\hbox{or}\quad
s\rho+c(u-e_\mu)\le1.
\]
Both imply
\[
\rho-e_\mu+u\le1/s\le17/12,\qquad
\rho-e_\mu<5/12+z. \tag{3}
\]
No location of the center of \(C\) is prescribed.

Define the algebraic expressions
\[
X=\frac{b_a+S-2}{K_a-K_z},\quad Q=S+(K_z-1)X,\quad S=S_4. \tag{4}
\]
They eliminate \(\mu\) algebraically; no covering classification for a rescaled target is invoked. The identity
\[
\rho-e_\mu=Q+\frac{2(\mu-1)(1-K_z)}{K_a-K_z}>Q
\]
uses \(K_z<1\), \(K_a>K_z\). Therefore
\[
Q<5/12+z. \tag{5}
\]
The actual long leg \(L=L_1\) also satisfies
\[
L>2-S,\quad L(1-a^2)\le1+a^2,\quad2aL\le1+a^2,
\quad0<S<g(z),\quad S_1=b_a-K_aL. \tag{6}
\]

### 2. First local inequality: \(S_1<2/7\)

Under (4)--(6) and the stated angle domain,
\[
S_1<2/7. \tag{7}
\]
Assume the opposite. If \(a\le1/4\), then \(X<a\), \(S>2-L\ge2-b_a\), and \(z<Y_c(a)\le1/14\); hence
\[
Q-z>S-a-z>2-17/15-1/4-1/14>5/12,
\]
contradicting (5). For \(a>1/4\), the assumption and (6) require
\[
F(a,z):=b_a-K_a(2-g(z))>2/7.
\]
Thus \(a<5/9\) and
\[
z<Z(a)=\frac{(1-a)(5-9a)}{-9a^2+42a-5}, \tag{8}
\]
with positive denominator on the actual interval. This follows from
\[
(F-2/7)(1+z)=g(a)-2/7-z(3K_a+2/7-b_a).
\]
The slope of \(Q\) in \(S\) is \((K_a-1)/(K_a-K_z)\). If \(K_a\le1\), use \(Q\ge Q(g(z))\); if \(K_a\ge1\), use
\[
S>S_{\min}=2-(b_a-2/7)/K_a,\qquad Q\ge Q(S_{\min}).
\]
It remains to establish nonnegativity of
\[
P_1=(Q(g(z))-z-5/12)(a-z)(1+az),
\]
\[
P_2=(Q(S_{\min})-z-5/12)28a(a-z)(1+az).
\]
All multiplied factors are positive in the actual domain. The complete domain is covered by three parameter charts, with \(0\le v\le1\):

1. \(P_1\): \(1/4\le a\le1/3\), \(z=Y_c(a)v\), \(Y_c=a^2/(1-2a^2)\).
2. \(P_1\): \(1/3\le a\le3/7\), \(z=Z(a)v\).
3. \(P_2\): \(2/5\le a\le5/9\), \(z=Z(a)v\).

The second covers the remaining \(K_a\le1\) range because \(\sqrt2-1<3/7\); the third covers \(K_a\ge1\) because \(\sqrt2-1>2/5\). After affine normalization of \(a\) and clearing positive denominators, the degrees are \((8,3),(8,3),(10,3)\). The source reports 116 strictly positive exact Bernstein coefficients and independent equality checks reconstructing all three polynomials. These certificates contradict (5) and establish (7). Their exact polynomial and coefficient records, rather than sample angles, are the arithmetic audit objects.

### 3. Stronger local inequality

On the same full local domain,
\[
S_1+q(5/12+z)<7/12,\qquad q(t)=t/(2-t). \tag{9}
\]
For larger \(z\), put \(w=2z/(1+z)\). The long leg obeys \(L>2-g(z)=1+w\) and \(L\le\sqrt2\). At fixed \(L\), \((1-L\sin\theta)/\cos\theta\) decreases with the legal angle; the smallest legal angle has \(\cos\theta=1/L\). The maximum is \(L(1-\sqrt{L^2-1})\), decreasing in \(L\). Thus
\[
S_1\le\Phi(w)=(1+w)(1-\sqrt{w(2+w)}).
\]
With \(v=\sqrt{w(2+w)}\),
\[
\Phi'(w)=1-2v-1/v\le1-2\sqrt2<-7/4.
\]
For \(z<4/15\), \(w'\ge450/361\), whereas
\[
\frac{d}{dz}q(5/12+z)\le7200/6241.
\]
Their sum strictly decreases, and at \(z=2/9\) it equals
\[
\frac{15(11-2\sqrt{26})}{121}+\frac{23}{49}<7/12.
\]
This proves (9) for \(z\ge2/9\).

For \(z<2/9\), define \(T=7/12-q(5/12+z)\), \(E=F-T\). Failure of (9) requires \(E>0\). For \(K_a\le1\), \(a\le\sqrt2-1<3/7\) and \(Q\ge Q(g(z))\). Put
\[
\mathcal P=12(a-z)(1+az)(Q(g(z))-z-5/12),
\]
\[
\mathcal N=12(1-a^2)(1+z)(19-12z)E.
\]
All displayed denominator-clearing factors are positive. Explicitly,
\[
\mathcal P=(12z^2+19z-12)a^2+(12z^3+17z^2-36z+7)a+5z.
\]
Five full charts suffice:

1. \(0\le z\le1/7\), \(0\le a\le3/7\): \(\mathcal P\ge0\).
2. \(1/7\le z\le3/16\), \(0\le a\le2/5\): \(\mathcal P\ge0\).
3. The same \(z\) interval, \(2/5\le a\le3/7\): \(-\mathcal N>0\).
4. \(3/16\le z\le2/9\), \(0\le a\le A(z)=(27-16z)/60\): \(\mathcal P\ge0\).
5. The same \(z\) interval, \(A(z)\le a\le3/7\): \(-\mathcal N>0\).

The first type contradicts (5); the second contradicts \(E>0\). The function \(A\) is an explicit analytic divider.

For \(K_a\ge1\), \(E\) strictly decreases in \(a\), and
\[
E_z=-2K_a/(1+z)^2+2/(19/12-z)^2<0.
\]
Since
\[
E(\sqrt2-1,1/9)=\sqrt2-6/5+19/53-7/12<0,
\]
the condition \(E>0\) forces \(z<1/9\), where \(E_z<-2/3\). With \(a_*=155/301\),
\[
E(a,0)=\frac{2(a_*-a)}{(1+a)(1+a_*)}.
\]
Thus \(a<a_*\); because \(a>2/5\), this expression is less than \(a_*-a\), giving
\[
0<z<\frac32(a_*-a). \tag{10}
\]
Now \(S_1\ge T\) implies \(S>2-(b_a-T)/K_a\). Since \(Q\) is nondecreasing in \(S\), it suffices to show
\[
\mathcal P_2=24a(a-z)(1+az)(19-12z)
\left[Q\left(2-\frac{b_a-T}{K_a}\right)-z-\frac5{12}\right]\ge0.
\]
The complete chart \(2/5\le a\le a_*\), \(z=\tfrac32(a_*-a)v\), \(0\le v\le1\), has strictly positive coefficients. Together the five charts above and this chart have degrees \((2,3),(2,3),(2,2),(2,4),(2,4),(7,4)\), and 103 exact nonnegative Bernstein coefficients. Zero coefficients occur only in the chart containing \((a,z)=(0,0)\). The source reports independent polynomial reconstruction and coefficient-identity checks for all six. These and the larger-\(z\) monotonicity establish (9) on the entire stated domain.

### 4. Excluding near-diagonal double-direct contact

Suppose additionally \(Q_R\in C\). Its actual right reach satisfies \(r\ge\mu-U_2>1-x\), so \(S_2<g(x)<q(r)\). Projection of \((r,0),(0,u)\) gives \(sr+cu\le1\) or \(cr+su\le1\). Since \(c\ge s\ge12/17\),
\[
r+u\le17/12,\quad r<5/12+z,\quad S_2<q(5/12+z).
\]
Equation (9) yields \(\Sigma<7/12\), contradicting (1). Therefore the whole subclass \(\sin\theta\ge12/17\) with both direct contacts is excluded. No repeated TOP midpoint or axial symmetry of \(C\) is required. This module leaves \(\sin\theta<12/17\) and the other three mechanisms open.

### 5. Repeated TOP midpoint: a third forced point

If the original \(W\) contains TOP midpoint, replace it legally by a top-anchored representative with half-angle \(\tau\), top long leg \(D\ge\mu\), and right short leg \(A\), preserving \(C,F\) and the other hosts. Reclassification after replacement remains required. RIGHT contact yields \(\tau<4/15\). Write
\[
p=c_z,\quad q=s_z,\quad c=c_\tau,\quad s=s_\tau,\quad\mathcal D=cq+ps>0.
\]
The first upper supports meet at
\[
Y_T=\frac{p+c-2\mu pc}{\mathcal D},\quad
X_T=\frac{1-qY_T}{p},\quad Q_T=(X_T-\mu,\mu-Y_T). \tag{11}
\]
TOP contact and \(L_4\le1/p,D\le1/c\) give \(Y_T\ge0\), and
\[
Y_T\le\frac{z^2+\tau^2-2z^2\tau^2}{(z+\tau)(1-z\tau)}<z+\tau<8/15. \tag{12}
\]
The exact lower-support identity is
\[
[Y_T-q(1-pL_4)]\mathcal D
=pc(L_4+D-2\mu)+p[(1-cD)+(pc-qs)(1-pL_4)]\ge0. \tag{13}
\]
Here \(pc-qs>0\) because \(K_zK_\tau<1\). The exchanged identity proves the other lower support. The second upper support requires \(Y_T\le p+q-pqL_4\), whose right side is at least \(p>209/241>8/15\); the same holds for \(W\). Thus this is an actual point of both squares. Immediately inward from the two first upper supports is an uncovered open wedge. Its positive-height points cannot be covered by \(F\), and the opposite-corner disjointness excludes \(V_1,V_2\) locally. The limiting-sequence argument of R40 gives
\[
Q_T\in C. \tag{14}
\]
If \(Y_T=0\), both top long legs being at least \(\mu\) force the intersection to be TOP midpoint, contradicting the midpoint prohibition on \(C\). Thus a remaining covering has \(Y_T>0\). The same original \(C\) contains \(P_L,P_R,Q_T\), permitting
\[
|\det(Q_T-P_L,P_R-P_L)|\le1
\]
and its two actual normal-width bounds. These are necessary conditions; the repeated-TOP-midpoint subclass is not closed here.

<a id="R42"></a>
## R42. A normalized seam point in the same central tile and a positive-rotation interval

**Scope and inputs.** The three-contact target is \([-\mu,\mu]^2\), \(\mu>1\), with \(V_1,V_2,V_4,W=V_3\) as before. The unique origin host \(C\) has no outer midpoint. The original \(F\) contains BOTTOM midpoint, lies entirely below the horizontal axis, and owns the complete bottom gap with its endpoints. The actual reaches satisfy \(u>38/79\) and \(l,r,u,d\le2-\mu<1\). In particular,
\[
\Sigma=S_1+S_2>2-\sqrt2>7/12. \tag{1}
\]

### 1. Actual geometric data

The legal normalized representatives of \(V_1,V_4\) have half-angles \(a,z\); \(C,F\) stay fixed. Set
\[
b=\frac{1+a^2}{1-a^2},\quad k=\frac{2a}{1-a^2},\quad
h=\frac{2z}{1-z^2},\quad G=g(z)=\frac{1-z}{1+z},\quad S=S_4.
\]
Here \(h=\lambda(z)\) is a slope, not the half-angle \(\eta\) of \(C\). Actual LEFT contact and corner projection caps give
\[
0<z<4/15,\quad z<a,\quad a+2z<1,\quad0<S<G,
\quad L_1>2-S,\quad S_1=b-kL_1. \tag{2}
\]
R40 supplies
\[
X_\mu=\frac{b+S-2\mu}{k-h},\quad e_\mu=\mu-S-hX_\mu,
\quad P_\mu=(-\mu+X_\mu,e_\mu)\in C\cap V_1, \tag{3}
\]
with \(0\le X_\mu<a\), \(e_\mu>0\). On the negative horizontal axis only \(C,V_1\) contribute. Hence the actual inward endpoint of \(V_1\) belongs to \(C\):
\[
Q_1=(-l_\mu,0),\qquad l_\mu=\mu-a+\frac{\mu-1}{k}. \tag{4}
\]
This auxiliary coordinate does not redefine the actual reach \(l\); rather, \(l\ge l_\mu\).

### 2. A normalized point belongs to the unchanged original \(C\)

Define, using the actual \(a,z,S\),
\[
X_1=\frac{b+S-2}{k-h},\quad e_1=1-S-hX_1,\quad
P_1=(-1+X_1,e_1). \tag{5}
\]
Then \(P_1\in C\) for every remaining configuration. This eliminates \(\mu\) without moving \(C\) or invoking a covering classification at \(\mu=1\).

Indeed \(b\ge L_1\), \(L_1+S\ge2\mu\) imply \(X_1>0\). Using \(b-ak=1\) and \(1-G=h(1-z)\),
\[
(k-h)(X_1-a)=S-1+ah<h(a+z-1)<0.
\]
Thus \(X_1<a\), and
\[
e_1>1-G-ha=h(1-z-a)>0. \tag{6}
\]
Furthermore
\[
e_\mu-e_1=(\mu-1)\left(1+\frac{2h}{k-h}\right)>0. \tag{7}
\]
The diameter of \(V_1\), containing \(P_\mu\) and the lower-left corner, gives
\[
0<e_1<e_\mu<\sqrt2-1<5/12<38/79<u. \tag{8}
\]
Hence \((0,e_1)\in C\). The first upper support of \(V_1\) yields
\[
\rho_\mu:=\mu-X_\mu=l_\mu+e_\mu/k,\quad
\rho_1:=1-X_1=(1-a)+e_1/k. \tag{9}
\]
The segment \(Q_1P_\mu\subset C\) meets height \(e_1\) at
\(Z=(-l_\mu-e_1/k,e_1)\). Since
\[
l_\mu-(1-a)=(\mu-1)(1+1/k)>0,
\]
the point \(P_1\) lies between \(Z\) and \((0,e_1)\). Convexity proves the assertion.

The original \(C\) also contains \((-(1-a),0)\). If it directly contains \(Q_U\), it contains \((0,1-z)\); if it directly contains \(Q_R\), it contains \((1-x,0)\). These are actual points in the unchanged tile. Similarly, translate the actual bottom line of \(F\) to height zero. Its complete bottom endpoints and negative-vertical handoff endpoint, shortened along segments in \(F\), show that it contains
\[
(-(1-S_1),0),\quad(1-S_2,0),\quad(0,1-d). \tag{10}
\]
This translation preserves the unit-square shape.

### 3. The positive-rotation projection

Now assume the normals of \(C\) are \((c,s),(-s,c)\), with \(c=\cos\theta\ge s>0\), and
\[
\eta=\tan(\theta/2),\quad K=\frac{2\eta}{1-\eta^2},\quad
1/3\le\eta\le9/25. \tag{11}
\]
If \(Q_U\in C\), then \(u>1-z\). The first-normal width between \(P_1\) and \((0,u)\) is at most one:
\[
c(1-X_1)+s(u-e_1)\le1.
\]
Using \((\sec\theta-1)/K=\eta\), with the strict inequality on \(u\), gives
\[
\widetilde Q_\eta(S):=S+(h-1/K)X_1<\eta+z. \tag{12}
\]
If also \(Q_R\in C\), the second normal gives \(sr+cu\le1\), hence
\[
r<\eta+z/K\le9/25+4z/3=:R(z)<1, \tag{13}
\]
because \(K\ge3/4\). Direct RIGHT contact then yields
\[
S_2<g(x)<q(r)<q(R(z)). \tag{14}
\]

### 4. Larger \(z\): an analytic exclusion

Set \(w=2z/(1+z)\). The two long-leg projections and \(L_1>2-G=1+w\) give
\[
S_1\le\Phi(w)=(1+w)(1-\sqrt{w(2+w)}). \tag{15}
\]
As in R41, the fixed-long-leg short-leg maximum occurs at \(\cos\theta=1/L\), and \(L(1-\sqrt{L^2-1})\) decreases with \(L\). Writing \(v=\sqrt{w(2+w)}\), we have \(\Phi'=1-2v-1/v<-7/4\). For \(z<4/15\), \(w'\ge450/361\), while
\[
\frac{d}{dz}q(R(z))=\frac{8/3}{(2-R(z))^2}
\le135000/83521<1575/722.
\]
Thus \(\Phi(w(z))+q(R(z))\) strictly decreases. At \(z_0=7/30\), it is
\[
\frac{51(37-4\sqrt{77})}{1369}+\frac{151}{299}<7/12. \tag{16}
\]
Consequently \(z\ge7/30\) is excluded by (1) and (14).

### 5. Small \(z\): concavity covers the full half-angle interval

For \(0<z\le7/30\), set
\[
A(z)=1/2-3z/4+4z^2/3,\qquad F(a,z)=b-k(2-G). \tag{17}
\]
Then \(S_1<F\), \(z<A(z)<1\), and
\[
F_a=\frac{4a-2(2-G)(1+a^2)}{(1-a^2)^2}<0.
\]
If \(a\ge g(\eta)\), then \(a\ge8/17\), and the source's full-interval positive-coefficient rational check gives
\[
S_1+q(R)<F(8/17,z)+q(R)<7/12. \tag{18}
\]
For \(a<g(\eta)\), we have \(k<1/K\). Thus \(\widetilde Q_\eta\) decreases in \(S\), and (12) requires
\[
D_\eta(a,z):=G+(h-1/K)X_G-\eta-z<0,\qquad
X_G=\frac{b+G-2}{k-h}>0. \tag{19}
\]
Positivity of \(X_G\) uses the actual facts \(b+S>2\), \(G>S\); it is not asserted on every auxiliary \(a\) value. At fixed actual \(a,z\),
\[
D_\eta=G+hX_G-z-H(\eta),\quad
H(\eta)=\eta(1-X_G/2)+\frac{X_G}{2\eta},\quad
H''=X_G/\eta^3>0.
\]
Thus \(D_\eta\) is concave in \(\eta\). Nonnegativity at \(1/3,9/25\) suffices for the whole closed interval.

For each endpoint define
\[
P_\eta(a,z)=D_\eta(a,z)(a-z)(1+az). \tag{20}
\]
After cancellation this is quadratic in \(a\), with strictly negative quadratic coefficient on \(0\le z\le7/30\), and the source establishes
\[
P_\eta(0,z)\ge0,\qquad P_\eta(A(z),z)\ge0. \tag{21}
\]
Concavity in \(a\) gives \(P_\eta\ge0\) for \(0\le a\le A(z)\). On the actual domain \(a>z\), the multiplied factor is positive, so \(D_\eta\ge0\) at both half-angle endpoints and hence throughout the interval, contradicting (19). Therefore \(a>A(z)\). Monotonicity of \(F\) and the second full-interval positive-coefficient check give
\[
S_1+q(R)<F(A(z),z)+q(R)<7/12. \tag{22}
\]
All \(a,z\) cases are covered, including both \(\eta\) endpoints. Equations (14) and (1) contradict the resulting \(\Sigma<7/12\).

### 6. Complete rational coefficient records

The coefficient records referenced above are supplied in
`artifacts/checkers/round42_interval_certificate.json`; their reconstruction
checker is `artifacts/checkers/check_round42.py`. The source narrative's
reference to this section is thus made explicit here. This is an editorial
completion from the existing certificate, not a new exclusion.

For each expression below, cancel it as a rational function and write
\(E_j=N_j/D_j\), choosing the sign so that \(D_j\) is positive at \(z=7/60\).
Put \(z=7v/30\). A listed coefficient vector \(b=(b_0,\ldots,b_n)\) denotes the
complete Bernstein expansion

\[
P(7v/30)=\sum_{i=0}^{n}b_i\binom ni v^i(1-v)^{n-i},\qquad 0\le v\le1.
\]

These are full-interval expansions, not values sampled at parameter points.
The vectors below are for the separate numerator and denominator polynomials
after this substitution. All denominator coefficients are strictly positive;
all numerator coefficients are nonnegative. The objective gaps, separator
and concavity coefficients have the stronger positivity used in the proof.

**Record 1: eta = 1/3 concavity.**

\[
E_{1}(z)=- \frac{5 z^{2}}{3} - \frac{4 z}{3} + \frac{4}{3}
\]

\[
\mathbf b_{N1}=\bigl(4,\ \frac{53}{15},\ \frac{503}{180}\bigr),\qquad n=2.
\]

\[
\mathbf b_{D1}=\bigl(3\bigr),\qquad n=0.
\]

**Record 2: eta = 1/3 at zero.**

\[
E_{2}(z)=- \frac{z \left(z - 2\right)}{3}
\]

\[
\mathbf b_{N2}=\bigl(0,\ \frac{7}{30},\ \frac{371}{900}\bigr),\qquad n=2.
\]

\[
\mathbf b_{D2}=\bigl(3\bigr),\qquad n=0.
\]

**Record 3: eta = 1/3 at separator.**

\[
E_{3}(z)=\frac{z^{2} \left(1280 z^{4} + 160 z^{3} - 367 z^{2} - 240 z + 156\right)}{432}
\]

\[
\mathbf b_{N3}=\left(\begin{gathered}0,\ 0,\ \frac{637}{1125},\ \frac{3479}{2250},\\\frac{32987633}{12150000},\ \frac{5531071}{1458000},\ \frac{170360701}{36450000}\end{gathered}\right),\qquad n=6.
\]

\[
\mathbf b_{D3}=\bigl(432\bigr),\qquad n=0.
\]

**Record 4: eta = 9/25 concavity.**

\[
E_{4}(z)=- \frac{319 z^{2}}{225} - \frac{322 z}{225} + \frac{272}{225}
\]

\[
\mathbf b_{N4}=\bigl(272,\ \frac{7033}{30},\ \frac{161549}{900}\bigr),\qquad n=2.
\]

\[
\mathbf b_{D4}=\bigl(225\bigr),\qquad n=0.
\]

**Record 5: eta = 9/25 at zero.**

\[
E_{5}(z)=- \frac{z \left(47 z - 128\right)}{225}
\]

\[
\mathbf b_{N5}=\bigl(0,\ \frac{224}{15},\ \frac{24577}{900}\bigr),\qquad n=2.
\]

\[
\mathbf b_{D5}=\bigl(225\bigr),\qquad n=0.
\]

**Record 6: eta = 9/25 at separator.**

\[
E_{6}(z)=\frac{5104 z^{6}}{2025} + \frac{422 z^{5}}{405} - \frac{40829 z^{4}}{32400} - \frac{2443 z^{3}}{5400} + \frac{761 z^{2}}{1350} - \frac{11 z}{75} + \frac{4}{225}
\]

\[
\mathbf b_{N6}=\left(\begin{gathered}576,\ \frac{1956}{5},\ \frac{306778}{1125},\ \frac{19004771}{90000},\\\frac{2299251511}{12150000},\ \frac{1351274639}{7290000},\ \frac{34785413359}{182250000}\end{gathered}\right),\qquad n=6.
\]

\[
\mathbf b_{D6}=\bigl(32400\bigr),\qquad n=0.
\]

**Record 7: objective low branch.**

\[
E_{7}(z)=\frac{793600 z^{6} - 614528 z^{5} - 1364484 z^{4} + 2558847 z^{3} - 1305009 z^{2} + 166536 z + 4860}{\left(12 z + 12\right) \left(100 z - 123\right) \left(16 z^{2} - 9 z - 6\right) \left(16 z^{2} - 9 z + 18\right)}
\]

\[
\mathbf b_{N7}=\left(\begin{gathered}4860,\ \frac{56682}{5},\ \frac{19614151}{1500},\ \frac{2106799867}{180000},\\\frac{17368689901}{2025000},\ \frac{171657060391}{36450000},\ \frac{15184751623}{18225000}\end{gathered}\right),\qquad n=6.
\]

\[
\mathbf b_{D7}=\left(\begin{gathered}159408,\ \frac{833832}{5},\ \frac{4307501}{25},\ \frac{528446249}{3000},\\\frac{30114810331}{168750},\ \frac{544719723361}{3037500},\ \frac{271600975633}{1518750}\end{gathered}\right),\qquad n=6.
\]

**Record 8: objective high branch.**

\[
E_{8}(z)=\frac{327700 z^{2} - 157971 z - 423}{\left(100 z - 123\right) \left(900 z + 900\right)}
\]

\[
\mathbf b_{N8}=\bigl(423,\ \frac{377059}{20},\ \frac{1749731}{90}\bigr),\qquad n=2.
\]

\[
\mathbf b_{D8}=\bigl(110700,\ 113115,\ 110630\bigr),\qquad n=2.
\]

**Record 9: separator above z.**

\[
E_{9}(z)=\frac{4 z^{2}}{3} - \frac{7 z}{4} + \frac{1}{2}
\]

\[
\mathbf b_{N9}=\bigl(6,\ \frac{71}{20},\ \frac{887}{450}\bigr),\qquad n=2.
\]

\[
\mathbf b_{D9}=\bigl(12\bigr),\qquad n=0.
\]

All nine rational targets, eighteen polynomial reconstructions and fifty-six
coefficients were rechecked directly from these expressions in the present
editorial pass. Fourteen supporting identities, six exact comparisons and
two local linear counterexample queries also passed that checker. These
arithmetic facts do not replace the geometric applicability established in
Sections 1--5, and do not prove other rotation bands or joining modes.

<a id="R43"></a>
## R43. Small-angle double-direct exclusion for both rotations

**Scope and inputs.** In the same actual three-contact configuration, \(C\) is the unique origin host with no outer midpoint, \(F\subset\{y<0\}\), and the complete bottom gap with both endpoints belongs to that original \(F\). The same tile gives
\[
\Sigma=S_1+S_2>2-\sqrt2>7/12,\qquad\Sigma>(1-d)^2,\quad d<1. \tag{1}
\]
Both positive-axis contacts of \(C\) are direct throughout this module.

### 1. Actual corner bounds

With half-angles \(a,z\), let \(b=(1+a^2)/(1-a^2)\), \(k=2a/(1-a^2)\), \(G=(1-z)/(1+z)\), and \(q(t)=t/(2-t)\). LEFT contact gives
\[
S_1<F(a,z):=b-k(2-G). \tag{2}
\]
Here \(0<z<4/15\), \(0<a<1\), with legal caps
\[
a\le2/5:\ z<Y_c(a)=\frac{a^2}{1-2a^2};\qquad
a\ge2/5:\ z<Y_s(a)=\frac{(1-a)^2}{6a-1-a^2}. \tag{3}
\]
Only \(a\le1/3\) uses the first cap and only \(a\ge1/2\) uses the second. The negative horizontal handoff gives \(l>1-a\); double-direct contact gives \(u>1-z\), \(r>1-x\), and
\[
S_2<q(r). \tag{4}
\]
The strict inequalities retain \(\mu>1\).

### 2. Common bounds for the two rotations

Write \(c=\cos\theta\ge s=\sin\theta\ge0\), with normals \((c,s),(-s,c)\) or \((c,-s),(s,c)\). Set
\[
\eta=\tan(\theta/2)\in[0,1/8],\quad K=s/c=\frac{2\eta}{1-\eta^2},\quad
\delta=1/c-1=\eta K.
\]
Then
\[
0\le K\le16/63<1/3,\qquad0\le\delta\le2/63. \tag{5}
\]
The horizontal and vertical chord projections, \(c(l+r)\le1\), \(c(u+d)\le1\), imply in either orientation
\[
r<a+\delta,\qquad d<z+\delta. \tag{6}
\]
Since \(1-z-\delta>0\),
\[
\Sigma>(1-z-\delta)^2. \tag{7}
\]
When \(a+\delta<1\), a contradiction follows if
\[
E_\delta(a,z):=(1-z-\delta)^2-F(a,z)-q(a+\delta)\ge0. \tag{8}
\]
The possible \(a+\delta\ge1\) case is handled separately below.

### 3. Three analytic bounds for the unrotated surplus

Let
\[
E=(1-z)^2-F(a,z)-q(a),\qquad
I(a)=\frac{3a(1-a)}{(1+a)(2-a)}.
\]
Direct algebra gives
\[
E=I+z^2-2z+\frac{2kz}{1+z},\qquad
E_z=\frac{2[k-(1-z)(1+z)^2]}{(1+z)^2}. \tag{9}
\]
If \(0<a\le1/3\), then \(k\le3/4\), \(z\le Y_c\le1/7\), and \((1-z)(1+z)^2\ge1\). Thus \(E\) decreases in \(z\), and
\[
E(a,z)\ge E(a,Y_c(a))>13a/20. \tag{10}
\]
For the final comparison, the source clears the rational expression \([E(a,Y_c(a))-13a/20]/a\), substitutes \(a=v/3\), \(0\le v\le1\), and reports ten strictly positive rational Bernstein coefficients each for numerator and denominator, with independent polynomial-identity reconstruction. Division by \(a\) occurs only at actual \(a>0\); zero is used solely for the continuous certificate extension.

If \(1/3\le a\le1/2\), then \(I\ge3/10\), \(k\ge3/4\), so
\[
E\ge3/10+z^2-31z/38\ge1313/8550. \tag{11}
\]
The quadratic decreases on \([0,4/15]\); \(I\ge3/10\) is equivalent to \(9a(1-a)\ge2\) on the stated interval.

If \(1/2\le a<1\), then \(k\ge4/3>32/27\), the global maximum of \((1-z)(1+z)^2\). Hence \(E\) increases in \(z\), and
\[
E\ge I\ge\frac23(1-a). \tag{12}
\]
The latter comparison is equivalent, after positive denominator clearing, to \((2a-1)(a+4)\ge0\).

### 4. Small and intermediate \(a\)

The rotation loss is exactly
\[
E_\delta-E=-2\delta(1-z)+\delta^2-[q(a+\delta)-q(a)]. \tag{13}
\]
If \(a\le1/3\), then \(a+\delta<1/2\), so \(q'\le1\) and
\[
E_\delta\ge E-3\delta. \tag{14}
\]
At \(\eta=0\), (10) is enough. For \(\eta>0\), positive rotation gives, from the first normal on \((-l,0),(0,u)\), \(l+Ku\le1+\delta\). Thus
\[
a>K(1-z-\eta)\ge(73/120)K,\quad
3\delta<45a/73<13a/20.
\]
For negative rotation the second normal gives \(Kl+u\le1+\delta\), whence
\[
z>K(1-a-\eta)\ge(13/24)K.
\]
Since \(Y_c\le3a/7\), \(K<72a/91\), and
\[
3\delta<27a/91<13a/20.
\]
In both orientations (10) and (14) imply \(E_\delta>0\). If \(1/3\le a\le1/2\), then \(a+\delta<1\) and \(q'\le2\), so
\[
E_\delta\ge E-4\delta\ge1313/8550-8/63>0. \tag{15}
\]
All \(a\le1/2\) cases are excluded with the appropriate normal for each rotation.

### 5. Large \(a\), including the extreme long-leg case

Let \(\epsilon=1-a>0\). If \(\epsilon\ge6\delta\), then \(a+\delta<1\), and
\[
E_\delta\ge\frac23\epsilon-4\delta\ge0. \tag{16}
\]
Even equality contradicts (7), because the bounds \(S_1<F\), \(S_2<q(a+\delta)\) are strict.

It remains that \(\epsilon<6\delta\), so \(\eta,K>0\). The sine cap in (3), whose denominator is at least \(7/4\), gives
\[
z<\frac47\epsilon^2<\frac{144}{7}\delta^2,\qquad
\frac zK<\frac{144}{7}\eta^2K\le4/49<1/10. \tag{17}
\]
Also
\[
S_1<g(a)=\frac\epsilon{2-\epsilon}<\frac{3\delta}{1-3\delta}\le2/19. \tag{18}
\]
For positive rotation, the second normal on \((r,0),(0,u)\) gives \(Kr+u\le1+\delta\), hence
\[
r<\eta+z/K<1/8+4/49<1/4.
\]
Thus \(\Sigma<2/19+q(1/4)=2/19+1/7<7/12\), contrary to (1).

For negative rotation, the first normal gives \(r+Ku\le1+\delta\), so
\[
r<1-K(1-\eta-z)<1-4K/5. \tag{19}
\]
Here \(1-\eta-z>4/5\) follows from \(\eta\le1/8\), \(z<K/10\), \(K<1/3\). Therefore
\[
q(r)<1-\frac{8K/5}{1+4K/5}\le1-24K/19<1-6K/5. \tag{20}
\]
The unweakened estimate in (18) is
\[
S_1<\frac{3\delta}{1-3\delta}\le63K/152<K/2,
\]
so
\[
\Sigma<1-7K/10. \tag{21}
\]
On the other hand, (7), \(z<K/10\), and \(\delta\le K/8\) give
\[
\Sigma>(1-z-\delta)^2\ge1-2(z+\delta)>1-9K/20. \tag{22}
\]
Since \(K>0\), these bounds conflict. This completes the double-direct exclusion for both rotations throughout \(\eta\in[0,1/8]\).

<a id="R44"></a>
## R44. A forced top seam point for an upper bridge without repeated TOP midpoint

**Scope and inputs.** The target and selected hosts are the actual three-contact configuration on \([-\mu,\mu]^2\), \(\mu>1\). The unique origin tile \(C\) has no outer midpoint, and \(F\subset\{y<0\}\). The actual reaches obey \(l>1-a\), \(a+2z<1\), hence
\[
l>2z,\qquad0<z<4/15. \tag{1}
\]
Assume the original \(W\) contains the actual upper-axis endpoint \(Q_U=(0,\mu-U_4)\), where \(U_4<z\). If \(Q_U\notin C\), closed coverage of the positive vertical axis forces \(W\) to contain both \(Q_U\) and \(U_C\). Sections 1--4 need only the first membership.

### 1. A legal representative of \(W\)

Keep \(C,F\) and the other corner tiles fixed. In inward coordinates \(X'=\mu-x,Y=\mu-y\), a target-relative dominating replacement gives
\[
0\le cX'+sY\le1,\qquad-\beta\le-sX'+cY\le1-\beta,
\quad c,s>0,\quad c^2+s^2=1. \tag{2}
\]
An axis-aligned tile cannot reach \(Q_U\) across \(X'=\mu>1\). The first original projection interval is \([\alpha,\alpha+1]\), with \(\alpha\le0\); moving it to \([0,1]\) preserves every old target point because \(X',Y\ge0\). The orthogonal interval remains unchanged, with \(0\le\beta\le1\).

If the new \(W\) contains TOP midpoint, use the established top-anchored dominating representative. Otherwise its actual top leg \(D<\mu\). The first support at \(Q_U\) gives \(c\mu<1\), so \(1/c>\mu\), and \(D=\min(1/c,\beta/s)=\beta/s\). Thus in either surviving branch one can use
\[
\beta=sD. \tag{3}
\]
A newly acquired RIGHT midpoint must be reclassified into the previously excluded near host-selection class; this branch transfer, rather than an invariance claim, is the premise required here. If \(A\) is the actual right leg and \(p=c_z,q=s_z\),
\[
A\le(1-\beta)/c,\quad L_2+A\ge2\mu,\quad L_4+D\ge2\mu,
\quad cD\le1,\quad pL_4\le1. \tag{4}
\]
In particular \(D\ge\mu\) is not assumed.

### 2. A fresh angle cap from the actual \(Q_U\)

Let \(\tau=(1-c)/s\in(0,1)\), so \(c=(1-\tau^2)/(1+\tau^2)\), \(s=2\tau/(1+\tau^2)\). At \(Q_U\), the second lower support gives \(\beta\ge s\mu-cU_4\), whence
\[
A\le\frac{1-s\mu}{c}+U_4<g(\tau)+z. \tag{5}
\]
RIGHT contact and \(L_2\le\sqrt2\) give \(A>2-\sqrt2>7/12\), so \(g(\tau)>19/60\) and
\[
0<\tau<41/79. \tag{6}
\]
This is derived for the actual free \(W\), without importing an anchored angle cap. In particular,
\[
z+\tau+z\tau<73/79<1,\quad pc-qs>0, \tag{7}
\]
\[
p>209/241>41/79,\quad c>2280/3961>41/79. \tag{8}
\]

### 3. Verifying the top seam in both actual squares

The supports of \(V_4\), in \(X=x+\mu,Y=\mu-y\), are
\[
0\le pX+qY\le1,\quad-qL_4\le-qX+pY\le1-qL_4.
\]
Intersect the two first upper supports:
\[
\mathcal D=cq+ps>0,\quad Y_\mu=\frac{p+c-2\mu pc}{\mathcal D},\quad
X_\mu=\frac{1-qY_\mu}{p},\quad Q_\mu=(X_\mu-\mu,\mu-Y_\mu). \tag{9}
\]
The first projection of \(W\) is also one because \(X'=2\mu-X_\mu\). Equation (4) gives
\[
p+c-2\mu pc=pc[(1/p-L_4)+(1/c-D)+(L_4+D-2\mu)]\ge0.
\]
Thus \(Y_\mu\ge0\). Its \(\mu=1\) algebraic value satisfies
\[
Y_\mu<Y_1=\frac{z^2+\tau^2-2z^2\tau^2}{(z+\tau)(1-z\tau)}
\le\max(z,\tau)<41/79. \tag{10}
\]
The maximum bound follows from the exact differences
\[
\tau-Y_1=\frac{z(\tau-z)(1-\tau^2)}{(z+\tau)(1-z\tau)}\quad(\tau\ge z),
\]
\[
z-Y_1=\frac{\tau(z-\tau)(1-z^2)}{(z+\tau)(1-z\tau)}\quad(z\ge\tau).
\]
Hence \(Y_\mu<\min(p,c)\), and the intersection is a positive-height target point. The remaining lower supports follow from
\[
[Y_\mu-q(1-pL_4)]\mathcal D
=pc(L_4+D-2\mu)+p[(1-cD)+(pc-qs)(1-pL_4)]\ge0, \tag{11}
\]
\[
[Y_\mu-s(1-cD)]\mathcal D
=pc(L_4+D-2\mu)+c[(1-pL_4)+(pc-qs)(1-cD)]\ge0. \tag{12}
\]
The upper supports require \(Y_\mu\le p+q-pqL_4\), \(Y_\mu\le c+s-csD\); their right sides are at least \(p,c\). Thus \(Q_\mu\in V_4\cap W\) as actual squares.

### 4. Full coverage forces this point into the original \(C\)

Increasing \(Y\) by a sufficiently small positive amount at fixed \(X\) violates both first upper supports and gives an interior sequence converging to \(Q_\mu\). Its height remains positive, excluding \(F\). Opposite-corner disjointness excludes \(V_1\) locally because \(Q_\mu\in W\), and \(V_2\) locally because \(Q_\mu\in V_4\). Closedness and complete coverage give
\[
Q_\mu\in C. \tag{13}
\]
The endpoint \(Y_\mu=0\) is retained: the inward sequence still works at TOP. Without two top legs at least \(\mu\), it need not be TOP midpoint. No angle of \(C\), direct \(Q_R\) contact, repeated midpoint, or shared-origin chord premise is needed.

### 5. A normalized top point when \(R_C\in W\)

Suppose additionally \(R_C=(r,0)\in W\), as occurs for two \(W\) bridges. Define
\[
Q_1=(x_1,y_1),\quad x_1=\frac{2z\tau(z-\tau)}{(z+\tau)(1-z\tau)},\quad
y_1=\frac{(1-z)(1-\tau)(2z\tau+z+\tau)}{(z+\tau)(1-z\tau)}. \tag{14}
\]
Set \(\epsilon=\mu-1>0\), \(v_x=(qc-ps)/\mathcal D\), \(v_y=1+2pc/\mathcal D>0\). Then
\[
Q_\mu=Q_1+\epsilon(v_x,v_y). \tag{15}
\]
The line meets the horizontal axis at \(A_0=(a_0,0)\), where
\[
a_0=x_1-y_1v_x/v_y=\frac{(\tau-z)(1-z-\tau-z\tau)}{N}, \tag{16}
\]
\[
N=(z+\tau)(1-z\tau)+(1-z^2)(1-\tau^2)
=\frac{(1+z^2)(1+\tau^2)}2(\mathcal D+2pc)>0.
\]
If \(\tau\ge z\), then \(a_0\ge0\), and the first support at \(R_C\) gives
\[
r>\frac{c+s-1}{c}=1-g(\tau). \tag{17}
\]
The exact identity
\[
1-g(\tau)-a_0=\frac{(1-z)(1+2\tau-\tau^2)(2z\tau+z+\tau)}{(1+\tau)N}>0 \tag{18}
\]
places \(a_0<r\). If \(\tau\le z\), then \(a_0\le0\), \(Y_1\le z\), \(x_1\ge0\), \(v_x\ge0\), and \(0<y_1<1\), so
\[
a_0>-\frac{qc}{\mathcal D+2pc}>-\frac q{2p}
=-\frac z{1-z^2}>-2z>-l. \tag{19}
\]
The last steps use \(z^2<1/2\) and (1). Thus always \(A_0\in C\), including \(\tau=z\). Finally
\[
Q_1=\alpha Q_\mu+(1-\alpha)A_0,\qquad
\alpha=\frac{y_1}{\mu-Y_\mu}\in(0,1). \tag{20}
\]
Convexity gives
\[
Q_1\in C. \tag{21}
\]
This is a true point of the original tile; neither moving \(C\) nor rescaling the squares is involved.

<a id="R45"></a>
## R45. Excluding two bridges by \(W\) and reducing four mechanisms to three

**Scope.** Retain the actual three-contact configuration, the original \(C,F\), and \(F\)'s empty horizontal chord. Initially suppose the original upper-right \(W\) contains \(Q_U\). The half-angles of \(V_2,V_4\) are \(x,z\), with \(0<z<4/15\).

### 1. Actual inputs and legal normalization

The actual endpoint of \(V_4\) is \(Q_U=(0,\mu-U(z))\), where
\[
U(t)=t-\frac{\mu-1}{K_t},\qquad K_t=\frac{2t}{1-t^2}. \tag{1}
\]
Use the R44 representative, preserving original target points and keeping \(C,F\) fixed:
\[
0\le cX'+sY\le1,\qquad-sD\le-sX'+cY\le1-sD, \tag{2}
\]
where \(X'=\mu-x_{\rm global},Y=\mu-y_{\rm global}\), \(c=(1-\tau^2)/(1+\tau^2)>0\), \(s=2\tau/(1+\tau^2)>0\). Its actual legs obey
\[
cA+sD\le1. \tag{3}
\]
For no TOP midpoint, \(\beta=sD\) follows directly from \(D<\mu\) and the support at \(Q_U\); otherwise use the legal anchored form. Empty contribution on the target horizontal segment need not imply that the original tile misses the entire infinite line; only its target contribution will be needed. Actual contacts and long-leg caps give
\[
L_2+A\ge2\mu,\quad L_4+D\ge2\mu,\quad L_2\le\sqrt2,\quad
L_4\le b_z=\frac{1+z^2}{1-z^2}. \tag{4}
\]
R44 gives
\[
A>7/12,\quad A<g(\tau)+z,\quad\tau<41/79. \tag{5}
\]

### 2. The stronger angle cap \(z\le\tau<2/5\)

The first upper support at \(Q_U\), \(c\mu+sU(z)\le1\), is equivalent to \(U(z)\le U(\tau)\). Since
\[
U'(t)=1+\frac{\mu-1}{2}+\frac{\mu-1}{2t^2}>0,
\]
we obtain
\[
\tau\ge z. \tag{6}
\]
Because \(b_z<241/209\), TOP contact gives \(D>177/209\). Together with (3) and \(A>7/12\),
\[
(7/12)c+(177/209)s<1. \tag{7}
\]
If \(\tau\ge2/5\), this requires
\[
f(\tau)=-5/12+(354/209)\tau-(19/12)\tau^2<0.
\]
But \(f\) is concave and its endpoint values on \([2/5,41/79]\) are \(157/20900>0\) and \(46848/1304369>0\). Thus
\[
0<z\le\tau<2/5. \tag{8}
\]
Concavity proves the whole interval, rather than sampling two angles.

### 3. A tile \(W\) containing \(Q_U\) has no horizontal target contribution

If the normalized tile met \(Y=\mu\), its first and second upper supports would require
\[
X'\le(1-s\mu)/c,\qquad X'\ge D+(c\mu-1)/s.
\]
Compatibility requires
\[
D\le B_\mu(\tau):=\frac{c+s-\mu}{cs}. \tag{9}
\]
This keeps the position of the floating chord. Since \(\mu>1\),
\[
B_\mu(\tau)<B_1(\tau)=\frac{1+\tau^2}{1+\tau},\quad
B_1'(\tau)=\frac{\tau^2+2\tau-1}{(1+\tau)^2}<0
\]
on \((0,2/5)\). Therefore \(B_1(\tau)\le B_1(z)\). TOP contact gives \(D>2-1/p\), \(p=c_z\), and
\[
2-1/p-B_1(z)=\frac{z(z^2-4z+1)}{1-z^2}>0. \tag{10}
\]
Indeed the decreasing numerator polynomial has value \(1/225>0\) at \(4/15\). Thus
\(D>2-1/p>B_1(z)\ge B_1(\tau)>B_\mu(\tau)\), contradicting (9). Even tangency is excluded. The normalized tile misses the entire horizontal line; domination implies that the original tile has no target horizontal contribution.

### 4. Exclusion of two \(W\) bridges

On the horizontal target segment \(F,V_4\) contribute nothing, \(V_1\) contributes only on the negative side, and \(V_2\) covers the outer positive end. If \(Q_R\notin C\), closed coverage forces the original \(W\) to bridge \(R_C\) and \(Q_R\), so its target horizontal contribution is nonempty. By Section 3 it cannot contain \(Q_U\). Thus \(Q_U\notin C\) is impossible too, since that would force \(Q_U\in W\). Hence
\[
Q_R\in C\quad\hbox{or}\quad Q_U\in C. \tag{11}
\]
This uses neither the angle nor rotation of \(C\), nor repeated TOP midpoint. The remaining mechanisms are double-direct; direct \(Q_R\) with an upper \(W\) bridge (whose horizontal contribution is empty); and direct \(Q_U\) with a right \(W\) bridge (whose \(W\) cannot contain \(Q_U\)). Only the fourth, two-bridge mechanism is closed here.

### 5. The same corner chain forces \(x<g(\tau)\)

Continue assuming \(Q_U\in W\). If \(x\ge g(\tau)\), monotonicity of half-angle sine and \(s_{g(\tau)}=c\) give \(L_2\le1/c\). Contacts then imply \(A\ge2\mu-1/c\), \(D\ge2\mu-1/p\). Equation (3) gives \(2\mu(c+s)\le2+s/p\). Since \(\mu>1\),
\[
2(c+s-1)<s/p,\quad
\tau>1-1/(2p)>177/418>2/5.
\]
The last margin is \(49/2090>0\), a contradiction. Therefore
\[
x<g(\tau). \tag{12}
\]
This does not imply \(x<\tau\) and supplies no reflected general right-seam bound.

### 6. The normalized top point for every \(W\) containing \(Q_U\)

Section 3 forces \(Q_R\in C\). Monotonicity of \(U\) and (12) give
\[
r\ge\mu-U(x)>\mu-U(g(\tau))
=\frac{(c+s)\mu-1}{c}>1-g(\tau). \tag{13}
\]
R44 already gives \(Q_\mu\in C\). Its normalized point is
\[
Q_1=\left(\frac{2z\tau(z-\tau)}{(z+\tau)(1-z\tau)},
\frac{(1-z)(1-\tau)(2z\tau+z+\tau)}{(z+\tau)(1-z\tau)}\right).
\]
The line intercept is \(a_0=(\tau-z)(1-z-\tau-z\tau)/N\), with
\(N=(z+\tau)(1-z\tau)+(1-z^2)(1-\tau^2)>0\). Since \(\tau\ge z\), the positive-factor identity of R44 gives \(0\le a_0<1-g(\tau)<r\). Thus \((a_0,0)\in C\), and the same exact convex combination proves
\[
Q_1\in C. \tag{14}
\]
Membership of \(R_C\) in \(W\) is no longer needed: the actual RIGHT corner chain and direct \(Q_R\) contact provide the required reach bound. In the upper-bridge representative \(Q_U\notin C\), equality \(\tau=z\) would make \(Q_\mu=Q_U\), impossible. Hence there
\[
z<\tau<2/5,\quad r>1-g(\tau),\quad u>1-\tau.
\]
The last inequality is the first support at the actual \(U_C\in W\). The same original \(C\) contains both R42's left point \(P_1\) and this top point \(Q_1\); its actual normal widths and the same \(F\)'s bottom budget may be combined.

<a id="R46"></a>
## R46. Rotation separation for an upper bridge and actual lower interfaces of \(C,F\)

**Scope.** Use the actual three-contact form and legal R45 representative, keeping the original \(C,F\). The complete bottom gap and its endpoints belong to \(F\), whose horizontal chord is empty. Sections 1--4 assume \(Q_U\in W\); Section 5 is universal in the remaining form; Section 6 again assumes \(Q_U\in W\).

### 1. Inputs when \(W\) contains \(Q_U\)

The previous modules give
\[
z\le\tau<2/5,\quad z<4/15,\quad c_\tau A+s_\tau D\le1,
\quad L_4+D\ge2\mu,\quad L_2+A\ge2\mu. \tag{1}
\]
The target horizontal contribution of \(W\) is empty, so \(Q_R\in C\). In either direct or bridged upper contact,
\[
u>1-\tau: \tag{2}
\]
direct contact gives \(u>1-z\ge1-\tau\), and a bridge gives the first support at \(U_C\in W\). Use \(K_t=2t/(1-t^2)\), \(b_t=(1+t^2)/(1-t^2)\), \(g(t)=(1-t)/(1+t)\), \(q(t)=t/(2-t)\), and \(\Delta_z=b_z-1\).

### 2. The actual long-leg inequality \(L_2>1+\tau\)

From \(A\le b_\tau-K_\tau D\) and both contacts,
\[
L_2\ge2\mu-b_\tau+K_\tau(2\mu-L_4)
>2-b_\tau+K_\tau(2-b_z).
\]
The last quantity minus \(1+\tau\) is exactly
\[
\frac{\tau[(1-\tau)^2-2\Delta_z]}{1-\tau^2}. \tag{3}
\]
Its bracket exceeds \(9/25-64/209=281/5225>0\). Thus
\[
L_2>1+\tau, \tag{4}
\]
and the actual short leg satisfies
\[
S_2<g(x)-K_x\tau. \tag{5}
\]
The two long-leg projections also give
\[
\tau<\frac{2x^2}{1-x^2},\qquad\tau<\frac{(1-x)^2}{2x}. \tag{6}
\]
These depend on the same leg budget and both actual contacts, not merely on existence of an axial chord.

### 3. A full two-parameter surplus bound

For \(0<x<1\), \(0<\tau<2/5\), under (6), set
\[
E(x,\tau)=(1-\tau)^2-q(x)-g(x)+K_x\tau.
\]
Then
\[
E(x,\tau)>\tau/8. \tag{7}
\]
Indeed, with
\[
I(x)=\frac{3x(1-x)}{(1+x)(2-x)},\quad
\mathcal E=E-\tau/8=I+(K_x-17/8)\tau+\tau^2, \tag{8}
\]
the following analytic intervals cover the domain. For \(0<x\le2/5\), put \(T_c=2x^2/(1-x^2)\). Throughout \(\tau\le T_c\),
\[
\mathcal E_\tau\le20/21-17/8+16/21=-23/56<0.
\]
It suffices to check \(\mathcal E(x,T_c)/x>0\). Its numerator and denominator have strictly positive rational Bernstein coefficients on the complete interval \([0,2/5]\); the degree-three numerator is elevated to degree twelve, with no subdivision. For \(2/5\le x\le3/7\), use \(\tau\le2/5\), giving
\[
\mathcal E_\tau\le21/20-17/8+4/5=-11/40<0,
\]
and the full-interval positive-coefficient check of \(\mathcal E(x,2/5)>0\). For \(3/7\le x\le1/2\), put \(T_s=(1-x)^2/(2x)\); the full-interval rational checks are
\[
K_x-17/8+2T_s<0,\qquad \mathcal E(x,T_s)>0.
\]
For \(1/2\le x\le2/3\), \(I\ge3/10\), \(K_x\ge4/3\), so
\[
\mathcal E\ge3/10+\tau^2-(19/24)\tau\ge3/10-(19/48)^2>0.
\]
For \(x\ge2/3\), \(K_x\ge12/5>17/8\), and every term in (8) is nonnegative, with \(I>0\). The source reports independent reconstruction of eight numerator/denominator identities for the four rational checks and 45 strictly positive rational coefficients. These are full-interval certificates, not sampled angles.

### 4. Rotation of the central tile is separated from zero

Let \(\theta_C\in[0,45^\circ]\) be the smaller axis angle of \(C\), and \(\delta=\sec\theta_C-1\), allowing either rotation. Suppose
\[
\delta\le\tau/32. \tag{9}
\]
Then \(\delta\le1/80\). The actual horizontal chord of \(C\), containing both corner endpoints, satisfies
\[
2\mu-U(a)-U(x)\le h_C\le1+\delta,
\]
so \(a+x>1-\delta\). Also \(x+\delta<1\): this is immediate if \(x\le1/2\); if \(x>1/2\), (6) gives \(\tau<(1-x)^2/(2x)<1-x\). Monotonicity of \(g\) yields
\[
S_1<g(a)<q(x+\delta),\quad
\Sigma<q(x+\delta)+g(x)-K_x\tau. \tag{10}
\]
The actual vertical chord gives \(u+d\le1+\delta\), so by (2), \(d<\tau+\delta\). The same \(F\) then requires
\[
\Sigma>(1-d)^2>(1-\tau-\delta)^2. \tag{11}
\]
Since \(q'\le2\) on \([x,x+\delta]\),
\[
(1-\tau-\delta)^2-q(x+\delta)-g(x)+K_x\tau
\ge E(x,\tau)-4\delta>\tau/8-4\delta\ge0,
\]
contradicting (10)--(11). Therefore
\[
\sec\theta_C-1>\tau/32. \tag{12}
\]
In particular axial \(C\) is excluded in all current cases with \(Q_U\in W\), even when \(Q_U\in C\) too. No such conclusion is transferred to a general right bridge.

### 5. A universal lower-left interface point

This section drops \(Q_U\in W\). A tile containing the LEFT chord of length at least \(\mu\) cannot have a point with \(x\ge0\): the triangle formed with that chord would have area at least \(\mu^2/2>1/2\), impossible in a unit square. Thus the entire \(V_1\) lies in \(x<0\); similarly \(V_2\subset\{x>0\}\), \(V_4\subset\{y>0\}\). The opposite-corner tiles \(V_1,W\) are disjoint.

Put \(p=c_a,s=s_a,L=L_1,S=S_1\). In \(X=x+\mu,Y=y+\mu\),
\[
0\le sX+pY\le1,\qquad-sL\le pX-sY\le1-sL.
\]
The inward boundary polyline \(\Gamma_1\) runs from
\(Q_L=(-l_\mu,0)\), \(l_\mu=\mu-a+(\mu-1)/K_a\), through
\[
M_1=(X_v-\mu,Y_v-\mu),\quad
X_v=s+p(1-sL),\quad Y_v=p-s(1-sL), \tag{13}
\]
to \(B_1=(-\mu+S_1,-\mu)\). Its vertex is strictly inside the lower-left target quadrant, as shown by
\[
X_v-\mu=-(1-p)(1-s)-(\mu-1)(1+ps)-ps(L-\mu)<0,
\]
\[
Y_v-(p+s-1)=(1-s)^2+s^2(L-1)>0,
\quad\mu-Y_v=(\mu-p)+s(1-sL)>0.
\]
Also \(X_v\ge s>0\), \(Y_v>0\), so both segments stay in the target and, except at endpoints, have \(-\mu<y<0\), \(x<0\).

Every point of \(\Gamma_1\) belongs to \(C\cup F\). For an interior point \(P\notin C\), closedness gives a neighborhood missing \(C\). The points \(P+(\epsilon,0)\), \(\epsilon\downarrow0\), violate the corresponding upper support of \(V_1\), remain in the lower-left quadrant, and cannot lie in \(V_2,V_4\). Closed disjointness of \(W,V_1\) excludes \(W\) locally. Coverage therefore puts this sequence in \(F\); closedness gives \(P\in F\). The endpoints already belong to \(C\) and \(F\), respectively.

At \(Q_L\), \(F\) is absent, while at \(B_1\), \(C\) is absent. Following the polyline from \(Q_L\), its first exit from \(C\), together with the two closedness conditions, gives an actual point
\[
E_1\in\partial C\cap F\cap\partial V_1,\quad
-\mu<x(E_1)<0,\quad-\mu<y(E_1)<0. \tag{14}
\]
If \(y(E_1)=-t_1\), its only two possible position formulas are
\[
x(E_1)=\begin{cases}
-l_\mu+t_1/K_a,&0<t_1\le\mu-Y_v,\\
-\mu+S_1+K_a(\mu-t_1),&\mu-Y_v\le t_1<\mu.
\end{cases} \tag{15}
\]
They agree at the vertex. No active face of \(C\) has yet been chosen; in particular \(t_1\) is not automatically \(d\).

### 6. A right interface and five actual points in the same \(F\)

If \(Q_U\in W\), its normalized tile misses the whole horizontal line and contains the upper-right corner, so lies wholly in \(y>0\). The other placements above remain valid. Reflect the inward polyline argument for \(V_2\), from \(Q_R\in C\) to \(B_2=(\mu-S_2,-\mu)\), moving slightly left to leave \(V_2\). All other corner tiles are excluded in the lower-right quadrant. Thus
\[
E_2\in\partial C\cap F\cap\partial V_2,\quad
0<x(E_2)<\mu,\quad-\mu<y(E_2)<0. \tag{16}
\]
Its formulas are the reflection of (15), using the actual parameters \(x,L_2,S_2\). Closed handoff on the negative vertical axis also gives \(D_C=(0,-d)\in F\). Hence the same original \(F\) contains
\[
B_1,B_2,D_C,E_1,E_2, \tag{17}
\]
and \(E_1,D_C,E_2\) also belong to the original \(C\). Their joint normal-width bounds may be used. No assertion that \(F\) contains the entire lower boundary of \(C\), or that these three common points are collinear, has been proved.

<a id="R47"></a>
## R47. A long bottom chord and exact five-point constraints for the same \(F\)

**Scope.** Keep the original \(C,F\), with \(\mu>1\), and assume \(Q_U\in W\). The exact fitting tool below checks actual forced points; it is not a sufficient condition for full coverage, and direction elimination is not required by the later R63 right-bridge exclusion.

### 1. The sum of the two short legs is less than one

R45--R46 give \(0<z\le\tau<2/5\), \(L_2>1+\tau\), \(u>1-\tau\), \(S_1<g(a)\), \(S_2<g(x)-K_x\tau\), where \(g(t)=(1-t)/(1+t)\), \(K_x=2x/(1-x^2)\), \(0<a,x<1\). The same \(C\) contains both actual horizontal corner endpoints, so its chord \(h=l+r>2-a-x\). Its budgets \(h+u^2\le2\), \(h\le\sqrt2\) yield
\[
a+x>(1-\tau)^2,\qquad a+x>2-\sqrt2>7/12. \tag{1}
\]
For \(0<\tau\le1/4\), put \(m=(1-\tau)^2\). Since \(a>m-x>-1\), monotonicity of \(g\) gives \(\Sigma<g(m-x)+g(x)-K_x\tau\); the auxiliary \(m-x\) need not be positive. Exactly,
\[
1-g(m-x)-g(x)+K_x\tau
=\frac{P(x,\tau)}{(1-x)(1+x)(1+m-x)},
\]
\[
P=3x(m-x)(1-x)+2x\tau(1+m-x)-(2\tau-\tau^2)(1-x). \tag{2}
\]
The denominator is positive. The actual long leg gives
\[
\tau<T_c(x)=2x^2/(1-x^2),\qquad
\tau<T_s(x)=(1-x)^2/(2x). \tag{3}
\]
The source proves \(P>0\) on three complete charts, \(0\le v\le1\):

1. \(0<x\le1/3\), \(\tau=T_c(x)v\): certify \(P/x>0\), positive denominator \((1-x^2)^3\), 36 strictly positive rational Bernstein coefficients.
2. \(1/3\le x\le1/2\), \(\tau=v/4\): certify \(P>0\), denominator 32, 16 strictly positive coefficients.
3. \(1/2\le x<1\), \(\tau=T_s(x)v\): certify \(P/(1-x)^2>0\), denominator \(4x^2\), 20 strictly positive coefficients.

The canceled factors are positive on the actual open domain. No sampled signs or adaptive subdivisions are used. Thus \(\Sigma<1\) in this range.

For \(1/4\le\tau<2/5\), \(L_2>5/4\) and its cosine and sine projections imply \(1/3<x<1/2\). Then (1) gives \(a>7/12-x>0\), so
\[
\Sigma<g(7/12-x)+g(x)-K_x/4<1. \tag{4}
\]
The exact positive difference is
\[
\frac{72x^3-126x^2+71x-10}{2(1-x^2)(19-12x)}.
\]
Its denominator is positive and its numerator has Bernstein coefficients \(7/3,53/18,55/18,3\) on \([1/3,1/2]\). Therefore throughout the actual domain,
\[
\Sigma<1. \tag{5}
\]

### 2. A long actual bottom chord makes \(F\) nonaxial

The same \(F\) contains \(B_1=(-\mu+S_1,-\mu)\), \(B_2=(\mu-S_2,-\mu)\). Its actual bottom chord has length
\[
b_F\ge2\mu-\Sigma>2\mu-1>\mu>1. \tag{6}
\]
An axis-aligned unit square has horizontal chords at most one, so \(F\) is nonaxial. If \(\phi\) is its smaller axis angle, \(b_F\le\sec\phi\), whence \(\sec\phi-1>1-\Sigma\).

Any unit square containing these endpoints must lie wholly below \(y=0\): a point at height at least zero would form a triangle of area at least \(b_F\mu/2>\mu^2/2>1/2\). Since \(S_1,S_2<1<\mu\), the bottom segment contains BOTTOM midpoint. Thus a successful five-point fit below automatically retains these two roles of \(F\); it still does not imply target coverage.

### 3. Effective depth and actual overlap

R46 supplies \(E_1=(-w_1,-t_1)\), \(E_2=(w_2,-t_2)\), with all four parameters positive, and \(D_C=(0,-d)\), all in the same \(C\cap F\). Define
\[
d_{\rm eff}=\frac{w_2t_1+w_1t_2}{w_1+w_2}. \tag{7}
\]
The axis intersection of \(E_1E_2\) is \(M=(0,-d_{\rm eff})\), so
\[
0<d_{\rm eff}\le d<1,\qquad M\in C\cap F. \tag{8}
\]
Using \(M\) in the same bottom-chord/height budgets strengthens them to
\[
\Sigma>(1-d_{\rm eff})^2,\qquad
\Sigma>2-\frac1{1-d_{\rm eff}}. \tag{9}
\]
The latter right side need not be positive; strictness comes from \(\mu>1\). The triangle \(E_1D_CE_2\subset C\cap F\) gives
\[
|C\cap F|\ge\frac{(w_1+w_2)(d-d_{\rm eff})}{2}. \tag{10}
\]
The common negative-axis interval has length at least \(d-d_{\rm eff}\). If the three points are collinear, \(d_{\rm eff}=d\) and the lower bound is zero. The effective depth only strengthens \(F\)'s height budget; it cannot replace the actual reach \(d\) in old active-face lemmas.

### 4. Exact elimination of the direction and translation of one \(F\)

Take \(\mathcal P=\{B_1,B_2,D_C,E_1,E_2\}\). For every pair difference \((\Delta x,\Delta y)\), a unit square with normals \((c,s),(-s,c)\) contains all five points exactly when some \(c,s\ge0\), \(c^2+s^2=1\), satisfies
\[
|\Delta x c+\Delta y s|\le1,\qquad
|\Delta y c-\Delta x s|\le1. \tag{11}
\]
The full first quadrant is retained; \(c\ge s\) is not imposed. At a fixed direction the two minimum projections determine a suitable translation.

Dropping \(c^2+s^2=1\) leaves a convex polygon \(K\) containing the origin. The actual bottom chord of length \(b>1\) implies \(bc\le1\), \(bs\le1\), so \(K\) is compact. Define
\[
R^2=\max_{v\in\operatorname{Vert}(K)}\|v\|^2.
\]
Then
\[
\mathcal P\text{ fits in one unit square}\quad\Longleftrightarrow\quad R^2\ge1. \tag{12}
\]
Necessity follows because every polygon point is a convex combination of vertices and its norm is bounded by their maximum norm. For sufficiency, radially contract a vertex of norm at least one onto the unit circle; convexity and the origin preserve all width inequalities. Choose the two minimum projections as support origins.

Every nonzero axis vertex has norm below one because \(b>1\). Thus any feasible witness includes a vertex with \(c,s>0\), determined by independent active rows
\(\alpha c+\beta s=1\), \(\gamma c+\epsilon s=1\). Its exact coordinates are
\[
c=\frac{\epsilon-\beta}{\alpha\epsilon-\beta\gamma},\qquad
s=\frac{\alpha-\gamma}{\alpha\epsilon-\beta\gamma}. \tag{13}
\]
This gives a finite exact row-pair elimination of angle and translation, rational when the point coordinates are rational. More generally, the smallest enclosing-square side length squared is \(1/R^2\). The source does not establish that every actual central active-face combination violates this test; this remains a local inclusion criterion only.

<a id="R48"></a>
## R48. Continuous-cover reductions and actual upper triple intersections

**Scope.** The main route uses the actual \(T_R\) existence theorem in Section 4. The lower five-point sufficiency result and the I/II classification are supplementary tools; R63 need not select either I or II. All unit tiles, directions, translations, and exit points mentioned below are actual geometric data.

### 1. The common-point fan lemma

Let closed convex sets \(A_i\) cover the boundary of a convex polygon \(R\), and let one point \(E\in R\) belong to every <span class="math-punctuation">\(A_i\).</span> Then they cover \(R\). For \(X\ne E\), extend the ray from \(E\) through \(X\) to a boundary point \(Y\). A set containing \(Y\) also contains \(E\), hence the segment \(EY\) and \(X\). The case \(X=E\) is immediate, even if \(E\in\partial R\). Pairwise intersections alone do not suffice. Each lower quadrant below uses its own actual triple point.

### 2. Exact five-point criterion for the lower half when \(Q_U\in W\)

Fix \(\mu>1\), the actual \(V_1,V_2,C\), their sizes, directions, and translations. Assume the R47 conditions: \(V_1\subset\{x<0\}\), \(V_2\subset\{x>0\}\), each outer vertical long leg is at least \(\mu\), and \(C\) contains \(O,Q_L,Q_R\), misses BOTTOM, and has lower endpoint \(D_C=(0,-d)\). The actual bottom gap endpoints are \(B_1,B_2\). Along the inward boundary polylines \(\Gamma_i\), from horizontal inner endpoint to bottom inner endpoint, define \(E_i\) as the first exit from this fixed \(C\). In a true covering R46 proves \(E_i\in\partial C\cap F\cap\partial V_i\), strictly inside its lower quadrant. For a candidate not yet known to cover, the exit can still be defined, allowing an immediate exit at the horizontal endpoint; a long-chord fitting tile below then makes that candidate infeasible.

Under \(\Sigma<1\), so \(b=|B_1B_2|>\mu>1\),
\[
\begin{aligned}
&\text{a unit }F\text{ with empty horizontal chord completes the lower half}\\
&\quad\Longleftrightarrow\quad
\{B_1,B_2,D_C,E_1,E_2\}\text{ fits in one unit square}.
\end{aligned} \tag{1}
\]
Necessity is R46. For sufficiency, a square containing the five points lies wholly below the horizontal axis by R47's long-chord triangle argument and contains BOTTOM midpoint. In the lower-left quadrant \(R_L=[-\mu,0]^2\), the top boundary runs from \(V_1\) to \(Q_L\) then through \(C\) to \(O\); the right boundary runs in \(C\) to \(D_C\), then in \(F\) to BOTTOM midpoint; the bottom boundary runs in \(V_1\) to \(B_1\), then in \(F\) to the midpoint; and the left boundary is in \(V_1\). The point \(E_1\in V_1\cap C\cap F\cap R_L\) permits the fan lemma. The lower-right quadrant uses \(V_2,C,F,E_2\) identically. Therefore the exact R47 polygon criterion becomes
\[
R^2_{\mathcal P}\ge1\quad\Longleftrightarrow\quad
\text{a required unit }F\text{ completes the lower half}. \tag{2}
\]
The actual five points remain fixed. This says nothing by itself about upper-half coverage or whether all actual parameters have \(R^2<1\).

### 3. The original \(F\) contains the whole boundary tail after exit

Let \(M_1\) be the corner of \(\Gamma_1\). If \(M_1\in C\), convexity puts \(Q_LM_1\subset C\); first exit occurs on the second edge, whose tail to \(B_1\) lies in \(F\). If \(M_1\notin C\), first exit occurs on the first edge, and intersection of \(C\) with that line is an interval. The segment after \(E_1\) through \(M_1\) is outside \(C\). Since \(\Gamma_1\subset C\cup F\), the vertex belongs to \(F\); convexity puts both \(E_1M_1\) and \(M_1B_1\) in \(F\). This includes vertex exit and tangent degeneracy, and does not overlook possible reentry into \(C\) along the second edge. The right version requires \(\Gamma_2\subset C\cup F\), supplied by \(Q_U\in W\) or a separate exclusion of other contribution. Under (1), tail inclusion is already implied by the five actual points and is not an independent extra vertex constraint. Collinearity with \(D_C\) is not asserted.

### 4. An actual upper-right triple point without an old angle ordering

This section requires only direct \(Q_R\in C\), not \(Q_U\in W\). For \(V_2\), use \(X=\mu-x,Y=y+\mu\), \(p=c_x,s=s_x,L=L_2\). The relevant supports are \(sX+pY\le1\), \(pX-sY\ge-sL\). Its inward upper polyline \(\Lambda_2\) runs from \(Q_R\), through \(N_2\), to the RIGHT long-leg endpoint \(J_2\), with inward coordinates
\[
Q_R:\ ((1-p\mu)/s,\mu),\quad
N_2:\ (s(1-pL),p+s^2L),\quad J_2:\ (0,L). \tag{3}
\]
The vertex satisfies both first upper and second lower supports. Since \(pL,sL\le1\), \(L\ge\mu\),
\[
Y(N_2)-L=p(1-pL)\ge0,\quad Y(N_2)\le p+s\le\sqrt2<2\mu.
\]
Together with \(V_2\subset\{x>0\}\), this puts \(\Lambda_2\) in the upper-right target, allowing \(N_2=J_2\). At every point other than the last endpoint, a small upward move leaves \(V_2\), violating the first upper support or second lower support. The move remains in the target. The tiles \(V_1,F\) are excluded by their signs. The opposite tiles \(V_2,V_4\) are disjoint: a shared point would bound the distance between their opposite target corners by the sum of two unit-square diameters, \(2\sqrt2\), whereas that distance is \(2\sqrt2\mu>2\sqrt2\). Closedness therefore also excludes a sufficiently small neighborhood of the fixed point from \(V_4\). Thus
\[
\Lambda_2\subset C\cup W. \tag{4}
\]
RIGHT contact puts \(J_2\in W\), while \(Q_R\in C\). If \(Q_R\in W\) already, it is a triple point; otherwise take first entry into \(W\), approaching through \(C\). Closedness gives
\[
T_R\in C\cap W\cap V_2. \tag{5}
\]
When \(Q_U\in W\), the horizontal line is empty in \(W\), so \(0<y(T_R)<\mu\), \(0<x(T_R)\le\mu\). A point on RIGHT is allowed. It need not be the old intersection of two first upper supports. No unproved \(x,\tau\) ordering or old right-seam formula is used.

### 5. The upper interface for a right bridge

If \(Q_U\in C\), rotate the argument for \(V_4\), using \(X=x+\mu,Y=\mu-y\), \(p=c_z,s=s_z,L=L_4\). The inward right polyline \(\Lambda_4\) has coordinates
\[
Q_U:\ (\mu,(1-p\mu)/s),\quad
N_4:\ (p+s^2L,s(1-pL)),\quad J_4:\ (L,0). \tag{6}
\]
It lies in the upper-right target. A small rightward move leaves \(V_4\), while \(V_1,F\) are excluded by signs and \(V_2\) by opposite-corner disjointness. Hence \(\Lambda_4\subset C\cup W\). TOP contact puts \(J_4\in W\), and closedness gives
\[
T_T\in C\cap V_4\cap W. \tag{7}
\]
In a right-bridge mechanism \(Q_U\notin W\), so \(x(T_T)>0\). TOP boundary contact is allowed; equality with R44's \(Q_\mu\) is not assumed. Double-direct contact permits both (5) and (7), in the same \(C\cap W\).

### 6. Boundary-path certificates for the upper half

Use the following convex-set path lemma. Suppose a boundary arc of a convex polygon \(R\) is covered in order by \(A_1,\ldots,A_n\), the remaining arc lies in a convex set \(C\), the endpoints lie in \(C\cap A_1,C\cap A_n\), and every adjacent pair has an actual point \(P_i\in C\cap A_i\cap A_{i+1}\). Then these sets cover \(R\). To prove it, choose boundary handoff points \(q_i\in A_i\cap A_{i+1}\). In each convex \(A_i\), deform its boundary path to the segment joining \(P_{i-1},P_i\); the intervening trips from \(q_i\) to \(P_i\) cancel. The resulting closed path lies in \(C\), where it contracts to a point. If a target-interior point were uncovered, every deformation would avoid it, contradicting the nonzero winding number of the boundary. This needs no unproved coordinate ordering of the chosen intersections.

With direct \(Q_R\), the horizontal boundary is covered by \(V_1,C,V_2\), and the upper outer arc runs through \(V_1,V_4,W,V_2\). R40's \(P_\mu\in C\cap V_1\cap V_4\), a point of \(C\cap V_4\cap W\), and (5) form the certificate. The middle point comes from (7) if contact is direct, or from R44 if \(Q_U\in W\). Thus double-direct and upper-bridge coverage reduce to these actual triple intersections.

For a right bridge, the positive horizontal arc runs \(C\) to \(R_C\), \(W\) to \(Q_R\), then \(V_2\) to RIGHT midpoint. The tile \(W\) contains \(R_C,Q_R\); both \(W,V_2\) contain the outer RIGHT contact \(J_2\). Deform the \(V_2\) outer path from \(J_2\) to \(Q_R\) to their chord, which also lies in \(W\). The remaining boundary path uses only \(V_1,V_4,W\), with endpoints \(Q_L,R_C\in C\); R40's left seam and (7) give the required two triple points. These are sufficiency certificates under the stated actual geometric facts, not automatic algebraic identities in free parameters.

### 7. Exactly two intersection combinations in the lower-right quadrant of a right bridge

Because \(W\) contains the upper-right target corner, every point with \(x\le0,y\le0\) is farther than \(\sqrt2\) from that corner. Thus \(W\) misses the closed lower-left quadrant. It also misses BOTTOM, at vertical distance \(2\mu>\sqrt2\). Consequently the lower-left quadrant always uses only \(V_1,C,F\), and R46's \(E_1\) with the fan lemma applies to all three remaining mechanisms.

In the lower-right quadrant \(R_R=[0,\mu]\times[-\mu,0]\), the boundary is cyclically covered by \(C,W,V_2,F\), with transitions \(R_C,Q_R,B_2,D_C\). Intersect these four convex compact sets with \(R_R\). They cover \(R_R\) exactly when at least one of the following pairs holds:
\[
\begin{array}{ll}
\mathrm I:&C\cap F\cap W\cap R_R\ne\varnothing,
\quad F\cap W\cap V_2\cap R_R\ne\varnothing;\\
\mathrm {II}:&C\cap W\cap V_2\cap R_R\ne\varnothing,
\quad C\cap F\cap V_2\cap R_R\ne\varnothing.
\end{array} \tag{8}
\]
Boundary points and a fourfold intersection are allowed; I and II are not mutually exclusive, and neither is excluded here.

For completeness, label the four sets \(1,2,3,4\) cyclically. For necessity, thicken them slightly to open convex sets while preserving emptiness of each originally empty triple intersection; compactness and finiteness permit this. Triangulate sufficiently finely, labeling vertices by original covering sets, with boundary labels in cyclic order. Each face barycenter belongs to the thickened sets of all its labels; hence a three-label face implies a nonempty original triple intersection. Adding labeled triangle boundaries modulo two cancels interior edges and leaves \(12+23+34+41\). The possible three-label faces are \(123,124,134,234\). Comparing the coefficients of diagonals \(13,24\) and outer edges forces either the pair \(123,134\) or the pair \(124,234\). Repeated-label faces contribute zero. Boundary handoffs can be chosen as subdivision vertices with the required arc labels.

For sufficiency, triple points of \(123\) and \(134\) are joined by a segment in both \(1,3\). This common chord splits the boundary loop into two three-set loops; each contracts to its triple point within the convex sets. The whole loop is therefore contractible in the union, and the winding-number argument forces coverage. The other pair is identical. The triangulation is a topological proof device, not a numerical grid search.

<a id="technical-part-H"></a>
# Technical Part H. Bridge angles and the same bottom tile

Modules: [R49](#R49), [R50](#R50), [R51](#R51), [R52](#R52), [R53](#R53), [R54](#R54), [R55](#R55), [R56](#R56), [R57](#R57), [R58](#R58), [R59](#R59).

<a id="R49"></a>
## R49. A continuous small-angle exclusion for a right bridge in both rotations

**Scope.** The original \(C\) contains \(Q_U\) but not \(Q_R\). The original \(W\) bridges the positive horizontal axis; no bound requiring \(Q_U\in W\) is imported. All bottom budgets concern the same original \(F\).

### 1. The actual bridge gives the correct short-leg replacement

Direct upper contact gives \(u>1-z\). Closed coverage forces \(R_C=(r,0),Q_R=(\mu-U(x),0)\in W\). Since \(Q_R\notin C\), its abscissa exceeds \(r\), and the actual horizontal chord length \(H\) satisfies
\[
H\ge\mu-U(x)-r>1-x-r,\qquad H>0.
\]
The TOP chord is also nonempty: \(L_4+D\ge2\mu\), \(L_4\le\sqrt2<2\mu\). These parallel lines are at distance \(\mu>1\), and their nonempty chord sum obeys \(D+H\le1\). More explicitly the general bound is \((c+s-\mu)/(cs)<1\), with positive direction components; the distance premise excludes an axial tile. TOP contact and \(L_4\le b_z\) give
\[
0<H<\Delta_z:=b_z-1=\frac{2z^2}{1-z^2}. \tag{1}
\]
This pairs TOP with the horizontal chord, with both intersections verified nonempty. Consequently, whenever \(r+\Delta_z<1\),
\[
x>1-r-\Delta_z,\qquad S_2<g(x)<q(r+\Delta_z). \tag{2}
\]
This replaces, rather than assumes, the double-direct bound \(S_2<q(r)\).

### 2. The same central tile and LEFT corner bounds

Let \(\eta=\tan(\theta/2)\), \(K=\tan\theta\), \(\delta=\sec\theta-1=\eta K\), where \(\theta\) is the smaller axis angle. For either rotation assume
\[
0\le\eta\le1/64,\quad K\le128/4095<1/31,\quad\delta\le2/4095. \tag{3}
\]
Actual chord projections and \(l>1-a,u>1-z\) give
\[
r<a+\delta,\qquad d<z+\delta, \tag{4}
\]
and the original \(F\) requires
\[
\Sigma>(1-z-\delta)^2,\qquad\Sigma>7/12. \tag{5}
\]
The real LEFT contact gives \(S_1<F(a,z)=b_a-K_a(2-g(z))\), \(z<4/15\), \(a+2z<1\), and
\[
a\le1/3:\ z<\frac{a^2}{1-2a^2};\qquad
a\ge1/2:\ z<\frac{(1-a)^2}{6a-1-a^2}. \tag{6}
\]
R43's LEFT-only surplus \(E=(1-z)^2-F-q(a)\) has bounds
\[
E>13a/20\ (a\le1/3),\quad E\ge1313/8550\ (1/3\le a\le1/2),
\quad E\ge2(1-a)/3\ (a\ge1/2). \tag{7}
\]
Only these independent LEFT facts and their frozen certificates are reused. On domains with \(a+\Delta_z+\delta<1\), it suffices to show
\[
\mathcal E=(1-z-\delta)^2-F(a,z)-q(a+\Delta_z+\delta)>0. \tag{8}
\]

### 3. Small \(a\)

For \(0<a\le1/3\), (6) gives \(z<1/7\), \(z<9a^2/7\), and
\[
\Delta_z<7z/24<3a^2/8\le a/8. \tag{9}
\]
Now \(a+\Delta_z+\delta<1/2\); hence \(q'\le1\), and
\[
\mathcal E>E-\Delta_z-3\delta>21a/40-3\delta. \tag{10}
\]
At \(\eta=0\), this is positive. For positive rotation, the first normal on \(L_C,U_C\) gives \(l+Ku\le1+\delta\), so
\[
a>K(1-z-\eta)>4K/5,\qquad3\delta<15a/256<21a/40.
\]
For negative rotation the second normal gives \(Kl+u\le1+\delta\), hence \(K(1-a-\eta)<z\), with \(1-a-\eta>1/2\). Thus
\[
K<2z<18a^2/7\le6a/7,\qquad3\delta<9a/224<21a/40.
\]
Both orientations make (10) positive.

### 4. Intermediate \(a\)

For \(1/3\le a\le1/2\), \(\Delta_z<32/209\), and the exact increment bound is
\[
q(a+\Delta_z)-q(a)=\frac{2\Delta_z}{(2-a-\Delta_z)(2-a)}\le256/1689. \tag{11}
\]
Let \(M=1313/8550-256/1689>0\). Here \(a+\Delta_z+\delta<1\); the remaining \(q\) increment and square loss are each at most \(2\delta\). Hence
\[
\mathcal E\ge M-4\delta\ge M-8/4095>0. \tag{12}
\]
Both constant differences are exact positive rational comparisons.

### 5. Large \(a\), ordinary range

Put \(\epsilon=1-a\in(0,1/2]\). From (6), whose denominator is at least \(7/4\),
\[
z<4\epsilon^2/7,\quad\Delta_z<120z/209<480\epsilon^2/1463. \tag{13}
\]
If \(\epsilon\ge12\delta\), then \(\Delta_z+\delta\le(240/1463+1/12)\epsilon<\epsilon\), so every \(q\) argument is below one. Using \(q'\le2\),
\[
\mathcal E\ge\gamma\epsilon-4\delta,\qquad\gamma=1486/4389.
\]
For \(\delta>0\), \(12\gamma-4=92/1463>0\) proves strict positivity; for \(\delta=0\), \(\gamma\epsilon>0\).

### 6. Large \(a\), extreme range

If \(0<\epsilon<12\delta\), then \(\eta,K,\delta>0\). Equation (13) gives
\[
z<576\delta^2/7,\quad z/K<576\eta^2K/7\le2/3185<1/100. \tag{14}
\]
Thus \(z<K/100<1/3100\), \(\Delta_z/z<1/10\), and
\[
\Delta_z<K/1000. \tag{15}
\]
The actual short leg obeys
\[
S_1<\frac{6\delta}{1-6\delta}
\le\frac{6/64}{1-12/4095}K<K/10. \tag{16}
\]
For positive rotation, the second normal on \(R_C,U_C\) gives \(Kr+u\le1+\delta\), so \(r<\eta+z/K<1/64+1/100\). Hence \(r+\Delta_z<1/4\), making (2) valid, and \(\Sigma<1/10+1/7<7/12\), contradicting (5).

For negative rotation, the first normal gives \(r<1-K(1-\eta-z)\), with \(1-\eta-z>49/50\). Thus \(r+\Delta_z<1-979K/1000<1-9K/10<1\). Since \(K<1/31<8/9\), \(q(1-9K/10)\le1-K\). Equations (2), (16) yield
\[
\Sigma<1-9K/10, \tag{17}
\]
whereas (5), \(z<K/100\), \(\delta\le K/64\) give
\[
\Sigma>(1-z-\delta)^2>1-2(z+\delta)>1-K/10. \tag{18}
\]
This is impossible for \(K>0\). All \(a\) and both rotations are therefore excluded throughout the closed half-angle interval in (3).

<a id="R50"></a>
## R50. Enlarging the two-rotation right-bridge exclusion to \(\eta\le1/16\)

**Scope.** Only direct \(Q_U\), nondirect \(Q_R\) is considered, keeping the original \(C,F\). R49's two actual nonempty parallel chords give
\[
0<H<\Delta_z=2z^2/(1-z^2),\qquad
S_2<q(r+\Delta_z)\quad(r+\Delta_z<1). \tag{1}
\]
The direct-only bound \(S_2<q(r)\) is not an input.

### 1. Inherited geometry and enlarged angle interval

For either rotation,
\[
0\le\eta\le1/16,\quad K\le32/255<1/7,\quad\delta=\eta K\le2/255. \tag{2}
\]
The same actual chord and bottom budgets give
\[
r<a+\delta,\quad d<z+\delta,\quad
\Sigma>(1-z-\delta)^2,\quad\Sigma>7/12. \tag{3}
\]
Use \(S_1<F=b_a-K_a(2-g(z))\) and \(E=(1-z)^2-F-q(a)\), with the three R43 lower bounds \(13a/20,1313/8550,2(1-a)/3\) on the small, middle, and large \(a\) ranges. The LEFT long-leg caps are those of R49. Only the LEFT part independent of direct \(Q_R\) is inherited; the normal comparisons are checked anew.

### 2. Small \(a\)

For \(0<a\le1/3\), \(z<1/7\), \(\Delta_z<3a^2/8\le a/8\), and
\[
a+\Delta_z+\delta\le1/3+1/24+2/255<1/2.
\]
Thus
\[
\mathcal E=(1-z-\delta)^2-F-q(a+\Delta_z+\delta)>21a/40-3\delta. \tag{4}
\]
At \(\eta=0\) this is positive. For positive rotation, \(a>K(1-z-\eta)>3K/4\), so \(3\delta\le3K/16<a/4<21a/40\). For negative rotation, \(K(1-a-\eta)<z\), \(1-a-\eta>1/2\), giving \(K<2z<18a^2/7\le6a/7\), and \(3\delta<9a/56<21a/40\). Both orientations are excluded.

### 3. A joint two-variable surplus for intermediate \(a\)

On the entire rectangle \(1/3\le a\le1/2\), \(0\le z\le4/15\),
\[
(1-z)^2-F(a,z)-q(a+\Delta_z)>8/255. \tag{5}
\]
This retains the same \(z\) in both terms. After subtracting \(8/255\), the exact positive denominator is
\[
D=255(1-a^2)(1+z)[(2-a)(1-z^2)-2z^2]. \tag{6}
\]
The last factor is at least \((3/2)(1-(4/15)^2)-2(4/15)^2=563/450>0\). Substitute \(a=1/3+u/6,z=4v/15\). The numerator has bidegree \((3,5)\), with all 24 rational Bernstein coefficients strictly positive, minimum \(443476/1366875\). The source reports independent termwise reconstruction of the full polynomial identity on \([0,1]^2\). Therefore (5) is a full-rectangle proof. As
\(a+\Delta_z+\delta\le1/2+32/209+2/255<1\), the extra \(q\) and square losses are at most \(4\delta\). Thus
\[
\mathcal E>8/255-4\delta\ge0, \tag{7}
\]
including \(\eta=1/16\).

### 4. Large \(a\), ordinary range

For \(a\ge1/2\), \(\epsilon=1-a\), the actual sine cap still gives \(z<4\epsilon^2/7\), \(\Delta_z<480\epsilon^2/1463\). If \(\epsilon\ge12\delta\), then \(\Delta_z+\delta\le(240/1463+1/12)\epsilon<\epsilon\). Every \(q\) argument is legal, and the R49 calculation gives
\[
\mathcal E\ge\gamma\epsilon-4\delta,\quad
\gamma=1486/4389,\quad12\gamma-4=92/1463>0.
\]
It is strictly positive for \(\delta>0\), and also for \(\delta=0\) since \(\epsilon>0\). This calculation does not require the old smaller cap \(\delta\le2/4095\).

### 5. Large \(a\), extreme range, with both normals checked anew

If \(0<\epsilon<12\delta\), then \(K>0\), and (2) gives
\[
z/K<576\eta^2K/7\le24/595<1/20,\quad z<K/20<1/140. \tag{8}
\]
Since \(\Delta_z/z<1/50\),
\[
\Delta_z<K/1000. \tag{9}
\]
Also
\[
S_1<\frac{6\delta}{1-6\delta}
\le\frac{6/16}{1-12/255}K=85K/216<2K/5. \tag{10}
\]
Positive rotation gives \(r<\eta+z/K<1/16+1/20\), so \(r+\Delta_z<1/4\). Equation (1) yields \(\Sigma<2K/5+1/7<2/35+1/7=1/5<7/12\), contrary to (3).

Negative rotation gives \(r<1-K(1-\eta-z)\), where
\(1-\eta-z>1-1/16-1/140>93/100\). Thus \(r+\Delta_z<1-929K/1000<1-9K/10<1\). Since \(K<1/7<8/9\), \(q(1-9K/10)\le1-K\), and
\[
\Sigma<1-3K/5. \tag{11}
\]
But (3), \(z<K/20\), \(\delta\le K/16\) imply
\[
\Sigma>(1-z-\delta)^2>1-2(z+\delta)>1-K/4, \tag{12}
\]
because \(2(1/20+1/16)=9/40<1/4\). This contradiction completes both rotations, with all angle endpoints retained. The corresponding full angle is approximately \(7.15^\circ\).

<a id="R51"></a>
## R51. Enlarging the two-rotation right-bridge exclusion to \(\eta\le1/8\)

**Scope and inputs.** Keep the R49--R50 actual geometry, original \(C,F\), direct \(Q_U\), and nondirect \(Q_R\). Both actual parallel chords of \(W\) are nonempty, so
\[
H<\Delta_z=2z^2/(1-z^2),\quad S_2<q(r+\Delta_z)\quad(r+\Delta_z<1). \tag{1}
\]
The actual roots satisfy \(u>1-z,r<a+\delta,d<z+\delta\), and
\[
\Sigma>(1-z-\delta)^2,\qquad\Sigma>7/12. \tag{2}
\]

### 1. Enlarged interval and required surplus

For either rotation take
\[
0\le\eta\le1/8,\quad K\le16/63<1/3,\quad\delta=\eta K\le2/63. \tag{3}
\]
Let \(\mathcal F=b_a-K_a(2-g(z))\), so \(S_1<\mathcal F\), and
\[
I=\frac{3a(1-a)}{(1+a)(2-a)},\quad E=(1-z)^2-\mathcal F-q(a),\quad
E_*=E-[q(a+\Delta_z)-q(a)].
\]
R43's independent LEFT argument gives
\[
E>13a/20\ (a\le1/3),\qquad E\ge I\ge2(1-a)/3\ (a\ge1/2). \tag{4}
\]
The needed final surplus is
\[
\mathcal E=(1-z-\delta)^2-\mathcal F-q(a+\Delta_z+\delta). \tag{5}
\]
Its \(q\) argument is checked below in every application; the extreme range instead uses actual \(R_C,U_C\) bounds.

### 2. Small \(a\), both rotations

For \(0<a\le1/3\), \(z<1/7\), \(\Delta_z<a/8\), and \(a+\Delta_z+\delta<1/3+1/24+2/63<1/2\). Hence
\[
\mathcal E>21a/40-3\delta. \tag{6}
\]
At \(\eta=0\) this is positive. Positive rotation gives \(a>K(1-z-\eta)>41K/56\), and \(3\delta\le3K/8<21a/41<21a/40\). Negative rotation gives \(K(1-a-\eta)<z\), with \(1-a-\eta>1/2\); thus \(K<2z<18a^2/7\le6a/7\), \(3\delta<9a/28<21a/40\). These are fresh checks under (3).

### 3. Intermediate \(a\): two complete charts from actual long-leg caps

For \(1/3\le a\le1/2\), the actual inequalities \(L_1>2-g(z)\), \(L_1\le b_a\) give
\[
b_a-(2-g(z))=\frac{2[a^2(1+2z)-z]}{(1-a^2)(1+z)}>0,
\quad z<Y_c(a)=\frac{a^2}{1-2a^2}. \tag{7}
\]
The denominator is positive for the use up to \(a=5/12\). Likewise \(L_1\le1/s_a\) gives
\[
\frac{1+a^2}{2a}-(2-g(z))
=\frac{(1-a)^2-z(6a-1-a^2)}{2a(1+z)}>0,
\quad z<Y_s(a)=\frac{(1-a)^2}{6a-1-a^2}. \tag{8}
\]
In the present positive-denominator domain,
\[
E_*(a,z)>8/63. \tag{9}
\]
Use two full charts \(0\le v\le1\): \(1/3\le a\le5/12\), \(z=Y_c(a)v\), and \(5/12\le a\le1/2\), \(z=Y_s(a)v\). The first cap is increasing and \(Y_c(5/12)=25/94<4/15\); the second has derivative \(4(a^2-1)/(6a-1-a^2)^2<0\) and is at most \(49/191<4/15\).

The positive denominator of \(E_*-8/63\) before substitution is
\(63(1-a^2)(1+z)[(2-a)(1-z^2)-2z^2]\). Writing each cap as \(N/d\), a positive denominator after substitution is
\[
63(1-a^2)d^2(d+Nv)[(2-a)d^2-(4-a)N^2v^2]. \tag{10}
\]
For the cosine chart this is exactly the denominator; for the sine chart a positive factor \(1-a\) cancels. After affine normalization of \(a\), the numerator degrees are \((13,5),(12,5)\), with 84 and 78 strictly positive rational Bernstein coefficients. The source reports independent reconstruction of both polynomial identities and all 162 coefficients. Since \(a+\Delta_z+\delta\le1/2+32/209+2/63<1\), the remaining losses are at most \(4\delta\), and
\[
\mathcal E>E_*-4\delta>8/63-4\delta\ge0. \tag{11}
\]
This includes \(\eta=1/8\).

### 4. A stronger joint lower bound for large \(a\)

Let \(a\ge1/2\), \(\epsilon=1-a\). The actual sine cap gives
\[
z<4\epsilon^2/7\le1/7,\quad\Delta_z<480\epsilon^2/1463<\epsilon. \tag{12}
\]
Thus \(a+\Delta_z<1\), and exactly
\[
E_*-I=z^2-2z+\frac{2K_az}{1+z}-[q(a+\Delta_z)-q(a)]. \tag{13}
\]
For \(1/2\le a\le2/3\), \(a+\Delta_z\le17/24\), so \(q'\le1152/961<5/4\). Dividing (13) by actual \(z>0\) yields a lower bound
\[
z-2+\frac{2K_a}{1+z}-\frac{5z/2}{1-z^2}.
\]
Here \(2K_a/(1+z)\ge7/3\), and \(z-(5z/2)/(1-z^2)\ge-149z/96\ge-149/672\), giving margin \(25/224>0\). For \(a\ge2/3\), \(K_a\ge12/5\), \(q'\le2\), and the corresponding lower bound is
\[
z-2+\frac{2K_a}{1+z}-\frac{4z}{1-z^2}
\ge-2+21/5-7/12=97/60>0.
\]
Therefore
\[
E_*>I\ge2\epsilon/3 \tag{14}
\]
for actual \(z>0\), with equality extension at auxiliary \(z=0\). If \(\epsilon\ge6\delta\), then \(\Delta_z+\delta\le(240/1463+1/6)\epsilon<\epsilon\). Thus \(\mathcal E>E_*-4\delta>2\epsilon/3-4\delta\ge0\), including \(\delta=0\).

### 5. The extreme range \(\epsilon<6\delta\)

Now \(K>0\). The caps yield \(z<144\delta^2/7\), \(z/K<4/49<1/10\), \(z<1/40\). Since \(\Delta_z/z<1/19\),
\[
\Delta_z<K/100. \tag{15}
\]
Also
\[
S_1<\frac{3\delta}{1-3\delta}\le63K/152<K/2. \tag{16}
\]
Positive rotation gives \(r<\eta+z/K<1/8+4/49\); adding \(\Delta_z<K/100<1/300\) gives \(r+\Delta_z<1/4\). Hence \(\Sigma<K/2+1/7<1/6+1/7<7/12\), contrary to (2).

Negative rotation gives \(r<1-K(1-\eta-z)\), with \(1-\eta-z>17/20\). Then \(r+\Delta_z<1-21K/25<1-4K/5<1\), and \(K<1/3\) implies
\[
q(r+\Delta_z)<q(1-4K/5)\le1-24K/19<1-6K/5.
\]
Equation (16) gives \(\Sigma<1-7K/10\), whereas (2), \(z<K/10\), \(\delta\le K/8\) imply \(\Sigma>(1-z-\delta)^2>1-9K/20\). This is impossible. The actual \(R_C\) always exists, even though \(Q_R\notin C\). Both rotations are excluded on the complete closed half-angle interval, corresponding to approximately \(14.25^\circ\).

<a id="R52"></a>
## R52. Small-angle upper-bridge exclusion and a uniform angle lower bound

**Scope.** Sections 1--5 assume the original \(W\) contains \(Q_U\), in the legal R45 representative, with the original \(C,F\) fixed. The result applies to an upper bridge and to a double-direct subclass with the same membership, but no such bound is transferred to a general right bridge.

### 1. Actual common inputs

Let \(a,x\in(0,1)\) be the half-angles of \(V_1,V_2\), \(\tau\in(0,2/5)\) that of \(W\), and \(\eta\) the smaller-axis half-angle of \(C\), with \(K=\tan\theta\), \(\delta=\sec\theta-1=\eta K\). R46 gives
\[
u>1-\tau,\quad l>1-a,\quad r>1-x,\quad
S_1<g(a),\quad S_2<g(x)-K_x\tau, \tag{1}
\]
\[
a+x>1-\delta,\quad d<\tau+\delta,\quad\delta>\tau/32, \tag{2}
\]
\[
\tau<T_c(x)=\frac{2x^2}{1-x^2},\qquad
\tau<T_s(x)=\frac{(1-x)^2}{2x}. \tag{3}
\]
The same original \(F\) requires
\[
\Sigma>(1-d)^2>(1-\tau-\delta)^2. \tag{4}
\]
Suppose \(0<\eta\le1/24\); \(\eta=0\) is already excluded by (2). Then
\[
K>0,\quad\delta\le2/575,\quad\tau<32\delta. \tag{5}
\]
Here \(\tau+\delta<1\), so the square comparison is legitimate. Actual \(L_C,U_C,R_C\) normal projections give
\[
\begin{array}{ll}
\text{positive rotation}:&a>K(1-\tau-\eta),\quad\tau>K(1-x-\eta),\\
\text{negative rotation}:&x>K(1-\tau-\eta),\quad\tau>K(1-a-\eta).
\end{array} \tag{6}
\]
Only \(u>1-\tau\) is used, not direct \(Q_U\) membership in \(C\).

### 2. The bottom budget forces one small and one large corner parameter

Set \(m=\min(a,x)\), \(M=\max(a,x)\). If \(m\ge1/2\), then \(\Sigma<g(a)+g(x)\le2/3\), but (4)--(5) imply \(\Sigma>(1-33\delta)^2\ge(1-66/575)^2>2/3\). Thus \(0<m<1/2\). Since \(M>1-m-\delta\), \(m+\delta<1\),
\[
\Sigma<g(m)+q(m+\delta).
\]
Define
\[
I(m)=1-g(m)-q(m)=\frac{3m(1-m)}{2+m(1-m)}.
\]
The bound \(q'\le2\) on \([m,m+\delta]\), together with (4), yields
\[
I(m)<2\tau+4\delta<68\delta. \tag{7}
\]
The function increases on \([0,1/2]\); \(I(2/9)=21/88\), while \(68\delta\le136/575<21/88\), with exact margin \(107/50600\). Therefore
\[
m<2/9,\quad m+\delta<1/4,\quad M>3/4. \tag{8}
\]
As \(I(m)/m\) decreases and its endpoint value \(189/176>16/15\),
\[
m<15\tau/8+15\delta/4. \tag{9}
\]

### 3. Excluding the two wrong placements of the small parameter

For positive rotation with \(x=m\), (6) gives \(\tau>53K/72\), \(\delta<3\tau/53\); (9) then gives \(x<885\tau/424\). The actual cosine cap in (3) would imply
\[
1<\frac{2x^2}{\tau(1-x^2)}
<\frac{885}{212}\frac{x}{1-x^2}<7965/8162<1.
\]
Thus positive rotation requires \(a=m,x=M>3/4\).

For negative rotation with \(a=m\), the same bound \(\delta<3\tau/53\) and (9) give \(a<885\tau/424\). Then \(\epsilon_x=1-x<a+\delta<909\tau/424\), with \(\epsilon_x<1/4,x>3/4\). The actual sine cap would imply
\[
1<\frac{\epsilon_x^2}{2x\tau}
<\frac{909}{424}\frac{\epsilon_x}{2x}<303/848<1.
\]
Thus negative rotation requires \(x=m,a=M>3/4\). These use \(V_2\)'s two actual long-leg projections.

### 4. The remaining positive-rotation placement

Let \(a=m,x>3/4\). We first show
\[
\tau<3\delta. \tag{10}
\]
Otherwise \(\delta\le\tau/3\), while the sine cap gives \(\tau<T_s(x)<1-x\), ensuring \(x+\delta<1\). Then \(S_1<q(x+\delta)\), and comparison with (4) uses
\[
E(x,\tau)=(1-\tau)^2-q(x)-g(x)+K_x\tau
=I(x)+(K_x-2)\tau+\tau^2.
\]
The \(q\) and square losses total at most \(4\delta\). Since \(K_x>24/7\),
\[
E>10\tau/7,\qquad E-4\delta>(10/7-4/3)\tau=2\tau/21>0,
\]
a contradiction, proving (10). Now (9) gives \(a<75\delta/8\le25K/64\), but (6) gives \(a>K(1-\tau-\eta)>67K/120\). Their coefficient difference is \(161/960>0\), impossible.

### 5. The remaining negative-rotation placement

Now \(x=m<2/9\). On \(0<x\le2/9\), \(0\le\tau\le T_c(x)\),
\[
E(x,\tau)>2x/5. \tag{11}
\]
Indeed \(E_\tau=K_x-2+2\tau\le36/77-2+16/77=-102/77<0\), so it suffices to use \(\tau=T_c(x)\). Exactly,
\[
\frac{E(x,T_c(x))}{x}-\frac25
=\frac{2x^4-61x^3+147x^2-79x+11}{5(2-x)(1-x)^2(1+x)}.
\]
The denominator is positive. Under \(x=2v/9\), the quartic Bernstein coefficients are
\(11,119/18,278/81,1889/1458,257/6561\), all strictly positive, with the source reporting independent full polynomial reconstruction. Division by \(x\) is used only on the actual positive domain.

Because \(x+\delta<1/4\), the same actual \(C,F\) comparison contradicts (4) whenever \(E-4\delta>0\). Equation (6) gives \(x>67K/120\), hence
\[
E-4\delta>\frac25\frac{67}{120}K-\frac16K=17K/300>0.
\]
Negative rotation is also excluded.

### 6. The uniform consequence for all remaining mechanisms

Thus \(Q_U\in W\) excludes both rotations for \(\eta\le1/24\). Double-direct contact already excludes \(\eta\le1/8\) by R43, and a right bridge excludes that range by R51. Consequently every remaining mechanism satisfies
\[
\eta_C>1/24,\qquad\delta_C>2/575,\qquad
\theta_C>4.771888^\circ\quad\text{approximately}.
\]
This gives no uniform positive lower bound on \(\tau\). The source records eight new identities, one complete quartic reconstruction, five positive rational coefficients, fourteen exact constants, and 36 geometric-premise checks; old R46/R51 inputs are not counted again. The remaining work continues in R53--R64.

<a id="R53"></a>
## R53. A universal actual relation between the left seam and the bottom short leg

**Scope.** All current remaining configurations keep the original \(C,F\). R42's normalized point \(P_1=(-1+X_1,e_1)\) belongs to that same \(C\). We prove
\[
Q=1-X_1-e_1=S_4+(K_z-1)\frac{b_a+S_4-2}{K_a-K_z},\quad
0<Q<1,\quad S_1<q(Q),\quad q(t)=t/(2-t). \tag{1}
\]

### 1. Inputs from actual LEFT geometry

The actual half-angles satisfy \(0<z<a<1\), \(a+2z<1\). Set \(b=(1+a^2)/(1-a^2)\), \(k=K_a=2a/(1-a^2)\), \(h=K_z=2z/(1-z^2)\), \(G=g(z)\). This local \(h\) is a corner slope. Let \(L=L_1\), \(T=S_1\), \(S=S_4\). The actual legs obey
\[
T=b-kL\ge0,\quad L\le b,\quad L\le1/s_a,
\quad L+S\ge2\mu>2,\quad0<S<G. \tag{2}
\]
Also \(L\ge\mu>1\) gives \(T<g(a)\). Since \(X_1,e_1>0\), \(Q<1\); positivity is proved below. Define
\[
\mathcal Q(S)=S+(h-1)\frac{b+S-2}{k-h},\quad
\mathcal Q'(S)=\frac{k-1}{k-h}. \tag{3}
\]
All denominators are nonzero because \(k>h\).

### 2. The case \(k\le1\)

The nonpositive slope and \(S<G\) give \(Q\ge\mathcal Q(G)\). Exactly,
\[
\mathcal Q(G)-(1-a)=\frac{z(1-a-z)(1-2a-a^2)}{(a-z)(1+az)}\ge0. \tag{4}
\]
Here \(a+z<1\), and \(k\le1\) is equivalent to \(a^2+2a-1\le0\). Thus \(Q\ge1-a>0\), and \(T<g(a)=q(1-a)\le q(Q)\). This includes \(k=1\), without requiring strictness in (4).

### 3. The case \(k\ge1\): a quadratic in the actual long-leg surplus

Now \(a\ge\sqrt2-1>2/5\). Since \(L>2-S\), monotonicity gives \(Q\ge Q_{\min}(L):=\mathcal Q(2-L)\). Put
\[
L_0=2-G,\quad w=L-L_0>0,\quad T=b-k(L_0+w),
\]
\[
R(w)=Q_{\min}(L_0+w)(1+T)-2T. \tag{5}
\]
This is quadratic, with coefficient
\[
R_2=\frac{k(k-1)}{k-h}\ge0. \tag{6}
\]
The actual sine cap gives
\[
z<Y_s(a)=\frac{(1-a)^2}{6a-1-a^2}. \tag{7}
\]
Its denominator is at least \(31/25>0\) for \(a\ge2/5\). To prove \(R(0),R'(0)>0\), certify the two functions
\[
R(0)/z,\qquad R'(0). \tag{8}
\]
Substitute \(z=Y_s(a)v\), \(a=2/5+3u/5\), \(0\le u,v\le1\); \(a=1\) is used only for polynomial extension. With \(N=(1-a)^2\), \(d=6a-1-a^2\), exact positive denominators are
\[
D_0=(1-a^2)(ad-Nv)(d+Nv)(d+aNv),\quad
D_1=(1-a^2)(ad-Nv)(d+aNv). \tag{9}
\]
Indeed \(d>0\), and \(ad-N=-a^3+5a^2+a-1\) equals \(17/125\) at \(2/5\) and has positive derivative \(-3a^2+10a+1\) on \([2/5,1]\). Thus \(ad-Nv>0\), also verifying \(z<a\) throughout the actual chart. The two numerator degrees are \((10,2),(7,2)\), with 33 and 24 strictly positive rational Bernstein coefficients and independent polynomial reconstruction in the source. Therefore \(R(0),R'(0)>0\); (6) and \(w>0\) imply \(R(w)>0\).

As \(T\ge0\), \(Q\ge Q_{\min}>2T/(1+T)\ge0\). Since \(Q<1\), \(q\) is increasing there, and \(q(2T/(1+T))=T\), proving (1). Zero short leg \(T=0\) is retained; no division by it occurs.

### 4. A near-diagonal tile with \(Q_U\in W\): the correct \(+\tau\) relation

Suppose additionally \(Q_U\in W\) and \(\sin\theta_C\ge12/17\). Then \(u>1-\tau>3/5>e_1\), since \(e_1<5/12\). Let \(\rho_1=1-X_1>0\), \(c\ge s\ge12/17\). The actual normals in the two rotations give respectively
\[
c\rho_1+s(u-e_1)\le1\quad\hbox{or}\quad
s\rho_1+c(u-e_1)\le1.
\]
Thus \(Q+u\le1/s\le17/12\), so \(Q<5/12+\tau<1\), and
\[
S_1<q(5/12+\tau). \tag{10}
\]
This uses \(u>1-\tau\), not the direct-only \(u>1-z\). The same actual \(R_C,U_C\) give \(r+u\le17/12\), whence \(r<5/12+\tau\). Since \(Q_R\in C\), \(r>1-x\), so
\[
x>A_\tau:=7/12-\tau>0. \tag{11}
\]

### 5. Retaining the stronger actual right long-leg loss

Before weakening its conclusion to \(L_2>1+\tau\), R46 gives
\[
L_2>2-b_\tau+K_\tau(2-b_z)=1+w_R,\quad
w_R=K_\tau(1-\Delta_z-\tau)>\tau>0. \tag{12}
\]
Therefore
\[
S_2<g(x)-K_xw_R<q(5/12+\tau)-K_{A_\tau}w_R. \tag{13}
\]
This uses monotonicity of \(g,K\) and (11), without comparing \(x\) to \(\tau\). The fixed-long-leg projection maximum also gives
\[
S_2<\Phi(w_R),\quad\Phi(w)=(1+w)(1-\sqrt{w(2+w)}),
\quad0<w_R<\sqrt2-1. \tag{14}
\]
Likewise \(S_1<\Phi(2z/(1+z))\). These may be combined with the same bottom budget \(\Sigma>2-\sqrt2\) and the actual \(T_R\in C\cap V_2\cap W\). This module does not prove that these independently relaxed bounds alone contradict every \((\tau,z)\); the original \(C\) must actually accommodate \(T_R\).

<a id="R54"></a>
## R54. A complete near-diagonal exclusion when \(W\) contains the upper endpoint

**Scope.** Throughout \(Q_U\in W\), with the legal actual \(V_2,W\) representatives and unchanged original \(C,F\). Use \(\tau\) for the half-angle of \(W\), \(\lambda(v)=2v/(1-v^2)\), \(b(v)=(1+v^2)/(1-v^2)\), \(g(v)=(1-v)/(1+v)\), and \(q(v)=v/(2-v)\). The constant called a cardinality-like letter in the source is denoted \(\mathcal K=71/50\) here; it is not the midpoint count \(\kappa\).

### 1. Actual inputs

R45--R46 give
\[
0<z\le\tau<2/5,\quad z<4/15,\quad u>1-\tau,
\quad L_2>1+\tau,\quad\tau<\frac{2x^2}{1-x^2}. \tag{1}
\]
The tile \(C\) directly contains \(Q_R\), \(F\) has empty horizontal chord, and the normalized \(W\) lies entirely above the horizontal axis. The actual short leg is \(S_2=b(x)-\lambda(x)L_2\ge0\). R53 supplies \(P_1=(-\rho,e)\in C\), with
\[
0<e<5/12,\quad\rho>0,\quad Q=\rho-e\in(0,1),
\quad S_1<q(Q),\quad\frac{2S_1}{1+S_1}<Q. \tag{2}
\]
R48 supplies the same actual triple point \(T_R=(\xi,\upsilon)\in C\cap V_2\cap W\), \(0<\xi\le\mu\), \(0<\upsilon<\mu\), without specifying its edge or excluding RIGHT contact. Put
\[
\mathcal K=71/50,\quad H_*=7/12,\quad\beta=2-b(4/15)=177/209. \tag{3}
\]
The same \(F\) requires \(S_1+S_2>2-\sqrt2>H_*\).

### 2. A fresh actual angle ordering

Equation (1) gives \(x^2>\tau/(2+\tau)>\tau^2\), since \(1-2\tau-\tau^2>1/25>0\). Thus
\[
x>\tau,\qquad\lambda(x)>\lambda(\tau). \tag{4}
\]
This is derived from the present long leg, without an old angle cascade.

### 3. A position bound for every actual upper-right triple point

In \(V_2\)'s inward coordinates \(X=\mu-\xi\ge0,Y=\upsilon+\mu\), the first support of \(V_2\) and second upper support of \(W\) give
\[
Y\le b(x)-\lambda(x)X,\quad
Y\ge B_{\rm act}-\lambda(\tau)X,
\quad B_{\rm act}=2\mu-b(\tau)+\lambda(\tau)D. \tag{5}
\]
TOP contact gives
\[
B_{\rm act}>B_z:=1+\lambda(\tau)(1-\Delta_z-\tau),\quad\Delta_z=b(z)-1. \tag{6}
\]
RIGHT contact gives \(L_2\ge B_{\rm act}\). For any chosen \(1<B_0\le B_z\),
\[
S_2<S:=b(x)-\lambda(x)B_0,\quad0<S<g(x)<1. \tag{7}
\]
The two supports and (4) imply
\[
X\le\frac{b(x)-B_{\rm act}}{\lambda(x)-\lambda(\tau)},\qquad
\xi+\upsilon=Y-X\ge M(B_{\rm act})>M(B_0),
\]
\[
M(B)=B-\frac{(1+\lambda(\tau))(b(x)-B)}{\lambda(x)-\lambda(\tau)},\quad
M'(B)=\frac{\lambda(x)+1}{\lambda(x)-\lambda(\tau)}>0. \tag{8}
\]
These inequalities apply to any actual triple point, including \(X=0\), and do not claim an infinite-support intersection is on an actual edge. Two usable bounds are
\[
B_\tau=1+\lambda(\tau)(1-\Delta_\tau-\tau)\le B_z,
\quad B_c=1+\lambda(\tau)(\beta-\tau)<B_z. \tag{9}
\]
The latter is strictly increasing for \(0<\tau<2/5\), since
\[
B_c'=\frac{2[\beta(1+\tau^2)-2\tau]}{(1-\tau^2)^2}>0,\quad\beta>4/5. \tag{10}
\]

### 4. Directional width of the same \(C\)

Write \(c=\cos\theta_C\ge s=\sin\theta_C>0\). It suffices to assume
\[
\frac1s+\left(\frac cs-1\right)\frac5{12}\le\mathcal K,
\quad\text{equivalently }300+125c\le551s. \tag{11}
\]
For \(\eta=\tan(\theta_C/2)\), this is \(175\eta^2-1102\eta+425\le0\). The polynomial decreases on \([0,\sqrt2-1]\); its smaller root is \(\eta_*=(551-\sqrt{229226})/175\), so (11) holds exactly above the corresponding full-angle threshold.

The difference \(T_R-P_1=(\xi+\rho,\upsilon-e)\) has positive first component and second component greater than \(-e\). Positive rotation uses normal \((c,s)\), negative rotation uses \((s,c)\). Their directional differences are at least \(s(\Delta_x+\Delta_y)\) and \(s(\Delta_x+\Delta_y)-(c-s)e\), respectively. Thus
\[
Q+\xi+\upsilon\le1/s+(c/s-1)e\le\mathcal K,
\]
and (2), (8) imply
\[
M(B_0)+\frac{2S_1}{1+S_1}<\mathcal K. \tag{12}
\]
Since \(u>1-\tau>3/5>e\), the actual pairs \(P_1,U_C\), \(R_C,U_C\) also give \(Q+u\le1/s\le\mathcal K\), \(r+u\le1/s\le\mathcal K\). Direct \(Q_R\) contact then yields
\[
S_1<q(\mathcal K-1+\tau),\qquad x>2-\mathcal K-\tau=29/50-\tau. \tag{13}
\]
Every \(q\) argument is in \((0,1)\). If \(s\ge12/17\), then \(c/s\le289/288\), since \(289^2-145\cdot576=1\); hence the left side of (11) is at most \(17/12+5/3456<71/50\). Thus the earlier near-diagonal band is included. For positive rotation the seam-pair normal has no \(e\) loss, so \(1/s\le\mathcal K\), namely \(s\ge50/71\), suffices. The negative-rotation loss cannot be dropped.

### 5. Six complete scalar certificates

The source supplies six complete polynomial identities with 111 strictly positive rational Bernstein coefficients. They certify signs on the full stated domains, with positive denominators checked separately.

For \(0\le\tau\le1/6\),
\[
H_*-2q(\mathcal K-1+\tau)+\lambda(2-\mathcal K-\tau)(B_\tau-1)>0. \tag{14}
\]
Its denominator is \(12(1-\tau)^2(1+\tau)^2(79-50\tau)(50\tau+21)\); the numerator has degree six and seven positive coefficients. Here \(B_\tau>1\), and (7), (13) force \(S_1+S_2<H_*\), impossible.

For \(1/6\le\tau\le1/5\),
\[
B_\tau>5/4. \tag{15}
\]
The denominator is \(4(1-\tau)^2(1+\tau)^2\), the numerator degree four, with five positive coefficients. The actual sine projection gives \(x<1/2\), and (13) gives \(x>19/50\).

For \(1/5\le\tau\le3/10\),
\[
H_*-q(\mathcal K-1+\tau)-g(9/20)+\lambda(9/20)(B_c-1)>0. \tag{16}
\]
Its denominator is \(800052(1-\tau)(1+\tau)(79-50\tau)\), with a degree-three numerator and four positive coefficients. If \(x\ge9/20\), (7), (13) contradict the bottom budget. Thus \(x<9/20\). Also \(B_c(1/5)-b(1/3)=49/2508>0\), and monotonicity with \(L_2\le b(x)\) gives \(x>1/3\).

For a chosen \(B\), let \(S=b(x)-\lambda(x)B\) and
\[
\begin{split}
N(B;\tau,x)={}&[B(\lambda(x)+1)-b(x)(1+\lambda(\tau))
-\mathcal K(\lambda(x)-\lambda(\tau))](1+H_*-S)\\
&+2(H_*-S)(\lambda(x)-\lambda(\tau)).
\end{split} \tag{17}
\]
The remaining three full rectangles have \(N>0\):

1. \(B=B_\tau\), \(\tau\in[1/6,1/5]\), \(x\in[19/50,1/2]\): numerator bidegree \((8,4)\), 45 positive coefficients; denominator \(300(1-\tau)^4(1+\tau)^4(1-x)^2(1+x)^2\).
2. \(B=B_c\), \(\tau\in[1/5,3/10]\), \(x\in[1/3,9/20]\): bidegree \((4,4)\), 25 positive coefficients; denominator \(13104300(1-\tau)^2(1+\tau)^2(1-x)^2(1+x)^2\).
3. \(B=B_c\), \(\tau\in[3/10,2/5]\), \(x\in[3/8,11/25]\): the same degree, coefficient count, and denominator as the preceding case.

The first two actual domains were established above. For the last, monotonicity of \(B_c\) and
\[
B_c(3/10)-b(3/8)=288/8645>0,\quad
B_c(3/10)-1/s_{11/25}=2008/475475>0 \tag{18}
\]
combine with the actual cosine and sine projections to give \(3/8<x<11/25\). These are domains deduced from geometry and the same bottom budget, not arbitrary numerical subdivisions.

### 6. Returning to the actual covering

For actual \(\tau\ge1/6\), choose the appropriate \(B\). We have \(\lambda(x)-\lambda(\tau)>0\), \(B>1\), \(0\le S_2<S<1\). The bottom budget gives \(S_1>H_*-S>-1\). Since \(j(v)=2v/(1+v)\) increases on \((-1,\infty)\), (12) implies
\[
M(B)+j(H_*-S)<\mathcal K. \tag{19}
\]
But exactly
\[
N=(\lambda(x)-\lambda(\tau))(1+H_*-S)
[M(B)+j(H_*-S)-\mathcal K]. \tag{20}
\]
Both prefactors are positive, while the certificates give \(N>0\), contradicting (19). Negative \(H_*-S\) is allowed, and neither short leg is divided out. Equation (14) covers smaller \(\tau\), and the three rectangles cover all remaining \(\tau<2/5\). This excludes the stated angle band for both rotations, allowing actual RIGHT contact and either TOP-midpoint status of the free tile.

<a id="R55"></a>
## R55. Excluding the entire positive-rotation class with \(Q_U\in W\)

**Scope.** The original \(W\) contains \(Q_U\), and the original \(C\) has positive rotation. All replacements preserve the actual target points and keep \(C,F\) fixed. Sections 1--6 first prove
\[
\tau<1/6. \tag{1}
\]
Sections 7--10 finish the whole positive-rotation class. None of its successive \(\tau\) caps applies to the negative rotation or to a general right bridge. Use core \(\eta\) for the half-angle of \(C\), \(\tau\) for that of \(W\), and \(\lambda(v)=2v/(1-v^2)\).

### 1. Actual inputs only

We have \(0<z\le\tau<2/5\), \(z<4/15\), \(x>\tau\), and
\[
S_2=b(x)-\lambda(x)L_2\ge0,\quad L_2\le b(x),\quad s_xL_2\le1. \tag{2}
\]
R53 gives the actual point \(P_1=(-\rho,e)\in C\), with \(e>0\), \(Q=\rho-e\in(0,1)\), \(S_1<q(Q)\), \(j(S_1)<Q\), where \(q(v)=v/(2-v)\), \(j(v)=2v/(1+v)\). R48 supplies the same actual point \(T_R=(\xi,\upsilon)\in C\cap V_2\cap W\), \(0<\xi\le\mu\), \(0<\upsilon<\mu\). The same \(F\) gives
\[
S_1+S_2>2-\sqrt2>H_*:=7/12. \tag{3}
\]
No near-diagonal short-leg cap or \(x\) lower bound is imported. Set \(\beta=177/209\), \(\mathcal K=71/50\), \(\Delta_v=b(v)-1\), and
\[
B_\tau=1+\lambda(\tau)(1-\Delta_\tau-\tau),\quad
B_c=1+\lambda(\tau)(\beta-\tau). \tag{4}
\]
For the appropriate legal lower bound \(B\), R54 gives
\[
L_2>B,\quad S_2<S:=b(x)-\lambda(x)B,\quad0<S<1, \tag{5}
\]
and, writing \(X=\mu-\xi\),
\[
X\le\frac{b(x)-B_{\rm act}}{\lambda(x)-\lambda(\tau)}
<X_*:=\frac{b(x)-B}{\lambda(x)-\lambda(\tau)}.
\]
Thus, for this same \(B\) and actual point,
\[
\xi>1-X_*,\qquad\xi+\upsilon>M:=B-(1+\lambda(\tau))X_*. \tag{6}
\]
Vertices and RIGHT contact remain allowed.

### 2. Four full parameter domains independent of the angle of \(C\)

Suppose \(\tau\ge1/6\). The function \(B_c\) increases by R54. On \([0,4/15]\), \(B_\tau\) also increases:
\[
B_\tau'=\frac{2P(\tau)}{(1-\tau^2)^3},\quad
P=1-2\tau-6\tau^2+2\tau^3-3\tau^4,
\]
\[
P'\le-2+6(4/15)^2=-118/75<0,\quad P(4/15)=353/5625>0. \tag{7}
\]
Actual cosine and sine long-leg projections, and monotonicity of \(b,s\), give these complete rectangular enclosures:

1. \(\tau\in[1/6,1/5]\), \(B=B_\tau\), \(1/3<x<1/2\), since \(B_\tau(1/6)-5/4=79/4900>0\), and \(b(1/3)=1/s_{1/2}=5/4\).
2. \(\tau\in[1/5,4/15]\), \(B=B_\tau\), \(9/25<x<12/25\); the two exact margins at \(1/5\) are \(1/1224\) above \(b(9/25)\) and \(61/3600\) above \(1/s_{12/25}\).
3. \(\tau\in[4/15,3/10]\), \(B=B_c\), \(3/8<x<5/11\), since \(B_c(4/15)-b(3/8)=1282/218405>0\), and \(b(3/8)=1/s_{5/11}=73/55\).
4. \(\tau\in[3/10,2/5]\), \(B=B_c\), \(3/8<x<11/25\), using the respective margins \(288/8645\) and \(2008/475475\) at \(3/10\).

Closed endpoints are used for polynomial certificates; the actual \(\tau<2/5\). No central angle condition enters these domains.

### 3. Two auxiliary endpoint directions

Let \(K_* =\lambda(x)-\lambda(\tau)>0\). On each rectangle prove
\[
N_0=2(H_*-S)K_*-(1+H_*-S)(b(x)-B)>0, \tag{8}
\]
\[
\begin{split}
N_{45}={}&[B(\lambda(x)+1)-b(x)(1+\lambda(\tau))
-\mathcal K K_*](1+H_*-S)\\
&+2(H_*-S)K_*>0.
\end{split} \tag{9}
\]
Exactly,
\[
N_0=K_*(1+H_*-S)[j(H_*-S)-X_*],
\]
\[
N_{45}=K_*(1+H_*-S)[M+j(H_*-S)-\mathcal K]. \tag{10}
\]
Since \(0<S<1\), \(H_*-S>-1\) and both prefactors are positive. The first two rectangles have numerator degree \((8,4)\) for each expression, with 45 positive rational Bernstein coefficients each. The third has degree \((4,4)\) and 25 coefficients for each; the last axial expression has degree \((4,4)\) and 25 coefficients. These are seven new full polynomials and 255 new positive coefficients. The last diagonal expression is exactly R54's final joint certificate; its 25 coefficients are independently replayed but not counted as new. The checked denominators contain only positive integers and even powers of \(1-\tau^2,1-x^2\).

### 4. The same actual point pair

The bottom budget gives \(S_1>H_*-S\). Monotonicity of \(j\) yields \(Q>j(S_1)>j(H_*-S)\). Equations (6), (8)--(10) imply
\[
Q+\xi>1,\qquad Q+\xi+\upsilon>\mathcal K>\sqrt2. \tag{11}
\]
For \(\Delta=T_R-P_1=(\xi+\rho,\upsilon-e)\),
\[
\Delta_x=Q+\xi+e>1,\qquad
\Delta_x+\Delta_y=Q+\xi+\upsilon>\sqrt2. \tag{12}
\]
No assumption \(\upsilon\ge e\) is needed, and both bounds concern the same pair.

### 5. The two endpoint directions exclude all positive rotations

For \(0\le\theta\le45^\circ\), a positive-rotation normal \((c,s)\) requires
\[
c\Delta_x+s\Delta_y\le1. \tag{13}
\]
But
\[
c\Delta_x+s\Delta_y=(c-s)\Delta_x+s(\Delta_x+\Delta_y)
>(c-s)+\sqrt2s. \tag{14}
\]
Both coefficients are nonnegative and at least one is positive, including the two endpoints. With \(\eta=\tan(\theta/2)\),
\[
c+(\sqrt2-1)s-1=\frac{2\eta(\sqrt2-1-\eta)}{1+\eta^2}\ge0. \tag{15}
\]
Thus (14) exceeds one, contradicting (13). These are auxiliary directions for one fixed actual pair; the proof never rotates the original tile while presuming coverage survives. This proves (1).

### 6. Intermediate consequences and their scope

All remaining positive-rotation configurations with \(Q_U\in W\) satisfy
\[
z\le\tau<1/6,\quad u>5/6,\quad L_4<b(1/6)=37/35,
\quad D>33/35,
\]
\[
B_{\rm act}>1+\lambda(\tau)(33/35-\tau). \tag{16}
\]
The corresponding angle of \(W\) is below \(2\arctan(1/6)\), approximately \(18.9246444161^\circ\). Negative rotation has a different signed normal and inherits none of (1), (6), or (16); a general right bridge also lacks \(Q_U\in W\).

### 7. Strengthening the first cap to \(\tau<3/20\)

For \(\tau\in[3/20,1/6]\), choose \(B=B_\tau\). Its monotonicity and the exact margins
\[
B_\tau(3/20)-b(33/100)=3165924/1362322591>0,
\]
\[
B_\tau(3/20)-1/s_{101/200}=25582119/6176392400>0
\]
give \(33/100<x<101/200\). Each of (8), (9) has a new degree \((8,4)\) certificate with 45 positive coefficients on this full rectangle. The same-pair argument excludes it. Therefore
\[
\tau<3/20. \tag{17}
\]

### 8. The stronger same-\(F\) area budget and positive-rotation endpoints

Now use \(\eta>0\) for \(C\), \(\Lambda=\lambda(\eta)=s_C/c_C\), \(\delta=b(\eta)-1\). The actual vertical chord \(u+d\le b(\eta)\) gives
\[
d<\delta+\tau. \tag{18}
\]
The same original \(F\) contains the bottom endpoints and \(D_C\). Their triangle gives \((2\mu-\Sigma)(\mu-d)\le1\). On the domains used below, \(\delta+\tau<1\); thus \(d<1\) and \(\mu>1\) imply
\[
\Sigma>H_F(\eta,\tau):=2-\frac1{1-\delta-\tau}. \tag{19}
\]
This uses three actual points of one tile. Positive-rotation normals on \(P_1,U_C\) and \(R_C,U_C\) give
\[
Q<A(\eta,\tau):=g(\eta)+\lambda(\eta)\tau,
\quad x>X(\eta,\tau):=1-\eta-\frac\tau{\lambda(\eta)}. \tag{20}
\]
On each application domain, \(0<A,X<1\) will be checked. Then
\[
\Sigma<U(\eta,\tau):=q(A)+g(X)-\lambda(X)(B_\tau-1). \tag{21}
\]
This combines the same \(S_1,S_2\), using R53, the actual right long leg, monotonicity of \(g,\lambda\), and \(B_\tau>1\).

### 9. A fixed-pair lemma with a finite auxiliary angle endpoint

Fix \(\eta_0\le\sqrt2-1\) and suppose the actual \(0\le\eta\le\eta_0\). Suppose \(\Sigma>H>0\), choose a legal \(B\), and set \(S=b(x)-\lambda(x)B\), \(K_* =\lambda(x)-\lambda(\tau)\), \(X_*=(b(x)-B)/K_*\). For auxiliary \(v\in\{0,\eta_0\}\), define
\[
\begin{split}
E_v=K_*(1+H-S)\big[&(1-v^2)(j(H-S)+1-X_*)\\
&+2v(B-1-\lambda(\tau)X_*)-(1+v^2)\big].
\end{split} \tag{22}
\]
If both are positive, the entire central angle interval is excluded. Indeed actual \(Y\ge B_{\rm act}-\lambda(\tau)X\), \(X<X_*\) imply
\[
(1-v^2)\xi+2v\upsilon
=(1-v^2-2v)\mu+2vY-(1-v^2)X
\]
\[
>(1-v^2)(1-X_*)+2v(B-1-\lambda(\tau)X_*). \tag{23}
\]
The weakening \(\mu\mapsto1\) is permitted precisely because \(1-v^2-2v\ge0\). It does not assign separately relaxed coordinates to a fabricated point. Put \(A_0=Q+\xi>0\), \(V=\upsilon>0\). The bottom budget, (5), and (23) give
\[
F(v)=(A_0-1)+2vV-(A_0+1)v^2>0\quad(v=0,\eta_0). \tag{24}
\]
This is concave for the same actual pair, and
\[
F(\eta)-[(1-\eta/\eta_0)F(0)+(\eta/\eta_0)F(\eta_0)]
=(A_0+1)\eta(\eta_0-\eta)\ge0.
\]
Yet the actual normal gives \(c(Q+\xi)+s\upsilon+(c-s)e\le1\), with \(e>0,c-s\ge0\), forcing \(F(\eta)\le0\). This proves the lemma.

If \(\eta\le1/5\), then \(\delta\le1/12\), and (17), (19) give \(H_F>16/23\). If \(1/20\le\tau<3/20\), the exact equality of margins
\[
B_\tau(1/20)-b(1/5)=B_\tau(1/20)-1/s_{2/3}=7261/636804>0
\]
gives \(1/5<x<2/3\). On \([1/20,3/20]\times[1/5,2/3]\), (22), with \(H=16/23\), \(v=0,1/5\), has two degree \((8,4)\) certificates of 45 positive coefficients each. Therefore
\[
\eta\le1/5\quad\Longrightarrow\quad\tau<1/20. \tag{25}
\]
If \(\eta\le1/10\), then \(\delta\le2/99\), so (25) gives \(H_F>1702/1841>12/13\), with margin \(34/23933\). If \(1/100\le\tau<1/20\),
\[
B_\tau(1/100)-b(1/11)=B_\tau(1/100)-1/s_{5/6}
=6261373/1999600020>0.
\]
Thus \(1/11<x<5/6\). On \([1/100,1/20]\times[1/11,5/6]\), the two expressions (22), with \(H=12/13\), \(v=0,1/10\), again have degree \((8,4)\) and 45 positive coefficients each. Hence
\[
\eta\le1/10\quad\Longrightarrow\quad\tau<1/100. \tag{26}
\]

### 10. Four endpoint inequalities finish every remaining angle

For the same \(U\) in (21), the source certifies the following full domains:

1. \(\eta\in[1/4,5/12]\), \(\tau\in[0,3/20]\): \(7/12-U>0\), numerator degree \((6,7)\), 56 positive rational coefficients.
2. \(\eta\in[1/5,1/4]\), \(\tau\in[0,3/20]\): \(H_F-U>0\), degree \((8,8)\), 81 positive coefficients.
3. \(\eta\in[1/10,1/5]\), \(\tau\in[0,1/20]\): \(H_F-U>0\), the same degree and 81 positive coefficients.
4. \(\eta\in[1/24,1/10]\), \(\tau\in[0,1/100]\): \(H_F-U>0\), the same degree and 81 positive coefficients.

For explicit denominator signs define
\[
f_1=\eta^2\tau-2\eta^2-\tau=-2\eta(1-X)<0,
\]
\[
f_2=3\eta^2+2\eta\tau-2\eta-1=(1-\eta^2)(A-2)<0,
\]
\[
f_3=\eta^2\tau-3\eta^2-\tau+1=(1-\eta^2)(1-\delta-\tau)>0,
\]
\[
f_4=\eta^2\tau-2\eta^2+4\eta-\tau=2\eta(1+X)>0.
\]
The first denominator is \(12(1-\tau^2)^2f_1f_2f_4\); the others are \((1-\tau^2)^2f_1f_2f_3f_4\). All are positive. On these domains \(A>0\), and \(A=1-\lambda(\eta)(1-\eta-\tau)<1\) since \(\eta+\tau<1\). Also \(X<1\), with respective uniform lower bounds \(29/96,39/100,221/400,749/960>0\). In the last three domains, \(\delta+\tau\) is at most \(17/60,2/15,299/9900<1\). Thus no illegal \(q\) argument, negative denominator, or short-leg division occurs.

The actual \(\eta\le\sqrt2-1<5/12\). Equations (17), (25), (26) place each remaining angle in the corresponding \(\tau\) domain. The same \(F\)'s lower bound \(\Sigma>7/12\) or \(\Sigma>H_F\) contradicts (21) and the certificate. Finally R52 already excludes \(0\le\eta\le1/24\). The entire positive-rotation class with \(Q_U\in W\) is therefore excluded.

<a id="R56"></a>
## R56. A continuous high-angle exclusion for negative rotation with \(Q_U\in W\)

**Scope.** Work on the actual target \([-\mu,\mu]^2\), \(\mu>1\), with unchanged original \(C,F\). Assume \(Q_U\in W\): then \(Q_R\in C\), the legal \(W\) lies in \(y>0\), \(F\subset\{y<0\}\), and \(C\) misses BOTTOM. Use \(\tau,x,z\) for the half-angles of \(W,V_2,V_4\), and \(\eta\) for that of \(C\). In this module \(\lambda(v)=2v/(1-v^2)\); \(b,g,q,j\) have the definitions of R55.

### 1. Actual common inputs

We have \(0<z\le\tau<2/5\), \(z<4/15\), \(x>\tau\), \(u>1-\tau\), \(r>1-x\). Set
\[
B_\tau=1+\lambda(\tau)(1-(b(\tau)-1)-\tau),\quad
B_c=1+\lambda(\tau)(177/209-\tau),\quad H_*=7/12.
\]
The actual long leg obeys \(L_2\le b(x)\), \(s_xL_2\le1\), and \(S_2=b(x)-\lambda(x)L_2\ge0\). R53 supplies \(P_1=(-Q-e,e)\in C\), with \(e>0\), \(0<Q<1\), \(S_1<q(Q)\); R48 supplies the actual \(T_R=(\xi,\upsilon)\in C\cap V_2\cap W\), allowing RIGHT and vertex contact. The same \(F\) gives \(\Sigma>2-\sqrt2>H_*\). For a legal \(B\le B_z=1+\lambda(\tau)(1-\Delta_z-\tau)\),
\[
K_*=\lambda(x)-\lambda(\tau)>0,\quad
S=b(x)-\lambda(x)B>S_2\ge0,\quad S<1,
\]
\[
X_*=(b(x)-B)/K_*,\quad Q>j(H_*-S),\quad1+H_*-S>0. \tag{1}
\]
The argument \(H_*-S\) may be negative, but exceeds \(-1\).

### 2. Both actual coordinate bounds retain their \(\mu\) dependence

Put \(X=\mu-\xi\ge0,Y=\upsilon+\mu\). The actual supports give
\[
Y\le b(x)-\lambda(x)X,\quad Y\ge B_{\rm act}-\lambda(\tau)X,
\quad B_{\rm act}=2\mu-b(\tau)+\lambda(\tau)D.
\]
Actual TOP contact gives \(D\ge2\mu-L_4\ge2\mu-b(z)\), hence the stronger relation
\[
B_{\rm act}\ge B_z+2(1+\lambda(\tau))(\mu-1). \tag{2}
\]
Together with R54's \(X<X_*\), this proves, for the same actual point,
\[
\xi>1-X_*,\qquad\upsilon>B-1-\lambda(\tau)X_*. \tag{3}
\]
In full, the second bound follows from
\[
\upsilon\ge B_z-1-\lambda(\tau)X+(1+2\lambda(\tau))(\mu-1)
>B-1-\lambda(\tau)X_*.
\]
The weaker isolated statement \(B_{\rm act}>B\) would not justify it. Either lower bound may be negative; neither defines a new placement of \(T_R\).

There is also a two-rotation cap
\[
\tau<19/50. \tag{4}
\]
Indeed \(B_c\) increases, \(L_2>B_c\), \(L_2\le\sqrt2\), and
\(B_c(19/50)^2-2=796687/553613841>0\). No positive-rotation cap from R55 is used.

### 3. Eliminating the seam height from negative-rotation widths

Write \(c=(1-\eta^2)/(1+\eta^2)\), \(s=2\eta/(1+\eta^2)\), with actual \(c\ge s\ge0\). The negative-rotation normals are \((c,-s),(s,c)\). Applying them to \(P_1,R_C,U_C\) gives
\[
c(Q+r)+(c+s)e\le1,\quad sQ+cu-(c-s)e\le1.
\]
Multiply by \(c-s,c+s\), respectively, and add. The \(e\) terms cancel and \(c^2+s^2=1\), giving
\[
Q+c(c-s)r+c(c+s)u\le2c. \tag{5}
\]
Using the strict actual reach bounds,
\[
Q<A_-(\eta,\tau,x):=2c(1-c)+c(c+s)\tau+c(c-s)x. \tag{6}
\]
The \((c,-s)\) width of \(R_C,U_C\) yields
\[
x>X_-(\eta,\tau):=1-b(\eta)+\lambda(\eta)(1-\tau)
=\lambda(\eta)(1-\eta-\tau). \tag{7}
\]
Replacing the second seam-to-upper-endpoint constraint by the actual seam-to-\(T_R\) constraint and using the same weights gives
\[
Q+c(c-s)r+(c+s)(s\xi+c\upsilon)\le2c. \tag{8}
\]
At \(c=s\), one weight is zero and the other remains positive. These are negative-rotation deductions, not the positive-rotation formulas of R55.

### 4. Small \(\tau\le1/6\): an axis-endpoint budget

For this module's range \(\eta\ge3/8\), we also have \(\eta\ge1/3\), \(c\le4/5\), \(c-s\le1/5\), so \(0\le c(c-s)\le4/25\). In the actual domain \(0<A_-<1\): the bounds \(2c(1-c)<1/2\), \(c(c+s)<5/4\), \(c(c-s)x<4/25\) give a sum below \(91/100\), even if \(\tau\) is enlarged to \(1/5\). For fixed \(\eta,\tau\),
\[
V(x)=q(A_-)+g(x)-\lambda(x)(B_\tau-1)
\]
strictly decreases, because \(q'\le2\), \(g'\le-1/2\), \(\lambda'>0\), and
\[
V'(x)<8/25-1/2=-9/50<0. \tag{9}
\]
Thus \(\Sigma<V(X_-)\). Here \(0<X_-<1\), with lower bound \(4/11\), and
\((1-\eta^2)(1-X_-)=(1-\eta)^2+2\eta\tau>0\). Exact substitution gives
\[
A_-(\eta,\tau,X_-)=c+s-1+\tau=:A_0,
\quad\Sigma<U_-:=q(A_0)+g(X_-)-\lambda(X_-)(B_\tau-1). \tag{10}
\]
This compares the whole sum as a function of \(x\); it does not separately assert \(Q<A_0\).

On \(\eta\in[3/8,5/12]\), \(\tau\in[0,1/6]\), the source proves
\[
H_*-U_->0 \tag{11}
\]
with numerator degree \((6,7)\) and 56 strictly positive rational Bernstein coefficients. The positive denominator is \(12(1-\tau^2)^2f_1f_2f_3\), where
\[
f_1=\eta^2+2\eta\tau-2\eta+1=(1-\eta^2)(1-X_-)>0,
\]
\[
f_2=3\eta^2+2\eta\tau-2\eta-1=-(1-\eta^2)(1+X_-)<0,
\]
\[
f_3=\eta^2\tau-4\eta^2+2\eta+\tau-2=(1+\eta^2)(A_0-2)<0.
\]
On the full algebraic rectangle \(0<X_-<1\), \(0<A_0<1\): positivity follows from \(\eta+\tau<1\), while \(A_0<\sqrt2-1+1/6<1\). The auxiliary endpoint \(5/12>\sqrt2-1\) is polynomial extension only; actual geometry retains \(\eta\le\sqrt2-1\). Equation (11) contradicts the same bottom budget.

### 5. Large \(\tau\): combining two necessary inequalities

Set \(J=j(H_*-S)\),
\[
E_{\rm axis}=J-A_-,
\]
\[
E_{\rm joint}=J+c(c-s)(1-x)
+(c+s)[s(1-X_*)+c(B-1-\lambda(\tau)X_*)]-2c.
\]
Every actual covering has both expressions negative, by (1), (3), (6), (8). It is enough to prove their sum positive; neither must separately be positive on the full parameter domain. Put \(d_0=1+\eta^2,c_0=1-\eta^2,s_0=2\eta,G=b(x)-B\). The exact cleared target is
\[
\begin{aligned}
N={}&K_*(1+H_*-S)d_0^2(E_{\rm axis}+E_{\rm joint})\\
={}&4(H_*-S)K_*d_0^2+(1+H_*-S)\{c_0(c_0-s_0)(1-2x)K_*\\
&+(c_0+s_0)[s_0(K_*-G)+c_0((B-1)K_*-\lambda(\tau)G)]\\
&+[-4c_0d_0+2c_0^2-c_0(c_0+s_0)\tau]K_*\}.
\end{aligned} \tag{12}
\]
Its prefactor is positive in the actual domain. Use R55's rotation-independent long-leg domains, replacing the last upper \(\tau\) endpoint by (4):

1. \(\tau\in[1/6,1/5]\), \(B=B_\tau\), \(x\in[1/3,1/2]\).
2. \(\tau\in[1/5,4/15]\), \(B=B_\tau\), \(x\in[9/25,12/25]\).
3. \(\tau\in[4/15,3/10]\), \(B=B_c\), \(x\in[3/8,5/11]\).
4. \(\tau\in[3/10,19/50]\), \(B=B_c\), \(x\in[3/8,11/25]\).

All four take \(\eta\in[3/8,5/12]\). In variable order \((\tau,x,\eta)\), the numerator degrees are \((9,5,4),(9,5,4),(5,5,4),(5,5,4)\), with respectively 300, 300, 180, 180 strictly positive rational coefficients. The first two positive denominators are \(6(1-\tau^2)^4(1-x^2)^2\); the last two are \(262086(1-\tau^2)^2(1-x^2)^2\). The full continuous domains cover all remaining \(\tau\), establishing the contradiction without sampling, layout optimization, or an interval tree.

<a id="R57"></a>
## R57. An actual lower-left exit point excludes a middle negative-rotation range

**Scope.** Retain R56's actual target, original \(C,F\), \(Q_U\in W\), direct \(Q_R\in C\), and \(F\subset\{y<0\}\). Use \(\eta\) for the negative-rotation half-angle of \(C\), \(\tau\) for that of \(W\), \(\Lambda=\lambda(\eta)=s/c\), \(\delta=b(\eta)-1=\eta\Lambda\). The negative normals are \((c,-s),(s,c)\); \(b,\lambda,g,q\) are as in R56.

### 1. Actual axis endpoints and the actual lower-left interface

The actual reaches obey \(l>1-a,u>1-\tau,r>1-x\), and \(S_1<g(a)\). The actual right leg gives \(S_2<g(x)-\lambda(x)(B_\tau-1)\), with \(B_\tau=1+\lambda(\tau)(1-(b(\tau)-1)-\tau)>1\). The same bottom chord requires \(\Sigma>H_*=7/12\), and actual \(\tau>0\). The two negative-rotation widths on \(L_C,U_C\) and \(R_C,U_C\) give
\[
a>\alpha:=1-\eta-\tau/\Lambda,\qquad
x>X:=\Lambda(1-\eta-\tau). \tag{1}
\]
No LEFT-midpoint membership of \(C\) is assumed. R46's actual exit point is \(E_1=(-w,-v)\in C\cap F\cap V_1\), \(w,v>0\). Its \((s,c)\) width with \(U_C\) gives
\[
\Lambda w+v\le b(\eta)-u<\delta+\tau. \tag{2}
\]
The actual first upper support of \(V_1\) gives
\[
w+v/\lambda(a)>1-a. \tag{3}
\]
Strictness follows from \(\mu>1\). This holds on either edge or at the vertex, without selecting an active face of \(C\) or identifying \(v\) with \(d\).

When \(a>\alpha>\eta\), combining (2)--(3), with the positive denominator justified by this ordering, yields
\[
v<V(a):=\frac{2\eta a(a-\alpha)}{(a-\eta)(1+\eta a)}. \tag{4}
\]
The function is strictly increasing on \(a>\alpha>\eta\), since it is the product \(2\eta[a/(1+\eta a)][(a-\alpha)/(a-\eta)]\) of two positive increasing factors. This remains true for an auxiliary argument \(a>1\), without interpreting that argument as a physical corner angle.

### 2. The same-\(F\) triangle excludes a full middle-angle, small-\(\tau\) rectangle

Suppose
\[
3/10\le\eta\le3/8,\qquad0<\tau\le1/5. \tag{5}
\]
The concave quadratic \(-19\eta^2+10\eta-1\) is positive at both endpoints, with smaller endpoint value \(5/64\). Hence \(\Lambda(1-2\eta)-\tau>0\), proving the crucial premise \(\alpha>\eta\). Set \(D=\eta+\tau/\Lambda=1-\alpha\). Then \(0<D\le407/600<1\), and \(0<X<1\), since \(\eta+\tau<1\) and \((1-\eta^2)(1-X)=(1-\eta)^2+2\eta\tau>0\).

Define
\[
T_2=g(X)-\lambda(X)(B_\tau-1),\quad P=H_*-T_2,
\quad A=g(P),\quad U=q(D)+T_2. \tag{6}
\]
Actual \(S_2<T_2\) and \(S_2\ge0\) give \(T_2>0\), while \(T_2<g(X)<1\), so \(-1<P<H_*<1\), \(A>0\). From \(S_1>P\) and \(S_1<g(a)\), we get \(a<A\). Thus \(A>a>\alpha>\eta\), making the denominator in \(V(A)\) positive and the monotone comparison legitimate. Also \(S_1<g(\alpha)=q(D)\), giving
\[
\Sigma<U<2,\qquad0<v<V(A). \tag{7}
\]
No assumption \(A<1\) is needed. On the entire actual domain,
\[
(2-U)(1-V(A))-1>0. \tag{8}
\]
The source proves this by a full-rectangle polynomial certificate on \([3/10,3/8]\times[0,1/5]\). For explicit denominator accounting, put
\[
Z=1-\eta^2,\quad Y=2\eta(1-\eta-\tau),\quad B_\tau=B_n/B_d,
\quad B_d=(1-\tau^2)^2>0,
\]
\[
T_d=(Z^2-Y^2)B_d,\quad T_n=(Z^2+Y^2)B_d-2B_nYZ,
\]
\[
N=5T_d+12T_n,\quad M=19T_d-12T_n,\quad A=N/M,
\]
\[
\alpha_n=2\eta(1-\eta)-\tau Z,\quad
V_n=2\eta N^2-\alpha_nNM,\quad V_d=(N-\eta M)(M+\eta N),
\]
\[
D_n=2\eta^2+\tau Z,\qquad Q_d=4\eta-D_n.
\]
Then \(T_2=T_n/T_d\), \(V(A)=V_n/V_d\), \(q(D)=D_n/Q_d\). The denominator \(Q_dT_dV_d\) is positive in the actual domain, using \(T_d,Q_d,M>0,N>\eta M\). Those signs need not be asserted at relaxed points lacking an actual configuration. The exact numerator of (8) is
\[
\mathcal N=(2Q_dT_d-D_nT_d-T_nQ_d)(V_d-V_n)-Q_dT_dV_d. \tag{9}
\]
It has degree \((16,20)\), with 357 strictly positive rational Bernstein coefficients on the complete rectangle, independently reconstructed in the source. Since \(U<2\), (8) also gives \(V(A)<1\). The same original \(F\) contains the actual bottom endpoints and \(E_1\); its triangle-area bound requires \((2\mu-\Sigma)(\mu-v)\le1\). Equations (7)--(8) and \(\mu>1\) make this product exceed one, a contradiction.

### 3. Large \(\tau\): retaining a nonnegative actual short-leg slack

Now take \(1/3\le\eta\le3/8\), \(\tau\ge1/5\). The two-rotation cap \(\tau<19/50\) of R56 remains applicable. Set \(S=b(x)-\lambda(x)B>S_2\ge0\), \(K_* =\lambda(x)-\lambda(\tau)>0\), \(X_*=(b(x)-B)/K_*\), and \(J=2(H_*-S)/(1+H_*-S)\). Retain R56's
\[
A_-=2c(1-c)+c(c+s)\tau+c(c-s)x,
\]
\[
E_{\rm axis}=J-A_-<0,
\]
\[
E_{\rm joint}=J+c(c-s)(1-x)
+(c+s)[s(1-X_*)+c(B-1-\lambda(\tau)X_*)]-2c<0.
\]
They concern the same actual \(P_1,R_C,U_C,T_R\), with the \(\mu\)-linked coordinate bounds. Define
\[
\mathcal L=K_*(1+H_*-S)(1+\eta^2)^2(E_{\rm axis}+E_{\rm joint}). \tag{10}
\]
Every actual covering has \(\mathcal L<0\). On these three full actual long-leg domains the source certifies the opposite:

1. \(\tau\in[1/5,4/15]\), \(x\in[9/25,12/25]\), \(B=B_\tau\): \(\mathcal L-S/3>0\).
2. \(\tau\in[4/15,3/10]\), \(x\in[3/8,5/11]\), \(B=B_c\): \(\mathcal L>0\).
3. \(\tau\in[3/10,19/50]\), \(x\in[3/8,11/25]\), \(B=B_c\): \(\mathcal L-S/3>0\).

All take \(\eta\in[1/3,3/8]\), \(B_c=1+\lambda(\tau)(177/209-\tau)\). The slack \(S/3\) in the first and third cases is actually positive, not a deleted parameter. Numerator degrees are \((9,5,4),(5,5,4),(5,5,4)\), with 300, 180, 180 strictly positive rational coefficients. The positive denominator is \(6(1-\tau^2)^4(1-x^2)^2\) for the first target and \(262086(1-\tau^2)^2(1-x^2)^2\) for each of the last two targets. The explicit multiplier is exactly \(1/3\). Each certificate forces \(\mathcal L>0\), contradicting the actual necessary inequalities.

<a id="R58"></a>
## R58. Extending the negative-rotation exclusion to \(\eta\ge1/6\)

**Scope.** Keep the original \(C,F\), assume \(Q_U\in W\), direct \(Q_R\in C\), legal \(W\subset\{y>0\}\), \(F\subset\{y<0\}\), and no BOTTOM contact by \(C\). Use core half-angles \(\eta,\tau\), with \(b,\lambda,g,q,j\) as in R56 and \(H_*=7/12\). Let \(B_\tau,B_c\) be R56's legal bounds.

### 1. A new lower bound for the actual left endpoint

The actual reaches satisfy \(l>1-a,r>1-x,u>1-\tau\), \(S_1<g(a)\), and \(\Sigma>H_*\). For a legal \(B\le B_z\), put
\[
K_* =\lambda(x)-\lambda(\tau)>0,\quad S=b(x)-\lambda(x)B>S_2\ge0,\quad S<1,
\]
\[
P=H_*-S>-1,\quad J=j(P),\quad
X_*=(b(x)-B)/K_*,\quad Y_*=B-1-\lambda(\tau)X_*.
\]
The same actual \(T_R=(\xi,\upsilon)\) obeys \(\xi>1-X_*\), \(\upsilon>Y_*\), the latter retaining R56's \(\mu\) dependence. From \(S_1<g(a)\) and monotonicity of \(j\),
\[
l>1-a=j(g(a))>j(S_1)>j(H_*-S)=J. \tag{1}
\]
This does not make the left endpoint equal to the seam point or assume LEFT-midpoint membership. A negative \(J\) remains a valid lower bound.

### 2. Four actual width inequalities give an all-angle \(\tau\) cap

Write \(c=(1-\eta^2)/(1+\eta^2),s=2\eta/(1+\eta^2)\), with negative normals \((c,-s),(s,c)\). The widths of \(L_C,R_C\) and \(L_C,T_R\) give
\[
E_H=c(J+1-x)-1<0,\quad
E_L=s(J+1-X_*)+cY_*-1<0. \tag{2}
\]
The original seam elimination of R56 gives
\[
A_-=2c(1-c)+c(c+s)\tau+c(c-s)x,
\]
\[
E_A=J-A_-<0,
\]
\[
E_P=J+c(c-s)(1-x)+(c+s)[s(1-X_*)+cY_*]-2c<0. \tag{3}
\]
Here \(J\) is also a lower bound for the seam coordinate \(Q\); no equality \(Q=l\) is asserted. Suppose \(\tau\ge1/5\); R56 gives \(\tau<19/50\). The actual long-leg domains are \([1/5,4/15]\) with \(B_\tau,9/25<x<12/25\); \([4/15,3/10]\) with \(B_c,3/8<x<5/11\); and \([3/10,19/50]\) with \(B_c,39/100<x<11/25\). The final lower bound is strengthened here using
\[
B_c(3/10)-b(39/100)=293184/161262101>0.
\]
On each full domain the source proves
\[
\begin{array}{ll}
0\le\eta\le3/10:&E_H+\frac{\lambda(\eta)}2E_L>0,\\
3/10\le\eta\le1/3:&3E_H+2E_A+2E_P>0.
\end{array} \tag{4}
\]
All combination weights are nonnegative, contradicting (2)--(3) for one actual configuration.

For exact denominator accounting, write \(B=B_n/B_d\), with \(B_d=(1-\tau^2)^2\) for \(B_\tau\) and \(B_d=209(1-\tau^2)\) for \(B_c\). Define
\[
d_x=1-x^2,\quad d_\tau=1-\tau^2,\quad d=1+\eta^2,\quad c_0=1-\eta^2,
\]
\[
S_d=d_xB_d,\quad S_n=(1+x^2)B_d-2xB_n,
\quad J_d=19S_d-12S_n=12S_d(1+P)>0,
\]
\[
K_n=2(x-\tau)(1+x\tau)B_d>0.
\]
Multiply the first target in (4) by \(c_0dJ_dB_dd_\tau K_n\), the second by \(d^2J_dB_dd_\tau K_n\). These multipliers are positive in the actual domain. In variable order \((\tau,x,\eta)\), the first three numerator degrees are \((16,5,4),(10,5,4),(10,5,4)\), with 510,330,330 positive coefficients; the second three are \((17,5,4),(11,5,4),(11,5,4)\), with 540,360,360 positive coefficients. Together with R57 for \(\eta\in[1/3,3/8]\) and R56 for \(\eta\ge3/8\), every remaining negative-rotation configuration must have \(\tau<1/5\). No positive-rotation cap is used.

### 3. Two actual lower bounds for \(x\) depending on \(\tau\)

The actual \(L_2>B_\tau\), \(L_2\le b(x)\), and monotonicity of \(b\) combine with
\[
B_\tau>b(\tau+1/6)\quad(1/10\le\tau\le1/6),
\]
\[
B_\tau>b((1+4\tau)/5)\quad(1/6\le\tau\le1/5) \tag{5}
\]
to give strict lower bounds for \(x\). The two one-variable certificates have seven and six positive coefficients; their positive denominators are \(-(1-\tau^2)^2(6\tau-5)(6\tau+7)\) and \(4(1-\tau^2)^2(2\tau+3)\). The negative-rotation width also gives
\[
x>X_R:=\lambda(\eta)(1-\eta-\tau). \tag{6}
\]
Any convex combination of simultaneously applicable lower bounds remains a strict lower bound; it is not a new actual corner.

### 4. The actual \(E_1\) and same \(F\) exclude \(1/6\le\eta\le3/10\)

We already have \(\tau<1/5\). The concave quadratic \(-19\eta^2+10\eta-1\) has positive endpoint values \(5/36,29/100\) on \([1/6,3/10]\), so
\[
\alpha=1-\eta-\tau/\lambda(\eta)>\eta. \tag{7}
\]
R57's actual interface argument therefore gives
\[
a>\alpha>\eta,\quad v<V(a)=\frac{2\eta a(a-\alpha)}{(a-\eta)(1+\eta a)},
\quad E_1=(-w,-v)\in C\cap F\cap V_1. \tag{8}
\]
The function increases in its argument above \(\alpha\), even beyond one. The actual interface may lie on either edge or at the vertex, and \(v\ne d\) is allowed. For any legal \(0<X<x\), \(X<1\), set
\[
T_2=g(X)-\lambda(X)(B_\tau-1),\quad A=g(H_*-T_2),
\quad D=\eta+\tau/\lambda(\eta),\quad U=q(D)+T_2.
\]
Actual \(S_2<T_2\), \(\Sigma>H_*\), \(S_1<g(a)\) give \(A>a>\alpha>\eta\), \(0<T_2<1\), \(0<D<1\), so all needed denominators are positive and
\[
\Sigma<U<2,\qquad v<V(A). \tag{9}
\]
The source proves
\[
(2-U)(1-V(A))>1 \tag{10}
\]
on four complete domains:

1. \(\eta\in[1/6,3/10]\), \(\tau\in[0,1/10]\), \(X=X_R\).
2. \(\eta\in[1/6,1/5]\), \(\tau\in[1/10,1/6]\), \(X=\tau+1/6\).
3. \(\eta\in[1/5,3/10]\), \(\tau\in[1/10,1/6]\), \(X=(3X_R+\tau+1/6)/4\).
4. \(\eta\in[1/6,3/10]\), \(\tau\in[1/6,1/5]\), \(X=(1+4\tau)/5\).

Their legality follows from (5)--(6), with \(0<X<1\) checked in each. Auxiliary \(\tau=0\) only closes the polynomial domain. For each chosen \(X=Y/Z\), \(Z>0\), recompute the numerator rather than reuse the old \(X_R\) expression. With \(B_d=(1-\tau^2)^2\), \(B_\tau=B_n/B_d\), put
\[
T_d=(Z^2-Y^2)B_d,\quad T_n=(Z^2+Y^2)B_d-2B_nYZ,
\]
\[
N=5T_d+12T_n,\quad M=19T_d-12T_n,\quad
\alpha_n=2\eta(1-\eta)-\tau(1-\eta^2),
\]
\[
V_n=2\eta N^2-\alpha_nNM,\quad V_d=(N-\eta M)(M+\eta N),
\]
\[
D_n=2\eta^2+\tau(1-\eta^2),\qquad Q_d=4\eta-D_n.
\]
The exact numerator of (10) minus one is
\[
\mathcal N=[(2Q_d-D_n)T_d-T_nQ_d](V_d-V_n)-Q_dT_dV_d. \tag{11}
\]
Its denominator \(Q_dT_dV_d\) is positive in the actual domain by \(0<X,D<1\), \(A>\alpha>\eta\), without imposing these signs on unrealizable relaxed points. The four numerator degrees in order \((\eta,\tau)\) are \((16,20),(4,20),(16,20),(4,20)\), with 357,105,357,105 strictly positive coefficients.

Since \(U<2\), (10) implies \(V(A)<1\). The triangle in the same original \(F\), formed from the bottom endpoints and this same \(E_1\), requires \((2\mu-\Sigma)(\mu-v)\le1\). Equations (9)--(10) and \(\mu>1\) force the product above one. This excludes \([1/6,3/10]\). R57 covers \([3/10,1/3]\) when \(\tau<1/5\), and the higher ranges are already closed. Hence every negative rotation with \(\eta\ge1/6\) is excluded.

### 5. The remaining small \(\eta\) also requires \(\tau<1/6\)

For \(\eta\le1/6\), suppose \(1/6\le\tau<1/5\). Then \(\delta\le2/35\); the legal long-leg domain gives \(1/3<x<1/2\) and \(B_\tau>5/4\). The same horizontal chord gives \(a+x>1-\delta\). As \(x+2/35<1\),
\[
S_1<q(x+2/35),\quad S_2<b(x)-\tfrac54\lambda(x).
\]
On the entire \([1/3,1/2]\),
\[
H_*-q(x+2/35)-b(x)+\tfrac54\lambda(x)>0. \tag{12}
\]
The denominator \(12(x-1)(x+1)(35x-68)\) is positive, and the cubic Bernstein coefficients are \(458/27,1375/27,2645/36,717/8\). Thus \(\Sigma<H_*\), contradicting the same bottom budget. Therefore \(\tau<1/6\).

<a id="R59"></a>
## R59. Excluding the entire upper-bridge mechanism

**Scope.** The complete remaining input from R58 is the negative-rotation domain
\[
1/24<\eta<1/6,\qquad0<\tau<1/6. \tag{1}
\]
The original \(W\) contains \(Q_U\) throughout. The original \(C,F\) stay fixed; budgets specific to this membership are not transferred to a general right bridge. Positive rotation was closed in R55.

### 1. An area budget for the same actual \(C,F\)

Let \(L_C=(-l,0),R_C=(r,0),U_C=(0,u),D_C=(0,-d)\). Direct \(Q_R\) contact holds, \(F\subset\{y<0\}\), and \(C\) misses BOTTOM. The actual coverage arguments of R46/R48 put \(D_C\) and both complete bottom-gap endpoints in the same original \(F\). Use \(\Lambda=\lambda(\eta)\), \(\delta=b(\eta)-1=\eta\Lambda\), and
\[
B_\tau=1+\lambda(\tau)(1-(b(\tau)-1)-\tau).
\]
The actual inputs are \(l>1-a,r>1-x,u>1-\tau,S_1<g(a)\), and
\[
L_2>B_\tau,\quad S_2=b(x)-\lambda(x)L_2
<g(x)-\lambda(x)(B_\tau-1),
\]
\[
\tau<T_c(x)=\frac{2x^2}{1-x^2},\qquad
\tau<T_s(x)=\frac{(1-x)^2}{2x}. \tag{2}
\]
The last two follow from the two actual projections of \(L_2>1+\tau\). The legal vertical-chord bound \(u+d\le b(\eta)\), rather than the old \(u+d<1\), gives
\[
d<\delta+\tau<2/35+1/6=47/210<1. \tag{3}
\]
The triangle formed by the two bottom endpoints and \(D_C\) requires \((2\mu-\Sigma)(\mu-d)\le1\). Since \(\mu-d>0\), and \(2\mu-1/(\mu-d)\) strictly increases in \(\mu\),
\[
\Sigma\ge2\mu-\frac1{\mu-d}>2-\frac1{1-d}
>H_F(\delta,\tau):=2-\frac1{1-\delta-\tau}. \tag{4}
\]
The final comparison uses (3) and monotonic decrease in \(d\). No interface height is equated to \(d\), and no second fitting tile is introduced.

### 2. The horizontal chord supplies a necessary negative expression

The same chord \(l+r\le b(\eta)\) gives \(a+x>1-\delta\). When \(x+\delta<1\),
\(S_1<g(a)<q(x+\delta)\). This is used only at \(x\le3/4\), where \(\delta\le2/35\) guarantees its domain. Every actual covering then requires
\[
G(x,\tau,\delta)<0, \tag{5}
\]
\[
G=2-\frac1{1-\delta-\tau}-q(x+\delta)-g(x)
+\lambda(x)(B_\tau-1). \tag{6}
\]
This is the difference between two budgets for the same actual tiles. On \(\delta+\tau<1,x+\delta<2\),
\[
G_\delta=-\frac1{(1-\delta-\tau)^2}-\frac2{(2-x-\delta)^2}<0. \tag{7}
\]
Also
\[
B_\tau''=-\frac{4(3\tau^5-3\tau^4+18\tau^3+2\tau^2+3\tau+1)}{(1-\tau^2)^4}<0
\]
on \([0,1/6]\), because its bracket is at least \(1-3(1/6)^4=431/432>0\). Consequently
\[
G_{\tau\tau}=-\frac2{(1-\delta-\tau)^3}+\lambda(x)B_\tau''<0. \tag{8}
\]
At fixed \(x,\delta\), the function is strictly concave in \(\tau\); its value on a complete closed interval is at least the smaller endpoint value. We first increase \(\delta\) by (7), then apply this endpoint argument.

### 3. Small \(x\): an actual quadratic bound for \(\delta\)

The negative-rotation \((c,-s)\) width of \(R_C,U_C\) gives
\[
x>\lambda(\eta)(1-\eta-\tau)>4\eta/3, \tag{9}
\]
using \(1-\eta-\tau>2/3\), \(\lambda(\eta)>2\eta\). Thus \(\eta<3x/4\), and \(\eta<1/6\) yields
\[
\delta<\delta_s(x):=81x^2/70. \tag{10}
\]
For \(0<x\le1/6\), \(\tau<T_c(x)\le2/35\), and \(\delta_s+T_c\le5/56<1\). Equations (7)--(8) give
\[
G(x,\tau,\delta)>G(x,\tau,\delta_s)
\ge\min\{G(x,0,\delta_s),G(x,T_c(x),\delta_s)\}.
\]
The two full one-variable certificates are
\[
G(x,0,\delta_s)/x>0,\qquad G(x,T_c(x),\delta_s)/x>0
\quad(0\le x\le1/6). \tag{11}
\]
At zero the canceled expressions are interpreted by continuous extension; actual \(x>0\) permits cancellation. Numerator degrees are four and fifteen, with five and sixteen strictly positive rational Bernstein coefficients. Their positive denominators are
\[
(x+1)(81x^2-70)(81x^2+70x-140),
\]
\[
(x-1)(x+1)(x^2+1)^2(3x^2-10)(3x^2-1)^2
(27x^2-7)(81x^2+70x-140).
\]
On the full interval the first has two negative factors, the second four, and all squared factors are nonzero. Therefore \(G>0\), contradicting (5).

### 4. Intermediate \(x\): a fixed \(\delta\) bound and concavity

Take \(\delta_c=2/35\). For \(1/6\le x\le1/4\), the actual \(\tau<T_c(x)\le2/15\) gives \(\delta_c+T_c\le4/21<1\). For \(1/4\le x\le3/4\), use \(\tau<1/6\), giving \(\delta_c+\tau<47/210<1\). The three complete certificates are
\[
G(x,0,\delta_c)>0\quad(1/6\le x\le3/4),
\]
\[
G(x,T_c(x),\delta_c)>0\quad(1/6\le x\le1/4),
\]
\[
G(x,1/6,\delta_c)>0\quad(1/4\le x\le3/4). \tag{12}
\]
Their numerator degrees are two, thirteen, three, with three, fourteen, four strictly positive rational coefficients. The positive denominators are, respectively,
\[
-33(x+1)(35x-68),
\]
\[
-(x-1)(x+1)(35x-68)(x^2+1)^2(3x^2-1)^2(103x^2-33),
\]
\[
199675(x-1)(x+1)(35x-68).
\]
The second is used only at \(x\le1/4\), where \(103x^2-33<0\) and \(3x^2-1\ne0\). Each other factor has the displayed fixed sign. Since \(\delta\le\delta_c\), (7) gives \(G(x,\tau,\delta)\ge G(x,\tau,\delta_c)\); (8) and the positive endpoint values make the entire actual \(\tau\) interval positive. Thus all \(1/6\le x\le3/4\) are excluded, including common endpoints.

### 5. Large \(x\): the same \(F\) forces too long a left reach

For \(3/4\le x<1\), the decreasing sine cap gives \(\tau<T_s(x)\le1/24\). Equation (4) and \(\delta\le2/35\) give \(\Sigma>674/757\). Since \(S_2<g(x)\le1/7\), \(S_1>3961/5299\). R58's actual left-reach bound then gives
\[
l>j(S_1)>3961/4630. \tag{13}
\]
Yet the negative-rotation \((s,c)\) width on \(L_C,U_C\) implies
\[
l<\frac{\delta+\tau}{\lambda(\eta)}
=\eta+\frac\tau{\lambda(\eta)}
<f(\eta):=\eta+\frac{1-\eta^2}{48\eta}.
\]
On the closed interval \([1/24,1/6]\), \(f''=1/(24\eta^3)>0\), so its maximum is at an endpoint. Exactly,
\[
f(1/24)=623/1152,\quad f(1/6)=83/288<623/1152<3961/4630. \tag{14}
\]
This contradicts (13). The lower bound \(\eta>1/24\) from R52 is essential; no extension toward zero is made. All \(x\) ranges are now excluded, closing the remaining negative rotation and hence the entire class \(Q_U\in W\). Together with the preceding reductions, two mechanisms remain for R60--R64.

<a id="technical-part-I"></a>
# Technical Part I. Remaining rotations and final contacts

Modules: [R60](#R60), [R61](#R61), [R62](#R62), [R63](#R63), [R64](#R64).

<a id="R60"></a>
## R60. Excluding every negative rotation in the two remaining mechanisms

**Scope.** The target is \([-\mu,\mu]^2\), \(\mu>1\), with the fixed corner roles \(V_1,V_2,V_4,W\), unique origin host \(C\) containing no outer midpoint, and bottom-midpoint tile \(F\subset\{y<0\}\). R59 excludes \(Q_U\in W\), so both remaining mechanisms have direct \(Q_U\in C\). The original \(C,F\) never move. Use \(\eta\) for \(C\)'s half-angle and \(\lambda(t)=2t/(1-t^2)\).

### 1. Actual inputs shared by the two mechanisms

Actual LEFT geometry gives \(0<z<4/15\), \(z<a<1\), \(a+2z<1\), \(0<S_4<g(z)\), \(L_1>2-S_4>2-g(z)\), \(L_1\le b(a)\), \(L_1\le1/s_a\). Put \(\mathcal F(a,z)=b(a)-\lambda(a)(2-g(z))\), \(\Delta_z=b(z)-1\). Then \(0\le S_1<\mathcal F\), and \(\mathcal F\) strictly decreases in \(a,z\). Also
\[
l>1-a,\quad u>1-z,\quad0<r<1,\quad\Sigma>2-\sqrt2>7/12. \tag{1}
\]
Both mechanisms share the weaker actual bound
\[
S_2<q(r+\Delta_z)\quad\text{only after }r+\Delta_z<1\text{ is proved}. \tag{2}
\]
Double-direct contact gives the stronger \(S_2<q(r)\). For a right bridge, both original TOP and horizontal chords of \(W\) are nonempty; their correct parallel-chord budget gives bridge length \(H<\Delta_z\), and actual handoff gives (2), as in R49--R51. No shared origin is assigned to the floating chord.

The actual \(D_C=(0,-d)\) belongs to the same \(F\), without assuming \(Q_U\in W\): \(W\), containing the upper-right corner, misses the negative vertical axis by diameter; the actual long-chord triangle argument puts \(V_1\subset\{x<0\}\), \(V_2\subset\{x>0\}\), \(V_4\subset\{y>0\}\). Thus beyond the actual lower endpoint of \(C\), only \(F\) covers that axis, and closedness gives membership. The complete bottom endpoints are also in this \(F\). If an actual chord bound gives \(d<D<1\), their triangle yields
\[
(2\mu-\Sigma)(\mu-d)\le1,\qquad
\Sigma>2-\frac1{1-D}. \tag{3}
\]
The denominator and strict \(\mu>1\) comparison are those explicitly proved in R59; the membership premise has just been checked independently here.

### 2. Three common negative-rotation constraints

Write \(c=(1-\eta^2)/(1+\eta^2)\), \(s=2\eta/(1+\eta^2)\). R43 and R51 already exclude \(\eta\le1/8\) in the two respective mechanisms. It remains that
\[
1/8<\eta\le\sqrt2-1<5/12. \tag{4}
\]
Set \(K=\lambda(\eta)\), \(\delta=b(\eta)-1\). Negative normals applied to \(L_C,U_C\) and \(R_C,U_C\) give \(sl+cu\le1\), \(cr+su\le1\), hence
\[
a>A(\eta,z):=1-\eta-z/K,\qquad r<g(\eta)+Kz. \tag{5}
\]
The actual \(R_C\) exists even without direct \(Q_R\) contact. R42's actual point is
\[
P_1=(-1+X,e),\quad X=\frac{b(a)+S_4-2}{\lambda(a)-\lambda(z)},
\quad e=1-S_4-\lambda(z)X,\quad0<e<5/12.
\]
The first negative normal on \(P_1,R_C\) gives \(r\le\delta+X-Ke\). Its derivative in \(S_4\) is \(K+(1+K\lambda(z))/(\lambda(a)-\lambda(z))>0\). Thus
\[
r<\delta+X_G-Ke_G, \tag{6}
\]
\[
X_G=\frac{(1-z)[a^2(1+2z)-z]}{(a-z)(1+az)},\quad
e_G=\frac{2az(1-a-z)}{(a-z)(1+az)}. \tag{7}
\]
Actual \(a+z<1\) gives \(e_G>0\), and \(e\) decreasing in \(S_4\) gives \(e_G<e<5/12\). Positivity of \(X_G\) uses actual \(b(a)+S_4>2\), \(g(z)>S_4\).

### 3. Larger \(z\): a left-seam budget for every negative angle

For \(3/20\le z<4/15\), actual geometry forces
\[
1/3<a<1/2. \tag{8}
\]
If \(a\le1/3\), then \(L_1\le5/4<29/23\le2-g(z)\). If \(a\ge1/2\), monotonicity and \(\mathcal F(1/2,3/20)=-1/69\) contradict \(\mathcal F>S_1\ge0\).

Let \(E_*=5/12\). For actual \(0\le\eta\le\sqrt2-1\), \(0<e_G<E_*\),
\[
[\delta(E_*)-\lambda(E_*)e_G]-[\delta(\eta)-\lambda(\eta)e_G]
=\frac{2(E_*-\eta)[E_*+\eta-e_G(1+E_*\eta)]}
{(1-E_*^2)(1-\eta^2)}>0. \tag{9}
\]
The bracket is at least \(\eta(1-E_*^2)\), with strictness from \(e_G<E_*\), \(E_*>\eta\). Hence
\[
r+\Delta_z<M_L:=50/119+X_G-(120/119)e_G+\Delta_z.
\]
On \([1/3,1/2]\times[3/20,4/15]\), the exact certificate proves
\[
7/12-\mathcal F(a,z)-q(M_L)>0. \tag{10}
\]
Numerator and denominator each have degree \((4,5)\), with 30 strictly positive rational Bernstein coefficients each and complete inverse reconstruction. The selected positive denominator \(D_L\) satisfies
\[
\frac{D_L}{2-M_L}=1428(a-z)(1-a^2)(1-z)(1+z)^2(1+az)>0. \tag{11}
\]
Thus \(2-M_L>0\). In the actual domain \(\mathcal F>0\), (10) implies \(q(M_L)<7/12\), hence \(M_L<14/19<1\). Only now is (2) used, giving \(\Sigma<7/12\), a contradiction.

### 4. Larger \(\eta\), small \(z\): the two endpoint projections suffice

For \(3/10\le\eta\le\sqrt2-1\), \(0<z\le3/20\), use the slightly larger full rectangle
\[
(\eta,z)\in[3/10,5/12]\times[0,3/20]. \tag{12}
\]
Set \(A=1-\eta-z/\lambda(\eta)\), \(M_A=g(\eta)+\lambda(\eta)z+\Delta_z\). Then \(427/1200\le A<1\), and (5) plus monotonicity gives \(S_1<\mathcal F(A,z)\). Throughout the actual ranges of this and Section 6,
\[
M_A\le7/9+(120/119)(3/20)+18/391<1. \tag{13}
\]
Thus (2) is legal. The source proves on (12)
\[
7/12-\mathcal F(A,z)-q(M_A)>0 \tag{14}
\]
with numerator and denominator degree \((6,6)\), 49 positive rational coefficients each. It contradicts (1). Together with Section 3 this excludes all \(\eta\ge3/10\).

### 5. Smaller \(\eta\), intermediate \(z\): separate directional bounds

For \(1/8<\eta\le3/10\), \(1/10\le z\le3/20\), LEFT forces
\[
2/7<a<3/5. \tag{15}
\]
The lower bound follows from \(L_1>13/11>b(2/7)=53/45\); the upper follows from \(\mathcal F(3/5,1/10)=-1/11\). Since \(\delta\le18/91\), \(K\ge16/63\), \(e_G>0\),
\[
r+\Delta_z<M_M:=18/91+X_G-(16/63)e_G+\Delta_z.
\]
On \([2/7,3/5]\times[1/10,3/20]\), the source proves
\[
7/12-\mathcal F(a,z)-q(M_M)>0, \tag{16}
\]
with numerator and denominator degree \((4,5)\), 30 positive coefficients each. Its selected positive denominator obeys
\[
\frac{D_M}{2-M_M}=9828(a-z)(1-a^2)(1-z)(1+z)^2(1+az)>0. \tag{17}
\]
As in Section 3, first obtain \(M_M<14/19<1\), then use (2) to contradict \(\Sigma>7/12\). The argument separately controls \(\delta,K\); it does not replace the true premise \(e_G<5/12\) in (9) by the unproved \(e_G<3/10\).

### 6. Smaller \(\eta\), small \(z\): the same-\(F\) area closes the remainder

For \(1/8<\eta\le3/10\), \(0<z\le1/10\), use the same \(A,M_A\). Now \(49/160\le A<1\), and (13) again ensures (2). The actual vertical chord gives \(d<\delta+z\le18/91+1/10<1\). By the independently checked original-\(F\) membership in Section 1,
\[
\Sigma>H_F(\eta,z):=2-\frac1{1-\delta-z}. \tag{18}
\]
On \([1/8,3/10]\times[0,1/10]\), the source proves
\[
H_F(\eta,z)-\mathcal F(A,z)-q(M_A)>0 \tag{19}
\]
with numerator and denominator degree \((8,7)\), 72 positive coefficients each. It contradicts (18) and the short-leg bounds. All remaining \(\eta,z\) ranges have been covered, excluding every negative rotation in both remaining mechanisms.

<a id="R61"></a>
## R61. An asymmetric triangle in the same \(F\) reduces the positive-rotation remainder

**Scope.** Retain R60's actual roles, original \(C,F\), and \(\mu>1\). R59 excludes \(Q_U\in W\), and R60 excludes negative rotation. Thus \(C\) has normals \((c,s),(-s,c)\), \(c\ge s>0\), and
\(1/8<\eta=\tan(\theta_C/2)\le\sqrt2-1<5/12\). Both remaining mechanisms directly contain \(Q_U\), so \(u>1-z\). Only double-direct contact supplies \(Q_R\in C\); this module uses the actual \(R_C\) throughout and never borrows an upper-right \(T_R\) absent from a right bridge.

### 1. Actual premises and common budgets

Use \(b,\lambda,g,q\) as in R60, \(K=\lambda(\eta)\), \(\delta=b(\eta)-1\). LEFT gives \(0<z<4/15\), \(z<a<1\), \(a+2z<1\), \(0<S_4<g(z)\), and
\[
L_1>2-S_4>2-g(z),\quad L_1\le b(a),\quad
0\le S_1<\mathcal F(a,z):=b(a)-\lambda(a)(2-g(z)). \tag{1}
\]
The function decreases strictly in \(a,z\), \(l>1-a\), and \(\Sigma>2-\sqrt2>7/12\). The two mechanisms share
\[
S_2<q(r+\Delta_z),\qquad\Delta_z=b(z)-1, \tag{2}
\]
used only after proving \(r+\Delta_z<1\). The right-bridge version comes from the original nonempty TOP/horizontal chords and actual handoff, not a shared-origin rule. The same original \(F\) contains the complete bottom endpoints and \(D_C\), by R60's independent sign and diameter argument. The actual chord gives \(d<\delta+z<41/60<1\). Shortening inside this same \(F\), after translating its bottom line to height zero, gives the actual contained points
\[
(-(1-S_1),0),\quad(1-S_2,0),\quad(0,1-d). \tag{3}
\]
No target rescaling or assignment \(\mu=1\) is made.

### 2. An asymmetric necessary triangle condition

**Lemma.** If a unit square contains \((-p,0),(q_0,0),(0,t)\), with \(p,q_0,t>0\) and \(L=p+q_0>1\), then
\[
(p+t)^2(L^2-1)\le L^2. \tag{4}
\]
Choose its normals modulo \(90^\circ\) as \((c_F,s_F),(-s_F,c_F)\), \(c_F,s_F\ge0\), without imposing \(c_F\ge s_F\). The bottom endpoints give \(Lc_F,Ls_F\le1\). Thus both components are at least \(\sqrt{1-1/L^2}\). The first-normal difference from the left endpoint to the top gives \(pc_F+ts_F\le1\), hence \((p+t)\sqrt{1-1/L^2}\le1\). Squaring nonnegative quantities proves (4). The left length \(p\) is retained; neither \(p=L/2\) nor \(p\ge q_0\) is assumed.

If actual \(S_1<F_0,S_2<q(M),d<D_0\), and \(p_0=1-F_0,q_0=1-q(M),t_0=1-D_0\) are positive, convexity shortens each of the three segments in (3) toward the origin. Their new endpoints still belong to that same \(F\). If \(L_0=p_0+q_0>1\), (4) requires
\[
G(F_0,M,D_0):=(2-F_0-D_0)^2[(2-F_0-q(M))^2-1]
-(2-F_0-q(M))^2\le0. \tag{5}
\]
This is not a newly placed independent triangle.

### 3. A universal positive-rotation lower-reach cap from \(P_1,D_C\)

R42 gives the actual \(P_1=(-1+X,e)\), with
\[
X=\frac{b(a)+S_4-2}{\lambda(a)-\lambda(z)},\quad
e=1-S_4-\lambda(z)X,\quad0<e<5/12.
\]
At \(S_4=g(z)\), define
\[
X_G=\frac{(1-z)[a^2(1+2z)-z]}{(a-z)(1+az)},\quad
e_G=\frac{2az(1-a-z)}{(a-z)(1+az)}. \tag{6}
\]
Actual \(0<X_G<a<1\), \(0<e_G<e<5/12\). The second normal on \(P_1,D_C\) gives \(s(1-X)+c(e+d)\le1\), hence \(d\le b(\eta)-K(1-X)-e\). Its derivative in \(S_4\) is \((\lambda(a)+K)/(\lambda(a)-\lambda(z))>0\). Thus
\[
d<D_G(\eta,a,z):=g(\eta)+KX_G-e_G. \tag{7}
\]
This requires no \(a<g(\eta)\). By contrast, the first-normal \(P_1,R_C\) bound \(r\le\delta+X+Ke\) has derivative \((1-K\lambda(a))/(\lambda(a)-\lambda(z))\); only when \(a<g(\eta)\) may one conclude
\[
r<R_P:=\delta+X_G+Ke_G. \tag{8}
\]
The actual axis pairs independently give
\[
a>A:=K(1-\eta-z),\qquad r<R_T:=\eta+z/K. \tag{9}
\]
No negative-rotation expression with \(-Ke_G\) is used.

### 4. Larger \(\eta\), small \(z\)

On \(\eta\in[3/10,5/12]\), \(z\in[0,1/10]\), \(0<A<1\), with positive lower bound \(\lambda(3/10)(1-5/12-1/10)\) and upper bound \(\lambda(5/12)(1-3/10)<1\). Also
\[
M_A=R_T+\Delta_z\le5/12+(1/10)/\lambda(3/10)+\Delta_{1/10}<1.
\]
Thus (2) is legal, and the actual short legs give \(\Sigma<\mathcal F(A,z)+q(M_A)\). The source proves
\[
7/12-\mathcal F(A,z)-q(M_A)>0 \tag{10}
\]
on this full rectangle. Numerator and denominator each have degree \((6,6)\) and 49 strictly positive rational Bernstein coefficients. This excludes \(\eta\ge3/10,z\le1/10\).

### 5. Larger \(z\): a common corner range

For \(1/5\le z<4/15\), actual geometry forces
\[
3/8<a<5/11. \tag{11}
\]
The lower bound follows from \(L_1>4/3>b(3/8)\), margin \(1/165\); the upper from \(\mathcal F(5/11,1/5)=-1/144\) and monotonicity. On \([3/8,5/11]\times[1/5,4/15]\),
\[
a-X_G=\frac{z(1-a^2)(1-a-z)}{(a-z)(1+az)}>0.
\]
Differentiating \(X_G=(b(a)+g(z)-2)/(\lambda(a)-\lambda(z))\) gives \(X_{G,a}>0\), since \(b'/\lambda'=2a/(1+a^2)>a>X_G\), and \(X_{G,z}<0\), since \(-g'/\lambda'=(1-z)^2/(1+z^2)>5/11\ge a>X_G\). Consequently
\[
X_G\le X_G(5/11,1/5)=9/35. \tag{12}
\]
The identity \(e_G=1-g(z)-\lambda(z)X_G\) gives decrease in \(a\) and increase in \(z\); also \(\mathcal F\le9/55\).

For \(1/8<\eta\le3/10\), (11) gives \(a<5/11<g(3/10)\le g(\eta)\), permitting (8). Set
\[
M(\eta)=\frac{2R_P(\eta)+R_T(\eta)}3+\Delta_z. \tag{13}
\]
Actual \(r+\Delta_z<M(\eta)\). At fixed actual \(a,z\), this is strictly convex: \(\delta''=4(1+3\eta^2)/(1-\eta^2)^3>0\), \(K''=4\eta(3+\eta^2)/(1-\eta^2)^3>0\), \(R_{T,\eta\eta}=z/\eta^3>0\), and \(e_G>0\). Thus it is bounded above by its larger endpoint at \(1/8,3/10\). Both endpoint values are below one using (12), \(e_G<5/12,z\le4/15\), with exact positive rational margins in the source's constant checks. On the full rectangle (11), certify
\[
7/12-\mathcal F(a,z)-q(M(1/8))>0,\quad
7/12-\mathcal F(a,z)-q(M(3/10))>0. \tag{14}
\]
Each numerator and denominator has degree \((4,6)\), totaling 140 positive rational coefficients. The larger endpoint yields the contradiction \(\Sigma<7/12\). Convexity controls the entire continuous central-angle range.

For \(3/10\le\eta\le\sqrt2-1<5/12\), at fixed \(a,z\),
\[
\partial_\eta^2D_G=\frac{4[1+3\eta^2-(1-X_G)\eta(3+\eta^2)]}{(1-\eta^2)^3}>0,
\]
because its bracket exceeds \((1-\eta)^3\). Moreover (12) gives
\[
D_G(3/10)-D_G(5/12)\ge g(3/10)-g(5/12)
+[\lambda(3/10)-\lambda(5/12)]9/35=400/10829>0.
\]
Hence \(d<D_0:=D_G(3/10,a,z)\). This bound increases in \(a\) and decreases in \(z\), so \(D_0\le3683/7644<1\). If \(D_0\le0\), actual \(d>0\) already contradicts it; otherwise \(1-D_0\) is a legal positive shortened height in \(F\).

Convexity of \(R_T\) gives \(r+\Delta_z<\max(M_-,M_+)\), where
\[
M_-=3/10+z/\lambda(3/10)+\Delta_z,\quad
M_+=5/12+z/\lambda(5/12)+\Delta_z.
\]
Both are below \(7/8<1\), as checked at \(z\le4/15\), so (2) is legal. For either, \(q(M)<7/9\) and \(\mathcal F\le9/55\), giving \(L_0=2-\mathcal F-q(M)>1\); all three shortened lengths in (5) are positive. But on the whole rectangle (11), the source proves
\[
G(\mathcal F,M_-,D_0)>0,\qquad G(\mathcal F,M_+,D_0)>0. \tag{15}
\]
Each numerator has degree \((12,14)\) and 195 positive rational coefficients. Writing \(T=2-\mathcal F-D_0=t_n/t_d\), \(L=2-\mathcal F-q(M)=l_n/l_d\), the exact numerator is \(t_n^2(l_n^2-l_d^2)-l_n^2t_d^2\), with denominator \(t_d^2l_d^2\). Here \(t_d=91(a-z)(1-a^2)(1+z)(1+az)>0\); \(l_d\) equals respectively \(-60\) or \(-120\) times \((1-a^2)(1-z)(1+z)^2(2-M)\), hence is nonzero. Denominator positivity comes from explicit squares and the actual branch, not extra positive-coefficient polynomials. Choosing the larger \(M\) contradicts the necessary (5). Both central-angle ranges together exclude every \(z\ge1/5\) in both mechanisms.

### 6. A hand proof excludes \(a\ge g(\eta)\) for \(\eta\le1/3\)

Suppose \(1/8<\eta\le1/3\), \(a\ge g(\eta)\). Positivity and monotonicity of \(\mathcal F\) imply
\[
0<\mathcal F(g(\eta),z)=\eta-\frac{2z}{K(1+z)}.
\]
Thus \(z<Y(\eta)=\eta^2/(1-2\eta^2)\le1/7\). The functions \(\eta,Y\) increase, and
\[
\frac d{d\eta}\frac YK=\frac{2\eta^4-\eta^2+1}{2(1-2\eta^2)^2}>0.
\]
Therefore \(0<R_T+\Delta_z<1/3+4/21+1/24=95/168<1\), so (2) applies. At fixed \(\eta\), the function
\(f(z)=\mathcal F(g(\eta),z)+q(R_T+\Delta_z)\) is strictly convex: the first term has second derivative \(4/[K(1+z)^3]>0\), and the second is an increasing convex \(q\) composed with an increasing convex argument below one. At zero, \(f=\eta+q(\eta)\le8/15<7/12\); at \(Y\), the first term is zero and \(f\le q(95/168)<7/12\). Convexity bounds the entire interval by these endpoints, contradicting \(\Sigma>7/12\). Thus remaining \(\eta\le1/3\) necessarily has \(a<g(\eta)\); the slope premise in (8) has been proved by excluding its alternative.

<a id="R62"></a>
## R62. Excluding all small \(z\) and confining the common remainder to an open strip

**Scope.** Retain R61's actual positive-rotation tile \(C\), with normals \((c,s),(-s,c)\), \(\eta>1/8\), the unchanged original \(F\), and direct \(Q_U\) in both remaining mechanisms. Thus \(u>1-z\). All axial endpoints below are actual points of \(C\). Use \(b,\lambda,g,q\), \(\delta(\eta)=b(\eta)-1\), \(\Delta_z=b(z)-1\) as before.

### 1. Actual geometry and the range still to be treated

LEFT gives
\[
0\le S_1<\mathcal F(a,z)=b(a)-\lambda(a)(2-g(z)),\qquad z<a<1, \tag{1}
\]
with \(\mathcal F\) decreasing in both variables. The actual positive-rotation endpoint widths give
\[
a>A(\eta,z):=\lambda(\eta)(1-\eta-z),\quad
r<R_T(\eta,z):=\eta+z/\lambda(\eta). \tag{2}
\]
Both mechanisms have \(S_2<q(r+\Delta_z)\), used only after its argument is below one. The same original \(F\) contains the actual bottom endpoints and \(D_C\), while the same \(C\) gives \(d<\delta+z\). In the present domain \(\delta+z<1\); the same-tile triangle therefore requires
\[
\Sigma>H_F(\eta,z):=2-\frac1{1-\delta(\eta)-z}. \tag{3}
\]
The strict \(\mu>1\) passage is inside the original \(F\), not a target rescaling. R61 already excludes \(\eta\ge3/10,z\le1/10\). It remains to treat
\[
1/8<\eta\le3/10,\qquad0<z\le1/10. \tag{4}
\]
On the entire rectangle \(1-\delta-z>0\), and the uniform bound
\[
R_T+\Delta_z\le3/10+(1/10)/\lambda(1/8)+\Delta_{1/10}<1 \tag{5}
\]
makes the right short-leg comparison legal. No monotonicity of \(R_T\) in \(\eta\) is needed.

### 2. Eliminating \(\eta\) with the actual left and upper endpoints

Differentiation gives
\[
A_\eta=\frac{2[(1-\eta)^2-z(1+\eta^2)]}{(1-\eta^2)^2}>0,
\]
since the bracket is at least \((7/10)^2-(1/10)(1+(3/10)^2)=381/1000>0\). Hence
\[
a>A(1/8,1/10)=62/315. \tag{6}
\]
Also \(f=A/\eta=2(1-\eta-z)/(1-\eta^2)\) has derivative
\[
f_\eta=-\frac{2[(1-\eta)^2+2\eta z]}{(1-\eta^2)^2}<0.
\]
Since \(\eta\le3/10\), \(a>\eta(140-200z)/91\), and therefore
\[
\eta<H(a,z):=\frac{91a}{140-200z}. \tag{7}
\]
The denominator is at least 120. This is a necessary functional bound from actual points, not a freely chosen new angle for \(C\).

### 3. Small \(a\): seam-to-right width and the same-\(F\) area

For \(62/315<a\le7/20\), R61's algebraic endpoints are
\[
X_G=\frac{(1-z)[a^2(1+2z)-z]}{(a-z)(1+az)},\quad
e_G=\frac{2az(1-a-z)}{(a-z)(1+az)}.
\]
In the actual domain \(0<X_G<a\), \(0<e_G<5/12\). Since \(a\le7/20<g(3/10)\le g(\eta)\), the positive slope in \(S_4\) permits
\[
r<R_P(\eta):=\delta(\eta)+X_G+\lambda(\eta)e_G. \tag{8}
\]
At fixed actual \(a,z\), this increases in \(\eta\), while \(H_F\) decreases. Thus (7) gives \(r<R_P(H)\), \(H_F(\eta,z)>H_F(H,z)\), without claiming that \(H\) defines another actual tile. On
\[
(a,z)\in[62/315,7/20]\times[0,1/10], \tag{9}
\]
we have \(H\le637/2400<3/10\). In the actual domain,
\[
M_P=R_P(H)+\Delta_z
<\delta(637/2400)+7/20+\lambda(637/2400)(5/12)+\Delta_{1/10}<1. \tag{10}
\]
Also \(1-\delta(H)-z>0\). On the full rectangle (9), the source proves
\[
H_F(H,z)-\mathcal F(a,z)-q(M_P)>0. \tag{11}
\]
Numerator and denominator each have degree \((8,10)\), with 99 strictly positive rational Bernstein coefficients each. The actual inequalities give \(\Sigma<\mathcal F+q(M_P)<H_F(H,z)<H_F(\eta,z)\), contradicting (3).

### 4. Intermediate \(a\): concavity of the complete joint budget

For \(7/20\le a\le79/200\),
\[
1/8<H(a,z)\le7189/24000<3/10. \tag{12}
\]
Define
\[
\Phi(\eta,a,z)=H_F(\eta,z)-\mathcal F(a,z)
-q(R_T(\eta,z)+\Delta_z). \tag{13}
\]
Its positivity contradicts the actual short-leg and same-\(F\) bounds. The key is strict concavity of this entire function in \(\eta\):
\[
H_{F,\eta\eta}=-\frac{\delta''}{(1-\delta-z)^2}
-\frac{2(\delta')^2}{(1-\delta-z)^3}<0,
\quad R_{T,\eta\eta}=z/\eta^3\ge0.
\]
The increasing convex \(q\) composed with the convex argument below one is convex, even if \(R_{T,\eta}<0\). Thus actual \(\eta\in[1/8,H]\) gives
\[
\Phi(\eta,a,z)\ge\min\{\Phi(1/8,a,z),\Phi(H,a,z)\}. \tag{14}
\]
On the entire \([7/20,79/200]\times[0,1/10]\), certify
\[
\Phi(H,a,z)>0, \tag{15}
\]
with numerator and denominator degree \((6,9)\), 70 positive rational coefficients each. For the other endpoint, monotonicity of \(\mathcal F\) gives \(\Phi(1/8,a,z)\ge\Phi(1/8,7/20,z)\). At fixed \(\eta,a\), \(\Phi\) is strictly concave in \(z\): \(H_F\) is concave, \(\mathcal F\) convex, and \(q(R_T+\Delta_z)\) convex. Its two \(z\) endpoint values at \(0,1/10\) are strictly positive rational numbers, independently checked in the source. Therefore the whole interval is positive, and (14) excludes this \(a\) range. In particular the proof does not infer \(R_T(\eta)<R_T(H)\) from \(\eta<H\); that inference would generally be false.

### 5. Large \(a\): four rational endpoint values and separate concavity

For \(a\ge79/200\), monotonicity gives \(\Phi(\eta,a,z)\ge\Phi(\eta,79/200,z)\). This is separately concave in \(\eta,z\); on \([1/8,3/10]\times[0,1/10]\) it is at least the smallest of the four corner values. In order \((1/8,0),(1/8,1/10),(3/10,0),(3/10,1/10)\), they are
\[
\frac{39727}{85095},\quad\frac{338285311622}{1566996353043},\quad
\frac{49603}{346239},\quad\frac{2880149942}{797749375203},
\]
all strictly positive. These are analytic bounds obtained by two concavity arguments, not angle sampling. The three \(a\) ranges cover every actual value after (6), including common boundaries. Together with R61's larger-angle small-\(z\) exclusion, this closes all \(z\le1/10\) in both mechanisms. Combined with R61's larger-\(z\) result, the common remainder lies in \(1/10<z<1/5\).

<a id="R63"></a>
## R63. Excluding the entire right bridge and leaving only positive double-direct contact

**Scope.** Retain the actual roles and unchanged original \(C,F\) of R62. The original \(C\) has positive rotation, and the common remainder satisfies
\[
1/8<\eta\le\sqrt2-1<5/12,\qquad1/10<z<1/5. \tag{1}
\]
The tile \(F\subset\{y<0\}\) owns the complete bottom gap. Both mechanisms directly contain \(Q_U\); no upper-bridge bound specific to \(Q_U\in W\) is used. In this module \(\tau\) is the smaller-axis half-angle of the original \(W\), derived afresh when it meets the horizontal line.

### 1. A uniform actual right-reach cap

Use \(b,\lambda,g,q\), \(\delta(\eta)=b(\eta)-1\), \(\Delta_z=b(z)-1\). The actual endpoints satisfy \(u>1-z,l>1-a\). LEFT gives
\[
0\le S_1<\mathcal F(a,z)=b(a)-\lambda(a)(2-g(z)),\quad L_1>2-g(z). \tag{2}
\]
The decreasing \(\mathcal F\), with \(\mathcal F(3/5,1/10)=-1/11\), forces \(a<3/5\). The horizontal chord and \(R_C,U_C\) second-normal width give
\[
r<a+\delta(\eta),\qquad r<R_T(\eta,z)=\eta+z/\lambda(\eta). \tag{3}
\]
If \(\eta\le1/3\), then \(r<3/5+1/4=17/20\). If \(\eta\ge1/3\), convexity \(R_{T,\eta\eta}=z/\eta^3>0\) and \(z<1/5\) give
\[
r<\max\{1/3+(1/5)/\lambda(1/3),,5/12+(1/5)/\lambda(5/12)\}
=\max\{3/5,123/200\}<17/20.
\]
Thus
\[
0<r<17/20<7/8,\qquad r+\Delta_z<17/20+1/12=14/15<1. \tag{4}
\]
Both mechanisms can therefore use
\[
S_2<q(r+\Delta_z). \tag{5}
\]
Double-direct contact has the stronger \(S_2<q(r)\); the right bridge uses the actual nonempty TOP/horizontal chords from R49. The same bottom chord always gives
\[
\Sigma>2-\sqrt2>7/12. \tag{6}
\]
The special upper-bridge bound \(\Sigma<1\) is not used.

### 2. Two actual horizontal intersections force a small angle for the original \(W\)

Suppose the original \(W\) meets \(y=0\), even tangentially. It also contains the upper-right target corner and hence meets TOP. Its actual top leg \(D\) satisfies
\[
D\ge2\mu-L_4\ge2\mu-b(z)>1-\Delta_z>11/12. \tag{7}
\]
No replacement is made. An axis-aligned \(W\) has vertical span one and cannot meet both lines at distance \(\mu>1\). Choose its smaller axis angle \(\beta\in(0,\pi/4]\), with \(c=\cos\beta\ge s=\sin\beta>0\) and \(\tau=\tan(\beta/2)\in(0,\sqrt2-1]\).

Let \(y_{\min},y_{\max}\) be its extreme heights; their difference is \(c+s\). Put \(\alpha=-y_{\min}\ge0\), \(\gamma=y_{\max}-\mu\ge0\). Then \(\alpha+\gamma=c+s-\mu<s\), since \(\mu>1\ge c\). Both lines lie in triangular end caps of the square, with full chord lengths \(\alpha/(cs),\gamma/(cs)\), including zero tangent chords. Its actual TOP segment is no longer than the full upper chord. Therefore
\[
D\le\frac{c+s-\mu}{cs}<\frac{c+s-1}{cs}
=\frac{1+\tau^2}{1+\tau}=1-\tau g(\tau). \tag{8}
\]
Both intersections have been verified nonempty before using this budget. Equations (7)--(8) give \(\tau g(\tau)<\Delta_z<1/12\). The function \(\tau g(\tau)\) increases on \([0,\sqrt2-1]\), with derivative \((1-2\tau-\tau^2)/(1+\tau)^2\ge0\); at \(1/8\) it equals \(7/72>1/12\). Hence
\[
0<\tau<1/8,\qquad\tau<9\Delta_z/7, \tag{9}
\]
the latter using \(g(\tau)>7/9\). No \(Q_U\) or TOP-midpoint membership is assumed.

### 3. Any actual horizontal point of \(W\) lies far left or far right

Take \(Z=(\xi,0)\in W\). Its two possible orientations relative to the target cover all rotations, with the diagonal equality excluded by (9). For positive orientation, normals \((c,s),(-s,c)\), compare \(Z\) with the actual TOP left endpoint \(P=(\mu-D,\mu)\) in the second normal:
\[
c\mu+s(\xi+D-\mu)\le1,
\]
\[
\xi\le\mu-D+\frac{1-c\mu}{s}
=\mu-D+\tau-(c/s)(\mu-1)<\Delta_z+\tau. \tag{10}
\]
The last step uses \(\mu-D\le L_4-\mu\le b(z)-\mu<\Delta_z\). For negative orientation, normals \((c,-s),(s,c)\), compare \(Z\) with the actual upper-right corner:
\[
s(\mu-\xi)+c\mu\le1,
\]
\[
\xi\ge\mu-\frac{1-c\mu}{s}
=1-\tau+(\mu-1)(1+c/s)>1-\tau>7/8. \tag{11}
\]
These are widths of actual points of the original \(W\), not intersections of infinite supports or movable bridge endpoints.

### 4. Both orientations contradict \(R_C\in W\)

If \(R_C=(r,0)\in W\), negative orientation gives \(r>7/8\), contrary to (4). Positive orientation gives \(r<\Delta_z+\tau\), and then
\[
r+\Delta_z<2\Delta_z+\tau<(23/7)\Delta_z=:M(z)<23/84<1. \tag{12}
\]
Thus (5) yields \(S_2<q(M(z))\). Keep the real LEFT long leg \(L=L_1>1\). Its short leg \((1-L\sin\theta_a)/\cos\theta_a\) has derivative \((\sin\theta_a-L)/\cos^2\theta_a<0\). The actual cap \(L\cos\theta_a\le1\) gives \(\theta_a\ge\arccos(1/L)\), hence \(S_1\le L(1-\sqrt{L^2-1})\). This decreases for \(L>1\); with \(L_1>2-g(z)=1+w(z)\), \(w(z)=2z/(1+z)\),
\[
S_1<\Phi(w(z)),\quad\Phi(w)=(1+w)(1-\sqrt{w(2+w)}). \tag{13}
\]
The actual \(L_1\le\sqrt2\) ensures the legal angle range. For \(v=\sqrt{w(2+w)}>0\), \(\Phi'=1-2v-1/v<-7/4\), because \(2v+1/v\ge2\sqrt2>11/4\). On \([1/10,1/5]\), \(w'\ge25/18\), so the derivative of \(\Phi(w(z))\) is below \(-175/72\). Also \(M\le23/84\), \(\Delta_z'\le125/144\), and
\[
\frac d{dz}q(M(z))\le\frac2{(2-23/84)^2}\frac{23}{7}\frac{125}{144}
=1610/841<175/72. \tag{14}
\]
Their sum strictly decreases. At \(z=1/10\),
\[
\Phi(2/11)=\frac{13(11-4\sqrt3)}{121}<4/9,
\qquad q(M(1/10))=23/670<1/20. \tag{15}
\]
The first comparison is equivalent to \(803<468\sqrt3\), with positive squared margin 12263 and both sides positive. Hence throughout the strip
\[
\Sigma<\Phi(w(z))+q(M(z))<4/9+1/20=89/180<7/12, \tag{16}
\]
contradicting (6). Thus the original \(W\) cannot contain the actual \(R_C\) in any current remainder.

### 5. Closing the right bridge and strengthening the double-direct remainder

A right bridge means \(Q_R\notin C\), with closed horizontal handoff from \(C\) through the original \(W\) to \(V_2\). It forces both \(R_C,Q_R\in W\), as in R49. Section 4 therefore excludes the entire remaining right bridge, without selecting either of R48's lower-right I/II combinations. Together with earlier angle, rotation, and exterior exclusions, the mechanism is closed.

Only double-direct contact remains. Write \(Q_R=(q_R,0)\), \(0<q_R\le r<17/20\). If the original \(W\) also contained \(Q_R\), negative orientation would give \(q_R>7/8\), impossible; positive orientation would give \(q_R<\Delta_z+\tau\). Since the actual corner endpoint satisfies \(q_R=\mu-U_2>1-x\), with \(S_2<g(x)\),
\[
S_2<q(q_R)<q(\Delta_z+\tau)<q(M(z)),
\]
all arguments being below one. The same LEFT calculation gives (16), again impossible. Thus in the double-direct remainder \(W\) contains neither \(R_C\) nor \(Q_R\). This does not imply that its whole horizontal chord is empty: redundant contribution inside the region already covered by \(C,V_2\) may remain. Nor does it exclude TOP-midpoint membership.

<a id="R64"></a>
## R64. Excluding all positive rotations in the middle-\(z\) double-direct form

**Scope.** This is a local theorem for the explicitly stated positive-rotation, double-direct, middle-\(z\) form. Its scalar certificates do not prove the preceding normalization or host reductions. Those premise transfers must be supplied by the earlier geometric route and the core's stepwise cover-domination and reclassification protocol. No independent global theorem is claimed here.

### 1. Complete local inputs

The target is \([-\mu,\mu]^2\), \(\mu>1\). The selected corner tiles retain their roles: \(V_1\) hosts LEFT midpoint, \(V_2\) RIGHT midpoint, \(V_4\) TOP midpoint, and \(W\) the upper-right corner. The tile \(C\) contains the origin and no outer midpoint; the original \(F\) contains BOTTOM midpoint and lies in \(y<0\). The three nonbottom outer edges have corner contact, \(C\) misses BOTTOM, and the complete bottom gap belongs to this same \(F\). The representatives of \(V_1,V_2,V_4\) are legally normalized with \(C,F\) fixed.

Assume double-direct contact: the actual \(Q_R,Q_U\) both belong to \(C\). Let \(R_C=(r,0),U_C=(0,u)\) be its actual axial endpoints. The half-angles of \(V_1,V_2,V_4,C\) are \(a,x,z,\eta\), respectively. The central normals are \((c,s),(-s,c)\), \(c\ge s\ge0\). Use \(b(t)=(1+t^2)/(1-t^2)\), \(\lambda(t)=2t/(1-t^2)\), \(g(t)=(1-t)/(1+t)\), \(q(t)=t/(2-t)\). Actual LEFT and bottom geometry give
\[
1/10<z<1/5,\quad z<a<1,\quad a+2z<1,\quad0<S_4<g(z),
\]
\[
\begin{aligned}
L_1&>2-S_4>2-g(z),\qquad L_1\le b(a),\\
0\le S_1&<\mathcal F(a,z):=b(a)-\lambda(a)(2-g(z)),\\
\Sigma&>7/12.
\end{aligned} \tag{1}
\]
The function \(\mathcal F\) decreases strictly in both variables. Since \(b(2/7)<13/11<2-g(z)\), and \(\mathcal F(3/5,1/10)=-1/11\),
\[
2/7<a<3/5. \tag{2}
\]
Double-direct contact gives \(u>1-z,r>1-x\), \(S_2<g(x)\); whenever \(0<r<1\),
\[
S_2<q(r). \tag{3}
\]
Every argument below independently proves its chosen upper bound on \(r\) is below one. No right-bridge \(\Delta_z\) loss is paid here; that mechanism lacks (3) and must first be excluded by R63.

R40/R42's actual seam and convexity argument give the point of the same original \(C\)
\[
P_1=(-1+X,e),\quad X=\frac{b(a)+S_4-2}{\lambda(a)-\lambda(z)},
\quad e=1-S_4-\lambda(z)X. \tag{4}
\]
At \(S_4=g(z)\), set
\[
X_G=\frac{(1-z)[a^2(1+2z)-z]}{(a-z)(1+az)},\quad
e_G=\frac{2az(1-a-z)}{(a-z)(1+az)}. \tag{5}
\]
Actual \(0<X_G<a\), \(0<e_G<5/12\). The point \(P_1\) is genuinely in the original \(C\), not merely a formal \(\mu=1\) substitution. The source's reinspection of R40/R42 concerns these local memberships; the global premise-transfer review remains separate.

### 2. Two positive-rotation projections and endpoint rules

Write \(K=\lambda(\eta)\), \(\delta=b(\eta)-1\). The first normal on \(P_1,R_C\) gives \(r\le\delta+X+Ke\). Its derivative in \(S_4\) is \((1-K\lambda(a))/(\lambda(a)-\lambda(z))\), positive when \(a<g(\eta)\). Thus on that branch
\[
r<R_P(\eta):=\delta(\eta)+X_G+\lambda(\eta)e_G. \tag{6}
\]
This is valid at \(\eta=0\), where the derivative is \(1/(\lambda(a)-\lambda(z))>0\). For \(\eta>0\), the first-normal width of \(P_1,U_C\), retaining \(u>1-z\), gives
\[
S_4+(\lambda(z)-1/K)X<\eta+z.
\]
If \(a<g(\eta)\), its left side decreases in \(S_4\), so \(S_4<g(z)\) forces
\[
D_\eta(a,z):=g(z)+(\lambda(z)-1/\lambda(\eta))X_G-\eta-z<0. \tag{7}
\]
At fixed actual \(a,z\), \(D_{\eta\eta}=-X_G/\eta^3<0\), so it is concave in \(\eta\). The auxiliary polynomial
\[
P_\eta(a,z):=D_\eta(a,z)(a-z)(1+az) \tag{8}
\]
is quadratic in \(a\); the factor is positive at actual \(a>z\). The arguments below use concavity in \(a\) at auxiliary angle endpoints, then concavity in \(\eta\) for actual points. They do not assume \(X_G>0\) at the auxiliary \(a=0\). Finally the actual \(R_C,U_C\) second-normal width gives, for \(\eta>0\),
\[
r<R_T(\eta,z):=\eta+z/\lambda(\eta),\qquad R_{T,\eta\eta}=z/\eta^3>0. \tag{9}
\]

### 3. Small angles, including the axial endpoint

For \(0\le\eta\le1/4\), (2) gives \(a<3/5=g(1/4)\le g(\eta)\), so (6) is valid. Since \(R_P\) increases with \(\eta\) when actual \(e_G>0\),
\[
r<R_P(1/4)=2/15+X_G+(8/15)e_G=:M.
\]
The bound \(M<2/15+3/5+(8/15)(5/12)=43/45<1\) makes (3) legal. On the full rectangle \([2/7,3/5]\times[1/10,1/5]\), the source proves
\[
7/12-\mathcal F(a,z)-q(M)>0. \tag{10}
\]
Numerator and denominator each have degree \((4,3)\), totaling 40 strictly positive rational Bernstein coefficients. Hence \(\Sigma<7/12\), contradicting (1). No division by \(\eta\) occurs, so \(\eta=0\) is included.

### 4. Middle angles

For \(1/4\le\eta\le1/3\), first suppose \(a\le2/5\). Then \(a<g(1/3)=1/2\le g(\eta)\), so (7) applies. At each auxiliary angle \(\eta=1/4,1/3\), on the complete \(z\in[1/10,1/5]\), the source certifies
\[
-[a^2]P_\eta>0,\qquad P_\eta(0,z)>0,\qquad P_\eta(2/5,z)>0. \tag{11}
\]
Thus \(P_\eta\) is strictly concave in \(a\) and positive on \([0,2/5]\). At actual \(a>z\), both endpoint values of \(D_\eta\) are positive. Its actual \(\eta\) concavity gives positivity throughout the interval, contradicting (7). Therefore \(a>2/5\).

Now \(S_1<\mathcal F(2/5,z)\), and \(R_T\le1/3+(1/5)/\lambda(1/4)<1\), making (3) legal. The function \(\mathcal F(2/5,z)+q(R_T(\eta,z))\) is separately convex in \(\eta,z\): \(R_T\) is convex in \(\eta\), \(q\) increasing convex, while in \(z\), \(R_T\) is linear and \(\mathcal F_{zz}=4\lambda(2/5)/(1+z)^3>0\). Its maximum is controlled by four corner values. The four exact positive margins below \(7/12\) are
\[
369/7700,\qquad7/396,\qquad167/7084,\qquad11/252. \tag{12}
\]
Therefore \(\Sigma<7/12\) throughout the middle-angle rectangle. These finite values bound the full domain by separate convexity, not by sampling.

### 5. Large angles

For \(1/3\le\eta\le\sqrt2-1\), use the strict rational outer cap
\[
E_*=29/70>\sqrt2-1,\qquad B(z)=1/2-3z/4+z^2.
\]
The cap follows from \((99/70)^2-2=1/4900>0\). For \(\eta\ge1/3,z\le1/5\), \(R_{T,\eta}=1-(z/2)(1+\eta^{-2})\ge0\); hence
\[
r<R(z):=E_*+z/\lambda(E_*)=29/70+(4059/4060)z<1. \tag{13}
\]
No such monotonicity is imported into the small-angle range. If \(a\ge g(\eta)\), then \(a\ge g(E_*)=41/99\). The full-interval certificate
\[
7/12-\mathcal F(41/99,z)-q(R(z))>0 \tag{14}
\]
contradicts (1).

Otherwise \(a<g(\eta)\), so (7) applies. At both auxiliary endpoints \(\eta=1/3,E_*\), the source certifies on the full \(z\) interval
\[
-[a^2]P_\eta>0,\qquad P_\eta(0,z)>0,\qquad P_\eta(B(z),z)>0. \tag{15}
\]
Also \(B(z)>z\), \(39/100\le B(z)\le87/200<1\). If actual \(a\le B(z)\), concavity first in \(a\), then in actual \(\eta\), gives \(D_\eta>0\), contradicting (7). Thus \(a>B(z)\). The remaining full-interval certificate is
\[
7/12-\mathcal F(B(z),z)-q(R(z))>0. \tag{16}
\]
Monotonicity of \(\mathcal F\), (3), and (13) again imply \(\Sigma<7/12\). These two \(a\) branches exhaust the large-angle domain, without invoking the historical specialized R41/R42 angle exclusions.

### 6. Arithmetic records and the precise local conclusion

There are fourteen distinct rational targets, twenty-eight complete numerator/denominator polynomials, and 114 strictly positive rational Bernstein coefficients. The middle and large ranges share the \(\eta=1/3\) concavity and \(a=0\) targets; those two are recorded and counted once. Each full numerator and denominator is reconstructed exactly from its coefficients and compared with an independently explicit coordinate expression. The source also checks twelve support formulas, eleven positive rational constants, four middle-angle endpoint values, and forty geometric-premise items. These are not all claimed as newly discovered, and no R63 or older polynomial statistics are added. No UNSAT result, layout search, fixed-point covering search, angle sampling, or interval tree is used.

The three closed angle ranges \([0,1/4]\), \([1/4,1/3]\), \([1/3,\sqrt2-1]\) cover every positive rotation, including their boundaries. Consequently the middle-\(z\), double-direct standard form stated in Section 1 is impossible. Its implication for an arbitrary covering depends on the earlier geometric reductions and their exact premise transfers, not on retroactively extending these scalar checks.

<a id="technical-index"></a>
# Module and evidence index

The module labels locate both the English derivations above and their frozen
arithmetic evidence. The source repository is
[ZhouNingyu327/S6-eq-2](https://github.com/ZhouNingyu327/S6-eq-2), with the
editorial source pinned to commit 99408eed4ddf3e42bef727e64fae22971e8bc768.
The later publication commit for the illustrated English core is recorded
separately in the delivery record.

## Part A: Foundation and the two-centre cases

- [R2. Fundamental grid and chord budgets](#R2) - source/evidence family `S6_round2_verification.zip`.
- [R3. Cyclic midpoint hosts and the remaining G5 representatives](#R3) - source/evidence family `S6_round3_verification.zip`.
- [R4. Central boundary contacts and reductions of the one-midpoint case](#R4) - source/evidence family `S6_round4_verification.zip`.
- [R5. Excluding the near representative with three joined outer edges](#R5) - source/evidence family `S6_round5_verification.zip`.
- [R6. Exclusion of every near G5 one-midpoint representative](#R6) - source/evidence family `S6_round6_verification.zip`.
- [R7. Boundary exclusion and redundancy in the far G5 representative](#R7) - source/evidence family `S6_round7_verification.zip`.
- [R8. The final far-case inequality and exclusion of G5](#R8) - source/evidence family `S6_round8_verification.zip`.

## Part B: No owned midpoint and centre-owned midpoint cases

- [R9. Exclusion of the G1 three-join configuration](#R9) - source/evidence family `S6_round9_verification.zip`.
- [R10C. Nonempty-chord correction for opposite G1 gaps](#R10C) - source/evidence family `S6_round65_verification.zip / support`.
- [R10. Completion of the G1 exclusion](#R10) - source/evidence family `S6_round10_verification.zip`.
- [R11. Interior-point obstruction and reduction of a far G2 representative](#R11) - source/evidence family `S6_round11_verification.zip`.
- [R12. The noncentral non-corner tile must contain an outer midpoint](#R12) - source/evidence family `S6_round12_verification.zip`.

## Part C: Adjacent owned midpoints

- [R20. Opposite and adjacent midpoint representatives in G3 and G4](#R20) - source/evidence family `S6_round20_verification.zip`.
- [R20A. Excluding a duplicated left midpoint in the same-side G4 representative](#R20A) - source/evidence family `S6_round20_addendum_verification.zip`.
- [R21. Excluding T8 and refining the remaining midpoint representatives](#R21) - source/evidence family `S6_round21_verification.zip`.
- [R21A. A strict lower bound for the floating vertical chord in diagonal G4](#R21A) - source/evidence family `S6_round21_addendum_verification.zip`.
- [R22. Actual bridge endpoints exclude the diagonal G4 representative](#R22) - source/evidence family `S6_round22_verification.zip`.
- [R22A. Two genuine gaps are forced in the same-side G4 representative](#R22A) - source/evidence family `S6_round22_verification.zip`.
- [R23. Completion of the G4 exclusion](#R23) - source/evidence family `S6_round23_verification.zip`.

## Part D: Opposite owned midpoints

- [R24. Exclusion of the G3 representative with both hosts on the F side](#R24) - source/evidence family `S6_round24_verification.zip`.
- [R24A. Reduction of the G3 representative with both hosts on the C side](#R24A) - source/evidence family `S6_round24_addendum_verification.zip`.
- [R25. Excluding all three G3 host representatives](#R25) - source/evidence family `S6_round25_verification.zip`.

## Part E: Near-end residual configurations

- [R13. Adjacent-corner budgets and necessary restrictions in G2](#R13) - source/evidence family `S6_round13_verification.zip`.
- [R14. Forced seams, disappearance of a vertical section, and the near left gap](#R14) - source/evidence family `S6_round14_verification.zip`.
- [R15. Continuous angle restrictions and a long-leg-free intersection in the near residual case](#R15) - source/evidence family `S6_round15_verification.zip`.
- [R15S. Angle separation and interior displacement of the near intersection](#R15S) - source/evidence family `S6_round16_verification.zip`.
- [R16P. Projection premises for the near intersection](#R16P) - source/evidence family `S6_round65_verification.zip / proofs`.
- [R16. Exclusion of the near G2 three-join branch](#R16) - source/evidence family `S6_round16_verification.zip`.
- [R16A. Gap ownership and intersections with a nonempty near horizontal section](#R16A) - source/evidence family `S6_round16_addendum_verification.zip`.
- [R17. Excluding the negative horizontal branch by overlap and projections](#R17) - source/evidence family `S6_round17_verification.zip`.
- [R18. Excluding the positive horizontal type and classifying the remaining near gaps](#R18) - source/evidence family `S6_round18_verification.zip`.
- [R19. Top-gap endpoints replace the old angle cascade](#R19) - source/evidence family `S6_round19_verification.zip`.
- [R26. Closing the entire near G2 top-gap representative](#R26) - source/evidence family `S6_round26_verification.zip`.
- [R27. One rotation branch each for near right gaps and far top gaps](#R27) - source/evidence family `S6_round27_verification.zip`.
- [R28. Excluding the entire near G2 representative](#R28) - source/evidence family `S6_round28_verification.zip`.

## Part F: Far-end gaps and horizontal sections

- [R29. Excluding every standardized far top-gap representative](#R29) - source/evidence family `S6_round29_verification.zip`.
- [R29N. Three far edge states and the corrected parallel directions](#R29N) - source/evidence family `S6_round65_verification.zip / proofs`.
- [R30. Correcting parallel directions and strengthening actual far axial constraints](#R30) - source/evidence family `S6_round30_verification.zip`.
- [R31. Excluding far three joins with a nonempty F horizontal section](#R31) - source/evidence family `S6_round31_verification.zip`.
- [R32. Excluding a right gap with a positive F horizontal section](#R32) - source/evidence family `S6_round33_verification.zip`.
- [R33. Excluding every right gap with a nonempty F horizontal section](#R33) - source/evidence family `S6_round33_verification.zip`.
- [R34. Excluding a left gap with a negative F horizontal section](#R34) - source/evidence family `S6_round34_verification.zip`.
- [R35. The last nonempty-horizontal family requires a two-tile relay](#R35) - source/evidence family `S6_round36_verification.zip`.
- [R36. Excluding all nonempty F horizontal mechanisms](#R36) - source/evidence family `S6_round36_verification.zip`.
- [R37. A global axial-root cap and two empty-horizontal side-gap rotation exclusions](#R37) - source/evidence family `S6_round37_verification.zip`.
- [R38. Closing all right gaps and the left double-bridge subclass](#R38) - source/evidence family `S6_round38_verification.zip`.
- [R39. Closing the LEFT true gap and excluding BOTTOM contact in the three-contact form](#R39) - source/evidence family `S6_round39_verification.zip`.

## Part G: Actual seams, contacts and lower exits

- [R40. A forced interior seam point in the three-contact form](#R40) - source/evidence family `S6_round40_verification.zip`.
- [R41. Near-diagonal double-direct contact and auxiliary seam comparisons](#R41) - source/evidence family `S6_round41_verification.zip`.
- [R42. A normalized seam point in the same central tile and a positive-rotation interval](#R42) - source/evidence family `S6_round42_verification.zip`.
- [R43. Small-angle double-direct exclusion for both rotations](#R43) - source/evidence family `S6_round43_verification.zip`.
- [R44. A forced top seam point for an upper bridge without repeated TOP midpoint](#R44) - source/evidence family `S6_round44_verification.zip`.
- [R45. Excluding two bridges by \(W\) and reducing four mechanisms to three](#R45) - source/evidence family `S6_round45_verification.zip`.
- [R46. Rotation separation for an upper bridge and actual lower interfaces of \(C,F\)](#R46) - source/evidence family `S6_round46_verification.zip`.
- [R47. A long bottom chord and exact five-point constraints for the same \(F\)](#R47) - source/evidence family `S6_round47_verification.zip`.
- [R48. Continuous-cover reductions and actual upper triple intersections](#R48) - source/evidence family `S6_round48_verification.zip`.

## Part H: Bridge angles and the same bottom tile

- [R49. A continuous small-angle exclusion for a right bridge in both rotations](#R49) - source/evidence family `S6_round49_verification.zip`.
- [R50. Enlarging the two-rotation right-bridge exclusion to \(\eta\le1/16\)](#R50) - source/evidence family `S6_round50_verification.zip`.
- [R51. Enlarging the two-rotation right-bridge exclusion to \(\eta\le1/8\)](#R51) - source/evidence family `S6_round51_verification.zip`.
- [R52. Small-angle upper-bridge exclusion and a uniform angle lower bound](#R52) - source/evidence family `S6_round52_verification.zip`.
- [R53. A universal actual relation between the left seam and the bottom short leg](#R53) - source/evidence family `S6_round53_verification.zip`.
- [R54. A complete near-diagonal exclusion when \(W\) contains the upper endpoint](#R54) - source/evidence family `S6_round54_verification.zip`.
- [R55. Excluding the entire positive-rotation class with \(Q_U\in W\)](#R55) - source/evidence family `S6_round55_verification.zip`.
- [R56. A continuous high-angle exclusion for negative rotation with \(Q_U\in W\)](#R56) - source/evidence family `S6_round56_verification.zip`.
- [R57. An actual lower-left exit point excludes a middle negative-rotation range](#R57) - source/evidence family `S6_round57_verification.zip`.
- [R58. Extending the negative-rotation exclusion to \(\eta\ge1/6\)](#R58) - source/evidence family `S6_round58_verification.zip`.
- [R59. Excluding the entire upper-bridge mechanism](#R59) - source/evidence family `S6_round59_verification.zip`.

## Part I: Remaining rotations and final contacts

- [R60. Excluding every negative rotation in the two remaining mechanisms](#R60) - source/evidence family `S6_round60_verification.zip`.
- [R61. An asymmetric triangle in the same \(F\) reduces the positive-rotation remainder](#R61) - source/evidence family `S6_round61_verification.zip`.
- [R62. Excluding all small \(z\) and confining the common remainder to an open strip](#R62) - source/evidence family `S6_round62_verification.zip`.
- [R63. Excluding the entire right bridge and leaving only positive double-direct contact](#R63) - source/evidence family `S6_round63_verification.zip`.
- [R64. Excluding all positive rotations in the middle-\(z\) double-direct form](#R64) - source/evidence family `S6_round64_verification.zip`.

## Recording a substantive review

For each challenged implication, record its module and local equation number,
the exact hypotheses, the earlier result providing each hypothesis, the
geometric membership or boundary issue, the arithmetic replay performed,
and a counterexample or correction if found. A successful program run does
not itself prove geometric applicability. Trace every identified gap through
the dependency order to its affected conclusions.

The historical fixed-point search and withdrawn candidate bounds are not
premises of this manuscript. R10 is read with R10C, R16 with R16P, and the
corrected TOP/H and RIGHT/V pairing is mandatory. Earlier local status words
refer to the intermediate reduction under discussion, not an independent
global confirmation of S(6)=2.
