#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *
#import "proof-layout.typ": proof

== DF — Differentials and Tangent Geometry <sup-df>

Differentials turn equations into linear relations. The resulting module records
first-order directions, but it also retains torsion and residue-field information
which a tangent-space dimension alone cannot see.

*Reading route.* Read DF-1–DF-9 after #book-link(<text-ii-8>)[II.8, the fundamental
  sequences]. Then read #book-link(<sup-lp2-1>)[LP2-1–LP2-6] for relative smoothness.
DF-10–DF-14 use the regular-immersion criterion in
#book-link(<sup-lp2-9>)[LP2-9] and the determinant rules in
#book-link(<sup-al>)[AL]. The complete-intersection case also uses
#book-link(<sup-al2>)[AL2]. All the explicit singular curves below are over an
algebraically closed field of characteristic zero. Other fields are named
explicitly. Purely algebraic assertions singled out below are to be proved by
the reader; the geometric reductions explain exactly where they are used.

=== Equations, infinitesimal directions, and residue fields

#metadata(none) <sup-df-1>
#proposition(number: "DF-1", title: "A tangent vector with its base point fixed")[
  Let $X$ be a scheme over a field $k$, and let $x in X(k)$. Morphisms
  $ops.spec(k[epsilon]\/ideal(epsilon^2)) -> X$ over $k$ whose restriction to
  $ops.spec k$ is $x$ are naturally in bijection with
  $
    ops.der_k(shf.o_(X,x),k)
    simeq ops.hom(idl.m_x\/idl.m_x^2, k, over: k)
    simeq ops.hom(tensor(Omega_(X\/k), k, over: shf.o_X), k, over: k),
  $
  where the tensor product in the last expression is the fiber at $x$.
]
#proof[
  The spectrum of the dual numbers has one point, so every such morphism
  factors through any affine neighborhood $U=ops.spec B$ of $x$. Write
  $e:B -> k$ for evaluation at $x$. The corresponding algebra homomorphism
  has the unique form $b mapsto e(b)+epsilon D(b)$; multiplication says
  $D(b c)=e(b)D(c)+e(c)D(b)$. Conversely this formula constructs the lift.
  An element outside the maximal ideal maps to a unit of the dual numbers,
  so the map extends uniquely to $B_(idl.m_x)=shf.o_(X,x)$. This is the
  explicit passage from the chosen affine chart to the local ring.

  Because the residue field is $k$, every $b$ in this local ring is uniquely
  $e(b)+(b-e(b))$. A derivation kills $k$ and $idl.m_x^2$, and a linear
  functional on $idl.m_x\/idl.m_x^2$ recovers it by this decomposition.
  The universal property of $Omega$, followed by tensoring with the residue
  field, gives the second identification. These elementary algebraic
  bijections are left to the reader to verify. They commute with localization,
  so changing $U$ leaves the constructed morphism unchanged; equivalently,
  the constructions agree on an affine refinement of two neighborhoods.
]

#metadata(none) <sup-df-2>
#proposition(number: "DF-2", title: "The Jacobian presentation")[
  For $B=A[x_1,dots,x_n]\/ideal(f_1 "," dots "," f_r)$ there is an exact sequence
  $
    B^r arrow.r.long^J B^n -> Omega_(B\/A) -> 0,
    quad J(e_i)=sum_j (partial f_i)/(partial x_j) d x_j.
  $
  There is no assertion that $J$ is injective. Under a change of base
  $A -> A'$, the same matrix with coefficients in $B'=tensor(B, A', over: A)$
  presents $Omega_(B'\/A')$.
]
#proof[
  Put $P=A[x_1,dots,x_n]$ and $I=ideal(f_1 "," dots "," f_r)$. Apply II.8.4A to
  $P -> B$. The free basis $d x_j$ of $Omega_(P\/A)$ identifies its tensor
  product with $B^n$. The surjection $B^r -> I\/I^2$ sends $e_i$ to
  $f_i$ modulo $I^2$, so its composite with the conormal map is exactly $J$.
  The derivative formula and right exactness of tensor products are the
  purely algebraic checks left to the reader. This also gives the stated
  presentation after base change. For instance, the relation $d(x^2)=2x d x$
  in $k[x]\/ideal(x^2)$ has a nonzero kernel when $ops.char k != 2$.
]

#metadata(none) <sup-df-3>
#proposition(number: "DF-3", title: "The residue-field term")[
  For any point $x$ of a $k$-scheme $X$, put $R=shf.o_(X,x)$ and
  $K=kappa(x)$. There is a canonical exact sequence
  $
    idl.m_x\/idl.m_x^2 -> tensor(Omega_(R\/k), K, over: R)
    -> Omega_(K\/k) -> 0.
  $
  If $x$ is closed in a scheme locally of finite type over $k$ and $K\/k$
  is separable, the first map is an isomorphism. Without this hypothesis
  neither its injectivity nor the vanishing of the last term is automatic.
  (Ex. II.8.1(a), separable closed-point case)
]
#proof[
  Restrict $X$ to $ops.spec B$ about $x$ and localize at its prime ideal.
  The localization formula of II.8.2A identifies the stalk of
  $Omega_(X\/k)$ with $Omega_(B_idl.p\/k)$. Apply II.8.4A to the
  quotient $R -> K$; the first map sends $a$ modulo $idl.m_x^2$ to
  $d a times.o 1$.
  Thus this sequence concerns the actual stalk and not the differentials of
  an arbitrarily chosen rational point.

  In the closed separable case, $K\/k$ is finite separable. Use the following
  precise algebraic fact: for a local $k$-algebra $R$ with finite separable
  residue field $K$, the map $idl.m\/idl.m^2 -> tensor(Omega_(R\/k), K, over: R)$
  is an isomorphism. Its proof, by lifting the residue field into
  $R\/idl.m^2$ using a separable primitive polynomial and correcting a lift
  by its invertible derivative, is left to the reader. Localization of the
  universal derivation shows that all identifications are canonical.
]

#metadata(none) <sup-df-4>
#proposition(number: "DF-4", title: "Relative differentials on fibers")[
  In a cartesian square $X'=fiber(X, Y', base: Y)$ with projection $g:X' -> X$,
  there is a canonical isomorphism
  $g^*Omega_(X\/Y) simeq Omega_(X'\/Y')$. In particular,
  $Omega_(X\/Y)|_(X_y) simeq Omega_(X_y\/kappa(y))$.
]
#proof[
  The map is induced by the derivation which sends a pulled-back section $b$
  to the differential of its image. Choose affine opens $V=ops.spec A$ in
  $Y$, $U=ops.spec B$ in $f^(-1)V$, and $V'=ops.spec A'$ in $Y'$ mapping to
  $V$. Their fiber product is $ops.spec B'$ for $B'=tensor(B, A', over: A)$.
  On this chart the map is
  $
    tensor(Omega_(B\/A), B', over: B) -> Omega_(B'\/A'),
    quad d b times.o c mapsto c,d(b times.o 1).
  $
  It is the isomorphism of II.8.2A, and DF-2 checks it directly on any finite
  presentation. Principal refinements localize this same map; the formula on
  universal differentials therefore agrees on all overlaps and glues.
  Taking $Y'=ops.spec kappa(y)$ proves the fiber statement. The same argument
  applies to extension of the ground field.
]

#metadata(none) <sup-df-5>
#proposition(number: "DF-5", title: "Tangent maps and tangent cones")[
  For a morphism $f:X -> Y$ over $k$ and a rational point $x$, the tangent map
  $d f_x:T_x X -> T_(f(x))Y$ is dual to the cotangent map induced by
  $f^*Omega_(Y\/k) -> Omega_(X\/k)$. If $f$ is given by coordinate
  polynomials $g_i$, its matrix is their Jacobian evaluated at $x$.
  The tangent cone is
  $ops.spec(bigOPlus(idl.m_x^n\/idl.m_x^(n+1), n>=0))$;
  it is a closed subscheme of the tangent space and need not be a vector space.
]
#proof[
  Compose the dual-number morphism of DF-1 with $f$. On affine charts this
  replaces $D$ by $D compose f^sharp$; the chain rule gives the matrix.
  Localizing the two coordinate rings at the corresponding maximal ideals
  identifies this map with the map on stalks, hence it is independent of
  the chosen charts. The graded algebra of the local ring is generated by
  $idl.m_x\/idl.m_x^2$, so the symmetric algebra surjects onto it. For a
  hypersurface at the origin, its kernel is generated by the lowest nonzero
  homogeneous part of its defining equation. These associated-graded
  algebra assertions are left to the reader. They explain why the full
  tangent cone contains information lost by its degree-one part.
]

=== Computations that distinguish geometric phenomena

#metadata(none) <sup-df-6>
#example(number: "DF-6", title: "A cusp and a node")[
  For the cusp $C=ops.spec A$, $A=k[x,y]\/ideal(y^2-x^3)$,
  $
    Omega_(A\/k)=(A d x plus.o A d y)\/ideal(2y d y-3x^2 d x).
  $
  At the origin the tangent space has dimension two, the curve has local
  dimension one, and the tangent cone is the doubled line $y^2=0$.
  Its normalization $k[x,y]\/ideal(y^2-x^3) -> k[t]$ sends
  $x mapsto t^2$, $y mapsto t^3$. The differential map sends
  $d x mapsto 2t d t$, $d y mapsto 3t^2 d t$, and has kernel
  $
    A\/ideal(x^2 "," y) dot tau, quad tau=2x d y-3y d x.
  $
  Here the map means $Omega_(A\/k) -> Omega_(k[t]\/k)$, before tensoring
  the source with the normalization. Tensoring the source can change the kernel.

  For the nodal curve $N=ops.spec B$,
  $B=k[x,y]\/ideal(y^2-x^2(x+1))$, the presentation is
  $
    Omega_(B\/k)=(B d x plus.o B d y)\/
    ideal(2y d y-x(3x+2) d x).
  $
  Its tangent space at the origin again has dimension two, but the tangent
  cone $y^2-x^2=0$ has two distinct lines. The normalization is
  $x=t^2-1$, $y=t(t^2-1)$; the points $t=1,-1$ lie above the node. The
  differential map is $d x mapsto 2t d t$, $d y mapsto (3t^2-1)d t$,
  with kernel
  $
    B\/ideal(x "," y) dot sigma, quad
    sigma=y(3x+2)d x-2x(x+1)d y.
  $
]
#proof[
  Apply DF-2 and then set $x=y=0$ for the two tangent spaces. DF-5 gives
  the initial equations of the tangent cones. The displayed normalization
  maps are finite and birational: in the cusp $t$ satisfies $t^2=x$ and
  equals $y/x$ in the fraction field; in the node $t^2=x+1$ and again
  $t=y/x$. Since $k[t]$ is integrally closed, these maps give the normalization.
  This last ring-theoretic criterion is left to the reader.

  The kernel computation can be checked without guessing generators.
  For the cusp, write $A=k[t^2,t^3]$. A pair $(a,b)$ maps to zero if and only
  if $(a,b)=(-3t h,2h)$, with $h in (t^2,t^3)A$; the defining
  differential relation corresponds to $h=t^3$. Thus the kernel is
  $(t^2,t^3)A\/t^3 A$, with basis represented by $t^2,t^4$.
  For the node use
  $B={q in k[t]:q(1)=q(-1)}$. A pair in the kernel has the form
  $((3t^2-1)h,-2t h)$; membership in $B^2$ forces
  $h=(t^2-1)q$ with $q in k[t]$. The defining relation corresponds to
  $q in B$, leaving $k[t]\/B$, represented by $t$.
  The reader should prove these elementary syzygy and quotient-module
  computations; they yield exactly the annihilators displayed above.
  The kernels are torsion because both maps become isomorphisms over the
  common fraction field. The doubled tangent line and the two normalization
  points distinguish the singularities despite their equal tangent dimensions.
]

#metadata(none) <sup-df-7>
#example(number: "DF-7", title: "The affine quadric cone")[
  For $A=k[x,y,z]\/ideal(x y-z^2)$,
  $
    Omega_(A\/k)=A^3\/ideal(y d x+x d y-2z d z).
  $
  The vertex has tangent dimension three and local dimension two. At every
  other closed point one Jacobian coefficient is nonzero, so a differential
  can be eliminated on a principal neighborhood. The resulting module is
  free of rank two there, and #book-link(<sup-lp2-4>)[LP2-4] proves smoothness.
  This is the same cone whose Weil divisors are studied in
  #book-link(<sup-dv>)[DV] and whose vertex blowup appears in
  #book-link(<sup-bu>)[BU].
]
#proof[
  DF-2 supplies the relation; its coefficients vanish simultaneously only
  at the vertex. The dimension assertion follows from the dimension of a
  polynomial ring modulo this nonzero irreducible equation, a commutative
  algebra calculation left to the reader. Localizing at any nonzero
  coefficient gives the asserted elimination and the standard smooth chart.
]

#metadata(none) <sup-df-8>
#example(number: "DF-8", title: "Separable powers and Frobenius")[
  Let $f:sch.a_k^1 -> sch.a_k^1$ be $s=t^m$ with $m>=1$. Its algebra is
  $k[s] -> k[t]=k[s,T]\/ideal(T^m-s)$, and
  $
    Omega_(k[t]\/k[s]) simeq (k[t]\/ideal(m t^(m-1))) d t.
  $
  If $ops.char k$ does not divide $m$, the map is étale on $D(t)$; when $m>1$
  the origin is ramified. When $m=1$ it is an isomorphism everywhere.
  In characteristic $p>0$, the map $s=t^p$ is finite flat but has
  $Omega_(k[t]\/k[s])=k[t] d t$. Its fibers have dimension zero, while this
  differential module has rank one; it is nowhere smooth.
]
#proof[
  DF-2 differentiates the single relation over $k[s]$. Division by the monic
  polynomial gives the basis $1,t,dots,t^(m-1)$ over $k[s]$; this algebraic
  calculation is left to the reader. It proves finite flatness. Apply
  #book-link(<sup-lp2-3>)[LP2-3] to the displayed module and flatness.
  In the Frobenius case every geometric fiber is
  $overline(kappa(s))[u]\/ideal(u^p)$ after translating its unique root.
  It is nonreduced and hence not regular. Thus local freeness of differentials
  alone is not a smoothness criterion. For the fiber calculations see also
  #book-link(<sup-mg>)[MG].
]

#metadata(none) <sup-df-9>
#example(number: "DF-9", title: "An inseparable closed point")[
  Suppose $ops.char k=p>0$ and $a in.not k^p$. In $sch.a_k^1$ let $x$ be the
  closed point with ideal $ideal(t^p-a)$, and put $K=k[t]\/ideal(t^p-a)$.
  The sequence of DF-3 is
  $
    K dot [t^p-a] arrow.r.long^0 K d t arrow.r.long^simeq K d overline(t) -> 0.
  $
  The local ring $k[t]_(t^p-a)$ is regular of dimension one. The ambient
  affine line is smooth over $k$, although the closed immersion of this
  residue point has a zero cotangent map. In contrast, $ops.spec K$ itself
  is regular but is not smooth over $k$: after extending $k$ to $K$ its
  coordinate ring becomes $K[u]\/ideal(u^p)$.
]
#proof[
  Differentiate $t^p-a$ over $k$ and use DF-2 both before and after the
  quotient. The first map is zero and the latter differential module is free
  of rank one over $K$. Irreducibility of $t^p-a$, the discrete valuation
  description of the local ring, and the displayed tensor-product
  calculation are algebraic assertions left to the reader. They show why
  the residue term cannot be deleted, and why regularity over an imperfect
  field does not imply geometric regularity.
]

=== Conormal sequences and canonical forms

#metadata(none) <sup-df-10>
#corollary(number: "DF-10", title: "Normal directions and the tangent sequence")[
  Let $i:X arrow.r.hook Y$ be a closed immersion of smooth schemes of finite
  type over a field $k$, with ideal sheaf $shf.i$. Define
  $shf.n_(X/Y)=(shf.i/shf.i^2)^ast$.
  Dualizing the locally split conormal sequence of
  #book-link(<sup-lp2-9>)[LP2-9] gives the locally split exact sequence
  $
    0 -> shf.t_X -> i^*shf.t_Y -> shf.n_(X/Y) -> 0.
  $
  The quotient records first-order normal directions along $X$.
]

#proof[
  LP2-9 proves the locally split conormal sequence with its canonical
  differential maps. On a splitting open, dualizing a split exact
  sequence of finite free modules gives a split exact sequence in the
  reverse order (Check!). These local duals are restrictions of the
  global sheaf-Hom maps, so exactness holds on the cover and hence on $X$
  by SC-4. The middle dual is $i^*shf.t_Y$ by QC-4, since
  $Omega_(Y/k)$ is finite locally free. The other duals are $shf.t_X$
  and the normal sheaf by definition. The maps agree on overlaps because
  they are the duals of the same canonical maps, irrespective of the
  chosen local splittings.
]

#metadata(none) <sup-df-11>
#proposition(number: "DF-11", title: "The normal bundle of a hypersurface")[
  A smooth degree-$d$ hypersurface $X subset sch.p_k^n$ has
  $shf.i\/shf.i^2 simeq shf.o_X(-d)$ and
  $shf.n_(X\/sch.p^n) simeq shf.o_X(d)$.
]
#proof[
  Multiplication by its homogeneous equation $F$ identifies the ideal sheaf
  with $shf.o_((sch.p)^n)(-d)$, as in II.5. On the chart $D_+(X_i)$ the
  local equation is $F/X_i^d$, a non-zero-divisor. Its class freely generates
  $I\/I^2$ over the hypersurface ring: cancellation by the local equation
  proves this, an algebraic check left to the reader. On a chart overlap the
  equations differ by $(X_j/X_i)^d$, exactly the transition of
  $shf.o (-d)$. Restrict and dualize to obtain both asserted bundles. DF-10
  identifies the second with normal first-order directions.
]

#metadata(none) <sup-df-12>
#remark(number: "DF-12", title: "The scaling relation in the Euler sequence")[
  The Euler sequence of II.8 is
  $
    0 -> Omega_((sch.p^n)\/k) -> shf.o_((sch.p)^n)(-1)^(n+1)
    arrow.r.long^((X_0,dots,X_n)) shf.o_((sch.p)^n) -> 0.
  $
  On $D_+(X_i)$ put $u_j=X_j/X_i$ and $u_i=1$. The last map becomes
  $(a_0,dots,a_n) mapsto sum_j u_j a_j$. Its kernel has basis
  $e_j-u_j e_i$ for $j!=i$, corresponding to $d u_j$.
  Indeed $d(X_j/X_i)=(X_i d X_j-X_j d X_i)/X_i^2$ removes the common
  homogeneous scaling direction. On overlaps the quotient rule transforms
  these expressions into one another. This chart calculation, whose
  elementary differentiation is left to the reader, explains the sequence
  already proved in the main text rather than adding another abstract proof.
]

#metadata(none) <sup-df-13>
#proposition(number: "DF-13", title: "Smooth adjunction by determinants")[
  A smooth degree-$d$ hypersurface $X subset sch.p_k^n$ satisfies
  $omega_X simeq shf.o_X(d-n-1)$. More generally, if a smooth complete
  intersection $X subset sch.p_k^n$ is cut out by a homogeneous regular
  sequence of degrees $d_1,dots,d_r$, then
  $
    omega_X=op("det") Omega_(X\/k)
    simeq shf.o_X(sum_i d_i-n-1).
  $
  (Ex. II.8.4(d))
]
#proof[
  Taking the determinant in DF-12 gives
  $op("det") Omega_((sch.p^n)\/k)=shf.o_((sch.p)^n)(-n-1)$.
  In the hypersurface case apply the determinant rule of
  #book-link(<sup-al-9>)[AL-9, in top exterior degree] to DF-10 and use DF-11.
  For the complete intersection, the classes of the equations form a basis
  of $I\/I^2$ on affine charts, by the regular-sequence assertion of
  #book-link(<sup-al2>)[AL2]. Their homogeneous transitions identify this
  sheaf with $bigOPlus(shf.o_X(-d_i), i=1, top: r)$. Therefore
  $
    op("det") i^*Omega_((sch.p^n)\/k)
    simeq tensor(op("det")(shf.i\/shf.i^2), omega_X),
  $
  where the right side denotes the tensor product of the two line bundles.
  Cancel $shf.o_X(-sum_i d_i)$ to obtain the formula. All determinant
  identifications come from exact sequences and thus agree on chart
  overlaps. The exterior-algebra determinant rule is a purely algebraic
  assertion left to the reader if it has not already been proved in AL.
  This argument concerns the canonical bundle of a smooth scheme; it makes
  no assertion that differentials on a singular complete intersection are
  invertible.
]

#metadata(none) <sup-df-14>
#proposition(number: "DF-14", title: "Plane curves: the actual local form")[
  Let $C=V(H) subset sch.p_k^2$ be a smooth plane curve of degree $d$.
  On $Z!=0$ put $x=X/Z$, $y=Y/Z$, $F=H(x,y,1)$. Its canonical bundle has
  local generators
  $
    eta_Z=(d x)/F_y quad "on" D(F_y),
    quad quad eta_Z=-(d y)/F_x quad "on" D(F_x).
  $
  These glue, and their projective transitions give $omega_C simeq shf.o_C(d-3)$.
  (Ex. II.8.4(d), plane-curve case)
]
#proof[
  Smoothness implies that $D(F_x)$ and $D(F_y)$ cover this affine part of
  $C$, by #book-link(<sup-lp2-4>)[LP2-4]. The relation
  $F_x d x+F_y d y=0$ shows equality on their intersection; elimination of
  one differential shows that each displayed form is a basis where its
  denominator is invertible.

  On $X!=0$ put $u=Y/X$, $v=Z/X$, and $G=H(1,u,v)$.
  On the overlap, $u=y/x$, $v=1/x$, and
  $F(x,y)=x^d G(y/x,1/x)$. Differentiating along the curve gives
  $G_u=x^(1-d)F_y$ and $d v=-x^(-2)d x$. Consequently
  $
    eta_X=-(d v)/G_u=x^(d-3) eta_Z.
  $
  The same computation on the other intersections yields the transitions
  of $shf.o_C(d-3)$; the chain-rule identities are left to the reader.
  No division is made outside the indicated principal opens. Because the
  forms are bases on a cover, these transitions describe the entire
  canonical line bundle and agree with DF-13.
]

#metadata(none) <sup-df-15>
#example(number: "DF-15", title: "A conic, a cubic, and a relative equation")[
  The smooth conic $X Z-Y^2=0$ has $omega_C=shf.o_C(-1)$. On $Z!=0$,
  $F=x-y^2$ gives $eta=-d y$. Since a line meets a conic in degree two,
  $deg omega_C=-2$; equivalently use the parametrization
  $[s:t] mapsto [s^2:s t:t^2]$ and pull back $shf.o_C(1)$ to
  $shf.o_(sch.p^1)(2)$.

  A smooth cubic $Y^2 Z=X^3+a X Z^2+b Z^3$ in characteristic zero has
  $omega_C=shf.o_C$. On its affine chart the canonical form is
  $d x/(2y)=d y/(3x^2+a)$ on the corresponding principal opens. DF-14 with
  $d=3$ shows that it extends as a nowhere-vanishing section across infinity;
  a denominator vanishing in one expression requires the other local frame.

  For the conic family $X Y=t Z^2$ over $ops.spec k[t]$, the chart $Z!=0$
  has coordinate ring $A=k[t,x,y]\/ideal(x y-t)$ and
  $Omega_(A\/k[t])=A^2\/ideal(y d x+x d y)$.
  Specialization at $t=c$ uses DF-4 without an additional correction term.
  The global family, its special fiber, and the contrast between smoothness
  of the total space and of the morphism are worked out in
  #book-link(<sup-vs2>)[VS2].
]

#metadata(none) <sup-df-16>
#exercise(title: "DF-16 — Calculations and hypothesis checks")[
  + Compute the tangent map of $t mapsto (t^2,t^3)$ at zero and away from
    zero. Explain why a zero tangent map at zero does not imply a constant
    morphism.
  + Verify both kernel computations of DF-6, including the annihilator of
    each displayed torsion generator. Compare with the kernel after tensoring
    the source module with $k[t]$.
  + For $k[x,y]\/ideal(x y)$, compute its normalization, differential module,
    tangent cone, and torsion kernel. Compare this reducible node with DF-6.
  + In DF-9 distinguish the tangent space of the local ring, the relative
    cotangent fiber of the affine line, and the differentials of the residue
    field. Specify every base field.
  + Derive the normal bundle and canonical bundle of a smooth intersection
    of two quadrics in $sch.p_k^4$. Check the degree shifts on two standard
    projective charts.
]

*Sources.* Hartshorne II.8, especially the fundamental sequences, Euler
sequence, and smooth adjunction; Liu, §6.2, Exercises 2.4–2.5 and
Proposition 6.3.13, with the smooth case of §6.4. The relative morphism
criteria used here are established in #book-link(<sup-lp2>)[LP2].
