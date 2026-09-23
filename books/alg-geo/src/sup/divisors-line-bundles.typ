#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== DV — Divisors and line bundles <sup-dv>

This section makes the dictionary of II.6 explicit. An invertible sheaf is
locally free of rank one. For an integral scheme its rational sections are
elements of its one-dimensional generic fiber; for a general Noetherian
scheme, meromorphic sections use the total quotient sheaf. Purely algebraic
and topological assertions are marked *Proof left to the reader*; the
geometric constructions specify the restriction and gluing maps.

=== Local equations and rational sections

#metadata(none) <sup-dv-1>
#proposition(number: "DV-1", title: "The transition convention")[
  Let a Cartier divisor $D$ be represented by equations $f_i$ on an open cover
  $U_i$ of $X$, with $f_i/f_j$ a regular unit on $U_i inter U_j$. Regard
  $shf.o_X(D)$ as the invertible subsheaf of the meromorphic sheaf generated
  by $e_i=f_i^(-1)$ on $U_i$. Our convention is
  $
    e_i=(f_j/f_i)e_j.
  $
  Thus, if a section has coefficients $a_i$ in these frames, its gluing
  condition is $a_j=a_i f_j/f_i$. Tensor product adds divisors, the dual
  changes the sign, and $shf.o_X(D)$ has the canonical meromorphic section $1$.
]

#proof[
  Multiplication by $f_i$ identifies the prescribed subsheaf on $U_i$
  with $shf.o_(U_i)$. The displayed frame identity shows that the subsheaves
  agree on overlaps. The transition units satisfy
  $(f_j/f_i)(f_l/f_j)=f_l/f_i$, so the sheaf gluing result
  #book-link(<sup-sl-3>)[SL-3] applies. The multiplication map
  $tensor(shf.o (D), shf.o (E), over: shf.o_X)->shf.o (D+E)$ sends
  $f_i^(-1) times.o g_i^(-1)$ to $(f_i g_i)^(-1)$ on a common refinement.
  It is an isomorphism in each frame; the multiplication description is
  unchanged by restriction, hence glues. Setting $E=-D$ gives the dual
  identification. These are the constructions of II.6.13 with the frame
  convention fixed explicitly.
]

#metadata(none) <sup-dv-2>
#proposition(number: "DV-2", title: "A rational section determines its divisor")[
  Let $X$ be integral and $shf.l$ invertible. Choose a nonzero rational section
  $s$ and frames $e_i$ of $shf.l$ on $U_i$. Write $s=a_i e_i$. Then
  $ops.dv (s)$ is the Cartier divisor with equations $a_i$, and there is a
  canonical isomorphism, depending on $s$,
  $
    shf.o_X(ops.dv (s)) isoto shf.l, quad h mapsto h s.
  $
  Replacing $s$ by $q s$, where $q in K(X)^times$, adds $ops.dv (q)$. A
  nonzero regular section gives an effective Cartier divisor, its zero scheme.
]

#proof[
  Every nonempty open of an integral scheme contains its generic point.
  Thus each frame identifies the generic fiber with $K(X)$ and gives
  $a_i in K(X)^times$. On an overlap with $e_i=u_(i j)e_j$,
  equality of the two expressions for $s$ gives $a_j=u_(i j)a_i$.
  Consequently $a_i/a_j$ is a regular unit, as required for a Cartier
  divisor. The displayed map sends the frame $a_i^(-1)$ to $e_i$,
  and these maps agree on overlaps because they all multiply by the same
  rational section. SL-3 glues them and their inverses. If $s$ is regular,
  each coefficient belongs to $shf.o_X(U_i)$; every stalk coefficient is
  nonzero in a domain, hence regular. Its vanishing ideal is locally
  $(a_i)$, which is the effective Cartier zero scheme. Finally the
  coefficients of $q s$ are $q a_i$, proving the principal-divisor formula.
]

#metadata(none) <sup-dv-3>
#proposition(number: "DV-3", title: "Effective divisors and their ideals")[
  If $D$ is effective Cartier, its ideal sheaf is $shf.i_D=shf.o_X(-D)$ and
  there is a canonical exact sequence
  $
    0 -> shf.o_X(-D) -> shf.o_X -> shf.o_D -> 0.
  $
  More generally, a section of an invertible sheaf defines an effective
  Cartier zero scheme if and only if its coefficients in local frames are
  non-zero-divisors.
]

#proof[
  Refine the equation cover by affine opens $U=ops.spec A$ on which the
  divisor has equation $a in A$. Under the affine correspondence of
  II.5.5, the inclusion $shf.o (-D)|_U->shf.o_U$ is the inclusion of
  $(a)$ in $A$, or multiplication by $a$ after choosing its free generator.
  Its cokernel is $A\/(a)$. Multiplication is injective precisely when $a$
  is regular. This is the terminal algebraic assertion; *proof left to
  the reader*. Sheafification and restriction preserve this sequence
  (#book-link(<sup-al-3>)[AL-3]); exactness may also be checked on stalks.
  On overlaps the equations differ by units, so their ideals and quotient
  maps agree. This glues the closed subscheme and the exact sequence.
]

For example, $V(u)$ in $ops.spec (k[u,v]\/(u v))$ is given by one equation,
but $u v=0$ and $v!=0$. It is not an effective Cartier divisor. The algebraic
check is *left to the reader*. A hypersurface described by one equation
must still pass the non-zero-divisor test.

#metadata(none) <sup-dv-4>
#proposition(number: "DV-4", title: "When pullback is a divisor")[
  Let $f:X->Y$ and let $D$ be effective Cartier on $Y$. Its inverse-image
  closed subscheme is effective Cartier if the pulled-back equation is
  regular at every point of $X$. In this case denote the divisor by $f^*D$;
  then
  $
    shf.o_X(f^*D) simeq f^*shf.o_Y(D).
  $
  Flat morphisms satisfy this condition. A dominant morphism between integral
  schemes also pulls back all Cartier divisors, including differences of
  effective divisors. Pullback of the invertible sheaf itself is defined for
  every morphism.
]

#proof[
  Choose an equation $a$ on an affine $V=ops.spec A subset Y$ and affine
  opens $U=ops.spec B$ in $f^(-1)V$, with ring map $phi:A->B$. The
  inverse-image ideal is $(phi(a))$; it is free on its proposed generator
  if and only if $phi(a)$ is regular. The stalk and cover criterion, and
  preservation under flat maps, are the Cartier-divisor criteria in
  #book-link(<sup-lp2>)[LP2]. Concretely flatness preserves the injection
  $A ->^a A$ after tensoring with $B$. For a dominant map of integral
  schemes the affine ring maps on nonempty such charts are injective
  (the dominance criterion in #book-link(<sup-lp>)[LP]), so they extend
  to function fields. Both numerator and denominator of a nonzero
  rational equation remain nonzero. In either case, pulling back the
  unit ratios gives Cartier data on the inverse-image cover. The frame
  $f_i^(-1)$ pulls back to the frame $phi(f_i)^(-1)$; the transition
  functions are the pulled-back ratios from DV-1. The local isomorphisms
  therefore agree on overlaps.
]

The inclusion $ops.spec k->{0} subset sch.a_k^1$ pulls the equation $t$
of the origin back to zero. Multiplication by zero on $k$ is not injective,
so the inverse image is the entire point, not an effective Cartier divisor.
The pullback of $shf.o_(sch.a^1)([0])$, which is a free line bundle, is still
the free line bundle on $ops.spec k$.

#metadata(none) <sup-dv-5>
#proposition(number: "DV-5", title: "Codimension-one multiplicities")[
  Let $X$ be normal, Noetherian, integral, and separated. For a codimension-one
  point $xi$, its local ring is a DVR. A Cartier divisor with equation $f_i$
  near $xi$ has Weil coefficient $nu_xi(f_i)$. This gives an injective map
  from Cartier divisors to Weil divisors, compatible with principal divisors.
  It is an isomorphism if $X$ is locally factorial, as in II.6.11.
]

#proof[
  Localization of a normal Noetherian domain at a height-one prime is a
  DVR; this is the local algebra used in II.6. The ratio of two equations
  is a unit in this DVR, so the coefficient is independent of the chart.
  The finite-support argument is II.6.1 applied on a finite affine cover.
  For injectivity, let all coefficients of a Cartier divisor vanish.
  On a normal affine chart $ops.spec A$ with rational equation $f$, the
  valuations of both $f$ and $f^(-1)$ are nonnegative at every height-one
  prime. The intersection formula II.6.3A gives $f,f^(-1) in A$.
  Thus every equation is a unit, and the Cartier divisor is zero.
  This last intersection-of-localizations assertion is commutative
  algebra: *proof left to the reader*. The locally factorial inverse is
  the construction already given in II.6.11; it is not asserted for a
  merely normal scheme. DV-15 exhibits the failure.
]

=== Meromorphic data beyond integral schemes

#metadata(none) <sup-dv-6>
#definition(number: "DV-6", title: "The total quotient sheaf")[
  On a Noetherian scheme $X$, let $shf.k_X$ be the sheaf obtained by inverting
  regular sections of $shf.o_X$ locally. On an affine open $ops.spec A$,
  its sections are $Q(A)$, the total quotient ring of
  #book-link(<sup-al2-5>)[AL2-5]. A Cartier divisor is a global section of
  $shf.k_X^times\/shf.o_X^times$. Its equations are therefore units in the
  total quotient sheaf, with regular-unit ratios.
]

The affine description and its compatibility with restriction are
localization facts for Noetherian rings: *proof left to the reader*.

#metadata(none) <sup-dv-7>
#proposition(number: "DV-7", title: "Meromorphic extension across an associated-point open")[
  If $X$ is Noetherian and $j:U arrow.r.hook X$ is an open subscheme containing
  every associated point of $X$, then
  $
    shf.o_X arrow.r.hook j_*shf.o_U, quad
    shf.k_X isoto j_*shf.k_U.
  $
]

#proof[
  The first is the associated-point restriction criterion in LP. For the
  second, restrict the comparison map to an arbitrary affine
  $V=ops.spec A subset X$. Choose a finite principal cover
  $U inter V=union_i D(g_i)$; finiteness is possible since $A$ is Noetherian.
  A meromorphic section gives elements $q_i in Q(A_(g_i))$ agreeing in
  $Q(A_(g_i g_j))$. The terminal localization assertion is: if the union
  of these principal opens contains $ops.ass(A, over: A)$, such a compatible
  family is the restriction of a unique fraction $a/b$ with $a in A$ and
  $b$ regular in $A$. *Proof left to the reader (commutative algebra):*
  clear the finite sets of denominator relations and use prime avoidance
  on the ideal of possible common denominators; that ideal avoids every
  associated prime. The injectivity in the first assertion guarantees
  uniqueness. Thus the comparison is bijective on every affine open,
  which proves the sheaf isomorphism. Uniqueness makes the extensions
  agree on affine overlaps. Example AL2-4 explains why generic points
  alone cannot replace associated points here.
]

#metadata(none) <sup-dv-8>
#lemma(number: "DV-8", title: "A common affine neighborhood")[
  If $X$ is quasi-projective over a Noetherian affine scheme and $F$ is a finite
  set of points of $X$, there is an affine open of $X$ containing $F$.
]

#proof[
  Write $X$ as an open subscheme of a closed subscheme $bar(X)$ of
  $sch.p_A^n$, where the base is $ops.spec A$. The boundary
  $Z=bar(X)-X$ is closed in $sch.p_A^n$ and disjoint from $F$. Choose a
  homogeneous ideal $J$ defining $Z$. Each point of $F$ corresponds to
  a homogeneous prime $idl.p_i$ not containing the irrelevant ideal,
  and $J subset.not idl.p_i$. Homogeneous prime avoidance gives a
  positive-degree homogeneous $g in J$ outside every $idl.p_i$.
  *Proof left to the reader (commutative algebra):* prove this finite
  homogeneous prime-avoidance statement, allowing unequal degrees by
  taking powers; no infinitude hypothesis on residue fields is needed.
  Then $F subset D_+(g) inter bar(X) subset X$. Since $D_+(g)$ is affine
  and $bar(X)$ is closed in projective space, their intersection is
  affine. It is open in $X$ and gives the required neighborhood.
]

#metadata(none) <sup-dv-9>
#theorem(number: "DV-9", title: "Two Cartier-class surjectivity theorems")[
  The injective map $ops.cacl (X)->ops.pic (X)$ of II.6.14 is an isomorphism
  in either of the following cases:

  + $X$ is Noetherian and has no embedded associated points;
  + $X$ is quasi-projective over a Noetherian affine scheme, with embedded
    points allowed.
]

#proof[
  In both cases we construct a meromorphic frame of an arbitrary invertible
  sheaf $shf.l$, that is, an isomorphism
  $tensor(shf.k_X, shf.l, over: shf.o_X) simeq shf.k_X$. Once this is done,
  the image of a regular local frame is a meromorphic unit $b_i$.
  The equations $b_i^(-1)$ have regular-unit ratios, and the inclusions
  identify $shf.l$ with the subsheaf $shf.o_X(D)$, exactly as in DV-1.

  In the first case let $eta_1,dots,eta_r$ be the finitely many generic
  points. For each $i$ choose a frame near $eta_i$ and remove the closures
  of all other generic points. The resulting opens $U_i$ are pairwise
  disjoint: a point belonging to both would lie on an irreducible component
  retained in each, contrary to the removals. Their union $U$ contains
  all associated points, and the chosen frames give $shf.l|_U simeq shf.o_U$.
  By DV-6 its meromorphic extension is a frame over $shf.k_X$.
  More explicitly, the maps on each trivializing affine chart extend
  uniquely from its intersection with $U$, and uniqueness gives agreement
  on overlaps. Restriction of $shf.l$ is injective because this is true for
  $shf.o_X$ in a local frame, so the resulting meromorphic embedding loses
  no sections.

  In the second case DV-8 gives $V=ops.spec A$ containing the finite set
  $ops.ass(X)$. Let $P=Gamma(V, shf.l)$. The affine correspondence makes
  it an invertible $A$-module. AL2-5 says that $Q(A) times.o_A P$ is free
  of rank one and that a frame spreads to $P_s$ for one regular $s in A$.
  Thus $U=D(s) subset V$ still contains all associated points of $X$,
  and $shf.l|_U$ is trivial. The extension just described again supplies
  a meromorphic frame. The semilocal freeness and spreading assertions
  are *left to the reader (commutative algebra)* in AL2-5.

  The injectivity used at the start is the existing Cartier-class theorem:
  a global generator of $shf.o_X(D)$ is a meromorphic unit, so a trivial
  invertible sheaf makes $D$ principal. This also shows that the constructed
  inverse depends only on the invertible-sheaf class.
]

Sources for these extensions are Liu 7.1.19 and 7.1.32; DV-8 is Liu
3.3.36. The first construction does not require a common affine neighborhood
of the generic points. The second accommodates the embedded point in AL2-4.

=== Length, residue fields, and degree

#metadata(none) <sup-dv-10>
#proposition(number: "DV-10", title: "Multiplicity in dimension one")[
  Let $(A,idl.m)$ be a one-dimensional Noetherian local ring. For regular
  $a,b in A$, the quotients by $(a)$, $(b)$, and $(a b)$ have finite length,
  with length zero when the element is a unit, and
  $
    0 -> A\/(b) ->^(times a) A\/(a b) -> A\/(a) -> 0,
    quad
    ops.length (A\/(a b))=ops.length (A\/(a))+ops.length (A\/(b)).
  $
  Consequently
  $
    ops.mult_A(a/b)=ops.length_A(A\/(a))-ops.length_A(A\/(b))
  $
  is a well-defined homomorphism $Q(A)^times\/A^times->ZZ$. If $A$ is a DVR,
  it is the usual valuation.
]

*Proof left to the reader (commutative algebra).* Regular elements avoid
the minimal primes, so their nonempty vanishing sets in this local
one-dimensional spectrum consist only of the closed point. This gives
finite length. Verify the displayed sequence, use length additivity,
and compare two fraction presentations by cross multiplication. In a DVR
the filtration by powers of a uniformizer has one-dimensional residue-field
quotients, giving $ops.length (A\/(pi^n))=n$.

For a Cartier divisor on a Noetherian scheme, apply this calculation to the
one-dimensional local rings at codimension-one points. Unit ratios preserve
the multiplicities. On an affine equation chart, only the finitely many
minimal primes over its numerator or denominator can contribute. Thus the
local cycles agree on overlaps and define its codimension-one cycle. This
construction uses lengths even when those local rings are not DVRs.

#metadata(none) <sup-dv-11>
#proposition(number: "DV-11", title: "Degree over an arbitrary field")[
  Let $C$ be a proper integral curve over a field $k$. For a Cartier divisor
  $D$, define
  $
    deg_k(D)=sum_(x in C text(" closed"))ops.mult_x(D)[k(x):k].
  $
  For an effective Cartier divisor $E$ this is
  $deg_k(E)=dim_k Gamma(E, shf.o_E)$. Every Cartier divisor is a difference
  $E-F$ of effective Cartier divisors, so the finite-algebra formula computes
  all degrees by subtraction.
]

#proof[
  The nonempty support of an effective equation on an integral curve has
  dimension zero. Since $E$ is closed in a proper finite-type curve, it is
  finite over $k$: a zero-dimensional finite-type $k$-scheme is a finite
  disjoint union of spectra of Artinian finite-dimensional $k$-algebras.
  This last algebraic assertion is *left to the reader*. Put
  $B=Gamma(E, shf.o_E)$. Its decomposition into its local factors gives
  $B=product_(x in E) shf.o_(E,x)$. Each composition factor over
  $shf.o_(C,x)$ is $k(x)$, hence
  $dim_k shf.o_(E,x)=[k(x):k]ops.length_(shf.o_(C,x))(shf.o_(E,x))$.
  The product decomposition and dimension formula are *left to the reader
  (commutative algebra)*. Summing gives the assertion.

  To produce $E-F$, take finitely many affine equation charts
  $U_i$ on which $D$ is $a_i/b_i$ with $a_i,b_i$ regular. The finite set
  $V(b_i) subset U_i$ consists of closed points of $C$, hence is closed
  in $C$. Glue the equation $b_i$ on $U_i$ to equation $1$ on
  $C-V(b_i)$; their ratio on the overlap is a unit. This gives an
  effective Cartier divisor $F_i$. Let $F=sum_i F_i$.
  On $U_i$, the divisor $D+F_i$ has regular equation $a_i$; every other
  $F_j$ is effective. Therefore $E=D+F$ is effective on this cover, hence
  effective globally by the Cartier locality criterion. Length additivity
  in DV-10 gives $deg(D)=deg(E)-deg(F)$, independently of the choices.
]

#metadata(none) <sup-dv-12>
#proposition(number: "DV-12", title: "Finite maps of normal curves")[
  Let $f:C->B$ be a finite dominant morphism of normal proper integral curves
  over $k$, and put $n=[K(C):K(B)]$. For a closed point $y in B$,
  $
    f^*[y]=sum_(x mapsto y)e_x[x], quad
    sum_(x mapsto y)e_x[k(x):k(y)]=n.
  $
  Consequently $deg_k(f^*D)=n deg_k(D)$ for every Cartier divisor $D$ on $B$.
]

#proof[
  Normality makes the curve local rings DVRs, so closed points are Cartier.
  Fix $y$, write $R=shf.o_(B,y)$ with uniformizer $pi$, and localize the
  finite affine algebra of $f$ at $y$ to obtain a finite semilocal
  $R$-algebra $T$. Dominance and integrality make it torsion-free over
  $R$. A finite torsion-free module over a DVR is free; tensoring with
  $K(B)$ identifies its rank as $n$. Hence
  $dim_(k(y))(T\/pi T)=n$. The local factors of this Artinian algebra are
  $shf.o_(C,x)\/(pi)$ for $x$ above $y$. Their dimensions over $k(y)$
  are $e_x[k(x):k(y)]$, by DV-10. These finite-module assertions are
  *left to the reader (commutative algebra)*. The local equation of the
  pullback is precisely $pi$, so its Weil coefficient is $e_x$.
  Sum the factor dimensions, then multiply by $[k(y):k]$ and use the
  tower law for residue fields. Additivity gives the divisor formula.
]

#metadata(none) <sup-dv-13>
#proposition(number: "DV-13", title: "Extension of the ground field")[
  Let $C$ and $D$ be as in DV-11, let $K/k$ be any field extension, and let
  $p:C_K->C$ be the projection. The flat pullback $D_K$ is Cartier, and
  $deg_K(D_K)=deg_k(D)$. On $C_K$ the degree uses the length multiplicities
  of DV-10, even if $C_K$ is reducible or nonreduced.
]

#proof[
  Field extension is flat, so DV-4 defines the pullback. For an effective
  divisor $E=ops.spec B$, the inverse-image scheme is exactly
  $E_K=ops.spec (tensor(B, K, over: k))$: this is the affine fiber-product
  construction, and its ideal is the pulled-back Cartier ideal. A
  $k$-basis of the finite-dimensional algebra $B$ becomes a $K$-basis
  after tensoring. Thus
  $dim_K(tensor(B, K, over: k))=dim_k B$; *proof left to the reader
  (linear algebra)*. Apply DV-11's Artinian factor calculation over both
  fields. The calculation applies to these effective zero-dimensional
  schemes even when their ambient curves are nonreduced. Finally write
  $D=E-F$ as in DV-11 and subtract. No assertion about higher cohomology
  is used: all global sections computed here belong to finite affine
  schemes.
]

For a real irreducible quadratic $q(t)$, its closed point on $sch.p_RR^1$
has residue field $CC$ and degree two. Over $CC$, the algebra
$RR[t]\/(q) times.o_RR CC$ is $CC times CC$, so the degree is $1+1$.
For a nonperfect field $k$ of characteristic $p$ and $a in.not k^p$, the
point defined by $t^p-a$ has degree $p$. Over $K=k(a^(1/p))$ its algebra is
$K[epsilon]\/(epsilon^p)$, one point of length $p$. These algebra
isomorphisms are *left to the reader*. They explain why counting geometric
points without their lengths gives the wrong degree.

=== Three calculations to use again

#metadata(none) <sup-dv-14>
#example(number: "DV-14", title: "The projective line")[
  Write $U_0=ops.spec k[t]$ and $U_infinity=ops.spec k[u]$, with $u=t^(-1)$.
  The function $t$ has divisor $[0]-[infinity]$, since its orders in the
  two discrete valuation rings are $1$ and $-1$. For $D=d[infinity]$,
  take equations $1$ on $U_0$ and $u^d$ on $U_infinity$. The corresponding
  frames satisfy
  $
    e_0=1, quad e_infinity=u^(-d)=t^d, quad e_0=t^(-d)e_infinity.
  $
  These are the frames of $shf.o_(sch.p^1)(d)$. A global section has
  coefficients $p(t) in k[t]$, $q(u) in k[u]$ with
  $q(u)=u^d p(u^(-1))$. Comparing Laurent coefficients gives
  $
    Gamma(sch.p^1, shf.o (d))=
    cases(
      k dot 1 plus.o k dot t plus.o dots plus.o k dot t^d & d>=0,
      0 & d<0
    ).
  $
  The Laurent-polynomial calculation is *left to the reader (algebra)*.
  Geometrically, the sheaf axiom on the two displayed opens identifies global
  sections with exactly these compatible pairs, so this computes all sections.
  No Riemann–Roch theorem enters the calculation.
]

#metadata(none) <sup-dv-15>
#example(number: "DV-15", title: "A non-Cartier Weil divisor on the cone")[
  Let $k$ be algebraically closed of characteristic zero and
  $A=k[x,y,z]\/(x y-z^2)$, $X=ops.spec A$. By
  #book-link(<sup-al2-13>)[AL2-13], $X$ is normal and has its unique singular
  point at $idl.m=(x,y,z)$. Let $D=V(x,z)$ with its reduced structure.

  At its generic point, $y$ is a unit and $x=z^2/y$. The chart
  $A_y=k[y,y^(-1),z]$ shows that $z$ is a uniformizer there, whence
  $nu_D(x)=2$. Every height-one prime containing $x$ also contains $z$
  and is therefore $(x,z)$: its quotient is $k[y]$. Thus
  $ops.dv (x)=2D$.

  The ideal $I=(x,z)$ is the ideal attached to the effective Weil divisor
  $D$: in a normal domain it is the set of elements with positive valuation
  at $(x,z)$. At the vertex the classes of $x,z$ are independent in
  $I_idl.m\/idl.m I_idl.m$, of dimension two. If $D$ were Cartier there,
  its effective equation would make this ideal principal, contradicting
  Nakayama. To justify that implication, a rational Cartier equation with
  nonnegative valuations lies in the normal local ring by the intersection
  formula II.6.3A, and its principal ideal is determined by those valuations.
  The independence and the ideal/valuation identification are
  *left to the reader (commutative algebra)*. They can be checked using the
  degree-one terms of the presentation, whose defining relation has degree two.

  Finally $A_x=k[x,x^(-1),z]$ is a UFD, so II.6.2 gives
  $ops.cl (D(x))=0$. The complement has the single prime divisor $D$.
  The divisor-class restriction sequence II.6.5 therefore makes
  $ZZ[D]->ops.cl (X)$ surjective. The equality $ops.dv (x)=2D$ supplies
  the relation $2[D]=0$, while non-Cartierness implies $[D]!=0$, since a
  principal Weil divisor is Cartier. Hence
  $ops.cl (X) simeq ZZ\/2ZZ$.
  The terminal group calculation, a nonzero cyclic group generated by an
  element of order dividing two, is *left to the reader*.
  (Ex. II.6.5(a)~(b), affine surface case)
]

#metadata(none) <sup-dv-16>
#example(number: "DV-16", title: "Two degrees on the product of projective lines")[
  Let $X=sch.p_k^1 times sch.p_k^1$, let $p_1,p_2$ be the projections, and put
  $
    shf.o_X(a,b)=tensor(p_1^*shf.o (a), p_2^*shf.o (b), over: shf.o_X).
  $
  Let $F_1={infinity} times sch.p^1$ and $F_2=sch.p^1 times {infinity}$.
  Pulling back the equations and frames of DV-14 identifies
  $shf.o_X(F_1)=shf.o_X(1,0)$ and $shf.o_X(F_2)=shf.o_X(0,1)$.

  On the four product charts, section coefficients satisfy the independent
  transition identities in $t$ and $s$. Thus, for $a,b>=0$, a basis of global
  sections is $t^i s^j$ with $0<=i<=a$, $0<=j<=b$; if either integer is
  negative there are no nonzero sections. Equivalently these are
  bihomogeneous polynomials of bidegree $(a,b)$ in the two pairs of homogeneous
  coordinates. The coefficient comparison is *left to the reader (algebra)*;
  as in DV-14, sheaf gluing on this cover proves that it exhausts the global
  sections. A nonzero such section defines an effective divisor by DV-2.

  Restriction to $sch.p^1 times {q}$, for a $k$-rational point $q$, gives
  $shf.o (a)$, hence degree $a$; restriction to ${q} times sch.p^1$ gives
  $shf.o (b)$, hence degree $b$. The factor pulled back from the constant
  projection is trivial, and the other restriction is the identity pullback.
  These observations compute the restriction maps on invertible sheaves
  without an intersection pairing.

  The four affine charts are polynomial rings, so $X$ is locally factorial
  and II.6.16 identifies $ops.pic (X)$ with $ops.cl (X)$. Removing $F_1 union F_2$
  leaves $sch.a_k^2$, whose coordinate ring is a UFD. Applying II.6.5
  successively to the two boundary divisors gives a surjection
  $ZZ^2->ops.pic (X)$, $(a,b) mapsto shf.o (a,b)$. The two restriction degrees
  send this pair back to $(a,b)$, proving injectivity. Consequently
  $ops.pic (X) simeq ZZ^2$. Every effective divisor has $a,b>=0$, by the
  section computation applied to its canonical section, and conversely every
  such pair is represented by an effective divisor (including zero).
  (Ex. II.6.1, II.6.5(c), projective surface cases)
]

#exercise(title: "Exercises: rebuild the dictionary")[
  + On the two charts of $sch.p^1$, glue frames by $e_0=t^(-d)e_infinity$.
    Choose a rational section, recover its Cartier equations, and compute
    what changes when the section is multiplied by $t-1$.
  + For the cone divisor $D$ of DV-15, compare the minimal numbers of local
    generators of the ideals of $D$ and $2D$ at the vertex. Explain why
    torsion in $ops.cl (X)$ does not make $D$ Cartier.
  + On a smooth curve, compare a double rational point with two distinct
    rational points. Compute their local Artinian rings, lengths, and degrees;
    explain which data are lost by degree.
  + For $[S:T] mapsto [S^n:T^n]$ on $sch.p^1$, compute the pullbacks of zero
    and infinity and the local ramification indices. Over $RR$, also choose
    a closed point of degree two and check the residue-degree sum in DV-12.
  + For the inseparable point in DV-13, verify directly that base extension
    preserves the Cartier equation while changing its reduced support.
]

Sources: Hartshorne II.6 for the divisor-class dictionary and restriction
sequence; Liu 7.1.18–7.1.19 and 7.1.32 for Cartier classes,
7.1.26–7.1.38 for lengths and pullback, and 7.3.1–7.3.8 for degree.
