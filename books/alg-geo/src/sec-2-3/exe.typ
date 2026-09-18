#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.3, Exercise 3.1
#exercise(title: "Exercise 3.1")[
  Show that $f:X->Y$ is locally of finite type iff, for every affine
  $V=ops.spec B subset.eq Y$, $f^(-1) (V)$ has an affine cover $ops.spec A_i$ with
  every $A_i$ a finitely generated $B$-algebra.
]

// Hartshorne II.3, Exercise 3.2
#exercise(title: "Exercise 3.2 (Quasi-compact Morphisms)")[
  A morphism is quasi-compact if some affine cover $V_i$ of $Y$ has all
  $f^(-1) (V_i)$ quasi-compact. Show this then holds for every affine open
  $V subset.eq Y$.
]

// Hartshorne II.3, Exercise 3.3
#exercise(title: "Exercise 3.3")[
  + Show $f$ is of finite type iff it is locally of finite type and
    quasi-compact.
  + Deduce that over every affine $V=ops.spec B$, $f^(-1) (V)$ has a finite affine
    cover $ops.spec A_i$ with finitely generated $B$-algebras $A_i$.
  + Show that then every affine $ops.spec A subset.eq f^(-1) (V)$ has $A$ finitely
    generated over $B$.
]

// Hartshorne II.3, Exercise 3.4
#exercise(title: "Exercise 3.4")[
  Show $f$ is finite iff for every affine $V=ops.spec B subset.eq Y$,
  $f^(-1) (V)=ops.spec A$ with $A$ a finite $B$-module.
]

// Hartshorne II.3, Exercise 3.5
#exercise(title: "Exercise 3.5 (Quasi-finite Morphisms)")[
  A morphism is quasi-finite if every point fibre is finite.

  + Show finite morphisms are quasi-finite and closed.
  + Give a surjective finite-type quasi-finite morphism that is not finite.
]

// Hartshorne II.3, Exercise 3.6
#exercise(title: "Exercise 3.6 (Function Field)")[
  If $X$ is integral, show the local ring at its generic point is a field,
  denoted $K(X)$, and for every nonempty affine $ops.spec A subset.eq X$ it is
  the fraction field of $A$.
]

// Hartshorne II.3, Exercise 3.7
#metadata(none) <exercise-ii-3-7>
#exercise(title: "Exercise 3.7")[
  Let $f:X->Y$ be dominant, generically finite, and of finite type between
  integral schemes. Show there is a dense open $U subset.eq Y$ such that
  $f^(-1) (U)->U$ is finite. First show $K(X)\/K(Y)$ is finite.
]

#book-link(<sup-rm-5>)[RM-5] treats the separated finite-type integral k-scheme version; it does not replace the full generality of this exercise.

// Hartshorne II.3, Exercise 3.8
#exercise(title: "Exercise 3.8 (Normalization)")[
  For integral $X$, glue $ops.spec overline(A)$ over affine $ops.spec A subset.eq X$,
  where $overline(A)$ is the integral closure in $K(X)$. Show the resulting
  normal integral scheme $overline(X)->X$ is universal for dominant maps
  from normal integral schemes. If $X$ is of finite type over a field, show
  this morphism is finite.
]

// Hartshorne II.3, Exercise 3.9
#exercise(title: "Exercise 3.9 (Topology of a Product)")[
  + Show $sch.a^1_k times_(ops.spec k) sch.a^1_k simeq sch.a^2_k$ and that its point set
    is not the product of the point sets of the factors.
  + Describe $ops.spec k(s) times_(ops.spec k) ops.spec k(t)$.
]

// Hartshorne II.3, Exercise 3.10
#exercise(title: "Exercise 3.10 (Fibres of a Morphism)")[
  + Show $ops.sp (X_y)$ is homeomorphic to $f^(-1) (y)$ with its induced topology.
  + For $X=ops.spec k[s,t]\/(s-t^2)->Y=ops.spec k[s]$, describe the fibres over
    $a!=0$, over $0$, and over the generic point, assuming $k$ algebraically
    closed; observe the nonreduced special fibre and quadratic generic
    residue-field extension.
]

// Hartshorne II.3, Exercise 3.11
#exercise(title: "Exercise 3.11 (Closed Subschemes)")[
  + Show closed immersions are stable under base extension.
  + Show every closed subscheme of $ops.spec A$ is $ops.spec (A\/idl.a)$ for an ideal
    $idl.a subset.eq A$.
  + On a closed subset, show the reduced induced structure is the smallest
    closed subscheme structure.
  + Show every morphism $Z->X$ has a smallest closed subscheme through which
    it factors, its scheme-theoretic image; for reduced $Z$, identify this
    with the reduced structure on the closure of the set-theoretic image.
]

// Hartshorne II.3, Exercise 3.12
#exercise(title: "Exercise 3.12 (Closed Subschemes of Proj)")[
  + If $S->T$ is a surjective graded map, show $ops.proj T->ops.proj S$ is a closed
    immersion.
  + For homogeneous $I subset.eq S$, study $ops.proj (S\/I) subset.eq ops.proj S$ and
    show truncating $I$ in sufficiently high degrees gives the same closed
    subscheme.
]

// Hartshorne II.3, Exercise 3.13
#exercise(title: "Exercise 3.13 (Finite-type Properties)")[
  Prove: closed immersions and quasi-compact open immersions are of finite
  type; finite type is stable under composition and base extension; products
  of finite-type $S$-schemes are finite type; if $X->Y->Z$ has $X->Y$
  quasi-compact and $X->Z$ finite type, then $X->Y$ is finite type; and a
  finite-type scheme over a noetherian scheme is noetherian.
]

// Hartshorne II.3, Exercise 3.14
#exercise(title: "Exercise 3.14")[
  Show the closed points of a scheme of finite type over a field are dense,
  and give an arbitrary scheme for which this fails.
]

// Hartshorne II.3, Exercise 3.15
#exercise(title: "Exercise 3.15 (Geometric Properties)")[
  For finite-type $X\/k$:

  + show irreducibility after an algebraic closure, a separable closure, and
    every field extension are equivalent;
  + show reducedness after an algebraic closure, a perfect closure, and every
    field extension are equivalent;
  + give integral schemes that are not geometrically irreducible and ones
    that are not geometrically reduced.
]

// Hartshorne II.3, Exercise 3.16
#exercise(title: "Exercise 3.16 (Noetherian Induction)")[
  Let a property of closed subsets of a noetherian space hold for $Y$ whenever
  it holds for all proper closed subsets of $Y$. Prove it holds for $X$.
]

// Hartshorne II.3, Exercise 3.17
#exercise(title: "Exercise 3.17 (Zariski Spaces)")[
  A Zariski space is noetherian and every nonempty irreducible closed subset
  has a unique generic point.

  + Show underlying spaces of noetherian schemes are Zariski spaces.
  + Show minimal nonempty closed subsets are single closed points and prove
    the $T_0$ axiom.
  + In an irreducible Zariski space, every nonempty open contains the generic
    point.
  + Describe specialization order: its minimal points are closed points and
    its maximal points are generic points of irreducible components; closed
    sets are stable under specialization and opens under generization.
  + For the functor $t$ of Proposition 2.6, show $t(X)$ is Zariski when $X$
    is noetherian, and $X$ is Zariski iff $X->t(X)$ is a homeomorphism.
]

// Hartshorne II.3, Exercise 3.18
#exercise(title: "Exercise 3.18 (Constructible Sets)")[
  In a Zariski space, define constructible sets as the Boolean algebra
  generated by opens.

  + Show they are exactly finite disjoint unions of locally closed subsets.
  + In an irreducible Zariski space, show a constructible set is dense iff it
    contains the generic point, and then it contains a nonempty open.
  + Show closed sets are exactly constructible sets stable under
    specialization, and similarly for opens and generization.
  + Continuous inverse images preserve constructible sets.
]

// Hartshorne II.3, Exercise 3.19
#exercise(title: "Exercise 3.19 (Chevalley's Theorem)")[
  Prove that a finite-type morphism of noetherian schemes sends constructible
  sets to constructible sets.

  + Reduce to the dominant affine integral case and to the image of $X$.
  + Show that image contains a nonempty open, using the algebraic lemma that
    for $A subset.eq B$ noetherian domains with $B$ finite type over $A$ and
    $0!=b in B$, some $0!=a in A$ makes every map $A->K$ to an algebraically
    closed field with $a$ nonzero extend to $B->K$ with $b$ nonzero.
  + Finish by noetherian induction, and give variety morphisms whose images
    are neither open nor closed.
]

// Hartshorne II.3, Exercise 3.20
#exercise(title: "Exercise 3.20 (Dimension)")[
  For integral finite-type $X\/k$, prove:
  $dim X=dim shf.o_(X,P)$ at closed points;
  $dim X=ops.trdeg_k K(X)$;
  $ops.codim(Y,X)=inf_{P in Y} dim shf.o_(X,P)$;
  $dim Y+ops.codim(Y,X)=dim X$;
  nonempty opens have dimension $dim X$; and every irreducible component of
  $X times_k k'$ has dimension $dim X$.
]

// Hartshorne II.3, Exercise 3.21
#exercise(title: "Exercise 3.21")[
  If $R$ is a DVR containing its residue field and $X=ops.spec R[t]$, show
  parts (a), (d), and (e) of Exercise 3.20 fail for $X$.
]

// Hartshorne II.3, Exercise 3.22
#exercise(title: "Exercise 3.22 (Dimension of Fibres)")[
  Let $f:X->Y$ be dominant between integral finite-type $k$-schemes and put
  $e=dim X-dim Y$.

  + For irreducible closed $Y'$ whose generic point lies in $f(X)$ and a
    component $Z$ of $f^(-1) (Y')$ dominating $Y'$, show
    $ops.codim(Z,X)<=ops.codim(Y',Y)$.
  + Every component of every nonempty fibre has dimension at least $e$.
  + On a dense open $U subset.eq X$, all nonempty fibres have dimension $e$.
  + Show the locus where a fibre component through $x$ has dimension at
    least $h$ is closed; use this to prove Chevalley's theorem that the loci
    ${y | dim X_y=h}$ are constructible and the $h=e$ locus contains a dense
    open subset of $Y$.
]

// Hartshorne II.3, Exercise 3.23
#exercise(title: "Exercise 3.23")[
  For varieties $V,W$ over algebraically closed $k$, show
  $t(V times W) simeq t(V) times_(ops.spec k) t(W)$.
]
