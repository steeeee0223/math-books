#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

// Kempf, Some elementary proofs of basic theorems in the cohomology of
// quasi-coherent sheaves, Rocky Mountain J. Math. 10 (1980), 637--645, §1.
// https://doi.org/10.1216/RMJ-1980-10-3-637
// Dependency order: 3.A and 3.B -> 3.5 -> 3.7.

#lemma(number: "3.A", title: "Kempf's Lemma")[
  Let $X$ be a topological space and let $cal(B)$ be a basis of open
  subsets closed under finite intersections. For $V in cal(B)$, let
  $j_(V):V inclusion("", "") X$ denote the inclusion.
  Let $shf.f$ be an abelian sheaf on $X$ and let $n>=1$ be an integer.
  Suppose that
  $
    H^(q)(V, shf.f|_(V))=0
    quad (V in cal(B), med 0<q<n).
  $
  Then for every $alpha in H^(n)(X, shf.f)$ there is an open covering
  $X=union_(i) V_(i)$, with $V_(i) in cal(B)$, such that the image of $alpha$
  under each map
  $
    H^(n)(X, shf.f)
    to H^(n)(X, j_(V_(i) ast) (shf.f|_(V_(i))))
  $
  is zero. These maps are induced by the natural sheaf morphisms
  $shf.f to j_(V_(i) ast) (shf.f|_(V_(i)))$.
]
#proof[
  _Sketch._

  *(I).* Set up dimension shifting.

  - Induct on $n$. Embed $shf.f$ in an injective abelian sheaf
    $shf.i$ and put $shf.g=shf.i/shf.f$.
  - The sheaf $shf.i$ is flasque
    by _(2.4)_. For an open $V$, write
    $shf.f_(V)=j_(V ast)(shf.f|_(V))$, and similarly for other sheaves.
    These abbreviations are used only in this proof.

  *(II).* The case $n=1$.

  - If $n=1$, lift $alpha$ to $s in Gamma(X, shf.g)$ using the long exact
    sequence and _(2.5)_.
  - The surjection $shf.i to shf.g$ locally lifts $s$;
    refine its lifting cover by members $V in cal(B)$.
  - Put
    $shf.k_(V)=ops.coker(shf.f_(V) to shf.i_(V))$.
  - There is a natural map
    from $0 to shf.f to shf.i to shf.g to 0$ to
    $0 to shf.f_(V) to shf.i_(V) to shf.k_(V) to 0$.
  - The chosen lift on $V$ is a global section of $shf.i_(V)$ lifting the
    image of $s$ in $shf.k_(V)$.
  - Naturality of the connecting map therefore
    kills the image of $alpha$ in $H^(1)(X, shf.f_(V))$.

  *(III).* The case $n>1$.

  - Suppose $n>1$. For every $B in cal(B)$, the hypothesis
    $H^(1)(B, shf.f)=0$ makes
    $0 to shf.f (B) to shf.i (B) to shf.g (B) to 0$ exact.
  - Since $B inter V in cal(B)$, taking sections on these intersections
    shows that
    $
      0 to shf.f_(V) to shf.i_(V) to shf.g_(V) to 0
    $
    is exact as a sequence of sheaves on $X$.
  - Exercise II.1.16(d) makes $shf.i_(V)$ flasque.
  - The connecting maps give
    compatible isomorphisms
    $
      H^(n-1)(X, shf.g) & simeq H^(n)(X, shf.f), \
      H^(n-1)(X, shf.g_(V)) & simeq H^(n)(X, shf.f_(V)).
    $
  - Moreover, $H^(q)(B, shf.g)=H^(q+1)(B, shf.f)=0$ for $0<q<n-1$.
  - Apply the induction hypothesis to the class corresponding to $alpha$
    in $H^(n-1)(X, shf.g)$, and use naturality of these isomorphisms.
]

#lemma(number: "3.B", title: "The Localization Embedding")[
  Let $A$ be a ring, let $M$ be an $A$-module, and put $X=ops.spec A$.
  Suppose $f_(1),dots.c,f_(r) in A$ satisfy
  $X=union_(i=1)^(r) D(f_(i))$. The diagonal localization map gives a
  short exact sequence
  $
    0 to tildeOf(M)
    to bigOPlus(tildeOf(M_(f_(i))), i=1, top: r)
    to shf.g to 0,
  $
  for some $shf.g in cat.qcoh(X)$.
]
#block(breakable: false)[
  #proof[
    _Sketch._

    - Consider the $A$-linear map
      $
        lambda:M to bigOPlus(M_(f_(i)), i=1, top: r), quad
        m mapsto (m/1)_(i=1)^(r).
      $
    - For every prime $idl.p subset A$, some $f_(i)$ lies outside $idl.p$.
      On localizing at $idl.p$, the corresponding component of $lambda$
      is an isomorphism, so $lambda$ is injective.
    - Apply the exact tilde functor of II.5.2(a), use II.5.2(c) for the finite
      direct sum, and take $shf.g=tildeOf(ops.coker lambda)$.
  ]
]

// General form of Hartshorne III.3.5; the proof uses Kempf's lemma.
#theorem(number: "3.5", title: "Cohomology of an Affine Scheme")[
  Let $A$ be any ring and let $X=ops.spec A$. For every quasi-coherent
  $shf.o_(X)$-module $shf.f$,
  $
    H^(i)(X, shf.f)=0 quad "for all" i>0.
  $
]
#proof[
  _Sketch._

  *(I).* Set up the induction.

  - Induct on $n>=1$, simultaneously for all rings $A$ and all
    quasi-coherent sheaves on $ops.spec A$.
  - By II.5.5(a), write
    $shf.f=tildeOf(M)$. Fix $alpha in H^(n)(X, shf.f)$.
  - Every distinguished open $D(f)=ops.spec A_(f)$ is affine, so the
    induction hypothesis supplies the lower-degree vanishings required
    by _(3.A)_ on the basis of distinguished opens.

  *(II).* Use a finite localization cover.

  - Choose a finite subcover $X=union_(i=1)^(r) D(f_(i))$ from the cover
    given by _(3.A)_.
  - By II.5.1(c) and II.5.2(d), the natural maps in that
    lemma identify with the localization maps
    $tildeOf(M) to tildeOf(M_(f_(i)))$ on $X$.
  - Thus $alpha$ maps to zero in the cohomology of their finite direct sum.
  - Use the short exact sequence of _(3.B)_ and its exact cohomology segment
    $
      H^(n-1)(X, shf.g) to H^(n)(X, tildeOf(M))
      to H^(n)(X, bigOPlus(tildeOf(M_(f_(i))), i=1, top: r)).
    $

  *(III).* Kill the class.

  - If $n>1$, the left group is zero by induction.
  - If $n=1$, II.5.6 makes
    the map from the global sections of the middle sheaf of _(3.B)_ onto
    $Gamma(X, shf.g)$ surjective, so its connecting map is zero.
  - In either case $alpha=0$.
]

// General form of Hartshorne III.3.7.
// Stacks Project, Cohomology of Schemes, Lemma 30.3.1.
// The converse uses quasi-coherent ideal sheaves and the affine-cover
// criterion already established in II.2, not flasque quasi-coherent hulls.
#theorem(number: "3.7", title: "Serre's Affineness Criterion")[
  Let $X$ be a quasi-compact scheme. The following conditions are equivalent:

  + $X$ is affine.
  + $H^(q)(X, shf.f)=0$ for every quasi-coherent $shf.o_(X)$-module $shf.f$
    and every $q>0$.
  + $H^(1)(X, shf.j)=0$ for every quasi-coherent sheaf of ideals
    $shf.j subset shf.o_(X)$.
]
#proof[
  _Sketch._

  *(I).* The direct implications.

  - The implication (a) $Rightarrow$ (b) is _(3.5)_, and
    (b) $Rightarrow$ (c) is immediate. Assume (c).

  *(II).* Construct affine principal neighborhoods.

  - For a closed point $x in X$, choose an affine open neighborhood $U$,
    and put $Z=X minus U$.
  - Let $shf.j$ and $shf.j'$ be the quasi-coherent
    ideals defining the reduced closed subschemes on $Z$ and
    $Z union {x}$, respectively, as in Exercise II.3.11.
  - The quotient $shf.j/shf.j'$ is the skyscraper sheaf $k(x)$ at $x$.
  - Since $H^(1)(X, shf.j')=0$, lift $1 in k(x)$ to
    $f in Gamma(X, shf.j) subset Gamma(X, shf.o_(X))$.
  - Then $x in X_(f) subset U$, and $X_(f)$ is the distinguished open
    $D(f|_(U))$ of $U$, hence affine.

  *(III).* Choose a finite principal cover.

  - The union of these affine principal opens contains every closed point.
  - Its closed complement is quasi-compact and, if nonempty, has a closed
    point: quasi-compactness gives a minimal nonempty closed subset by
    the descending-chain intersection argument, and the separation
    property of scheme points makes this subset a singleton.
  - Thus these opens cover $X$; choose finitely many
    $X_(f_(1)),dots.c,X_(f_(r))$.

  *(IV).* Generate the unit ideal.

  - The sheaf map
    $
      shf.o_(X)^(r) to shf.o_(X),quad
      (a_(i))_(i=1)^(r) mapsto sum_(i=1)^(r) f_(i) a_(i)
    $
    is surjective.
  - Its quasi-coherent kernel $shf.k$ has a finite
    filtration obtained by intersecting with the first $i$ summands.
  - Projection onto the $i$th summand identifies each successive quotient
    with a quasi-coherent ideal of $shf.o_(X)$, by II.5.7(i).
  - Condition (c) and the long exact sequences give $H^(1)(X, shf.k)=0$.
  - Consequently, the map on global sections is surjective, so the
    $f_(i)$ generate the unit ideal of $Gamma(X, shf.o_(X))$.
  - Exercise II.2.17(b) now implies that $X$ is affine.
]
