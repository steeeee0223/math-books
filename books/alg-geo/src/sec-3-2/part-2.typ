#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

=== A Vanishing Theorem of Grothendieck

// Stacks Project, Cohomology, Lemma 20.8.2.
#proposition(number: "2.B", title: "Mayer-Vietoris")[
  Let $X=U union V$ be a covering of a topological space by two open
  subsets, and let $shf.f$ be an abelian sheaf on $X$.
  There is a natural long exact sequence, for $q>=0$,
  $
    dots.c & to H^(q)(X, shf.f)
             to H^(q)(U, shf.f) plus.o H^(q)(V, shf.f) \
           & to H^(q)(U inter V, shf.f)
             to H^(q+1)(X, shf.f) to dots.c.
  $
  The map to the cohomology of $U inter V$ is the difference of the
  two restriction maps.
]
#proof[
  _Sketch._

  *(I).* Form the short exact sequences.

  - Choose a flasque resolution $0 to shf.f to sym.cplx(I)$.
  - In each degree, the sheaf gluing axiom and flasqueness give a short
    exact sequence
    $
      0 to Gamma(X, I^(p))
      to Gamma(U, I^(p)) plus.o Gamma(V, I^(p))
      to Gamma(U inter V, I^(p)) to 0.
    $
    The maps are restriction and the difference of restrictions.
  - Surjectivity of the last map follows by extending a section on
    $U inter V$ to $U$.

  *(II).* Pass to cohomology.

  - These sequences form a short exact sequence of
    complexes.
  - Apply its cohomology long exact sequence and _(2.5)_,
    noting that the restrictions of the resolution to $U$, $V$, and
    $U inter V$ remain flasque resolutions.
]

// This form has a direct finite-gluing and dimension-shifting proof.
// It replaces the Cech acyclicity criterion in the dimension argument.
#lemma(number: "2.C", title: "Acyclicity on Quasi-compact Opens")[
  Let $Y$ be a topological space whose quasi-compact open subsets form
  a basis and are closed under finite intersections.
  Let $shf.g$ be an abelian sheaf on $Y$. Suppose that
  $
    Gamma(V, shf.g) to Gamma(U, shf.g)
  $
  is surjective whenever $U subset V$ are quasi-compact open subsets of $Y$.
  Then
  $
    H^(q)(U, shf.g)=0 quad (q>0)
  $
  for every quasi-compact open subset $U subset Y$.
]
#proof[
  _Sketch._

  *(I).* Lift sections on a finite cover.

  - Embed $shf.g$ in an injective sheaf $shf.i$, and put
    $shf.h=shf.i\/shf.g$.
  - For a quasi-compact open $U$, a section of the quotient lifts to
    $shf.i$ on a finite cover by quasi-compact opens $U_(1),dots.c,U_(r)$.

  *(II).* Glue the lifts.

  - Glue the lifts successively. At each step their difference on
    $(U_(1) union dots.c union U_(i-1)) inter U_(i)$ is a section of
    $shf.g$. This intersection is quasi-compact, so the restriction
    hypothesis extends the difference to $U_(i)$; subtract it from the
    new lift before gluing.
  - Hence $Gamma(U, shf.i) to Gamma(U, shf.h)$ is surjective for every
    quasi-compact open $U$.
  - A section of $shf.h$ on $U subset V$ lifts
    to $shf.i (U)$ and then extends to $shf.i (V)$, since $shf.i$ is flasque.
  - Thus the quotient has the same restriction-surjectivity property.

  *(III).* Shift cohomological degree.

  - The long exact sequence first gives $H^(1)(U, shf.g)=0$ and then
    $H^(p+1)(U, shf.g) simeq H^(p)(U, shf.h)$ for $p>0$.
  - Repeat this argument for successive quotients to obtain the result
    by dimension shifting.
]

// Stacks Project, Cohomology, Lemma 20.22.1(2).
// Only this neighborhood-continuity statement is needed, not the general
// theorem on filtered colimits of sheaf cohomology.
#proposition(number: "2.E", title: "Cohomology over Shrinking Neighborhoods")[
  Let $X$ be a quasi-compact, quasi-separated scheme, and let
  $T subset X$ be quasi-compact and stable under generization.
  Let $U subset T$ be quasi-compact and open, put $Z=T minus U$, and set
  $
    W={t in T | exists z in Z, z in overline({t})}.
  $
  Give these subsets their subspace topologies, and let $shf.f$ be an
  abelian sheaf on $T$. For every integer $q>=0$, restriction induces an isomorphism
  $
    ops.colim_(Z subset V) H^(q)(V inter U, shf.f)
    simeq H^(q)(W minus Z, shf.f|_(W minus Z)),
  $
  where $V$ runs through the quasi-compact open neighborhoods of $Z$
  in $T$, with transition maps given by restriction to smaller neighborhoods.
]
#proof[
  _Sketch._

  *(I).* Describe the shrinking neighborhoods.

  - Put $S=W minus Z$ and order the quasi-compact open
    neighborhoods $V$ of $Z$ by reverse inclusion.
  - #supplement-link(<sup-xp-13>)[XP-13] makes $T$, $W$, and $S$ spectral
    and identifies $W$ with the intersection of these neighborhoods. Thus
    $S=inter_(Z subset V)(V inter U)$.

  *(II).* Compare finite data.

  - The finite-data comparison needed for this intersection is that
    sections on a quasi-compact open of $S$, their equalities, and finite
    open covering relations are represented on the corresponding opens
    of $V inter U$ after shrinking $V$.
  - To check it, use finite local representatives and quasi-compact open
    refinements. XP-13(d), applied in $T$ and intersected with the
    quasi-compact open $U$, descends the resulting finite containment
    and covering relations to one neighborhood $V$.

  *(III).* Restrict a flasque resolution.

  - In degree zero this gives
    $
      ops.colim_(Z subset V) Gamma(V inter U, shf.f)
      simeq Gamma(S, shf.f|_(S)).
    $
  - Choose a flasque resolution $0 to shf.f to sym.cplx(I)$ on $T$.
  - The same comparison on quasi-compact opens of $S$ shows that
    $I^(p)|_(S)$ has surjective restrictions between such opens:
    represent a section at one finite stage and extend it there using
    flasqueness of $I^(p)$.
  - By _(2.C)_, these restrictions are acyclic.
    Restriction to $S$ is exact, so they give an acyclic resolution on $S$.

  *(IV).* Pass to higher cohomology.

  - Apply the degree-zero comparison term by term. Filtered colimits of
    abelian groups are exact, hence commute with cohomology of complexes.
  - On each open $V inter U$, _(2.5)_ computes cohomology by the restricted
    resolution; on $S$, use the acyclic resolution and III.1.2.
    This gives the asserted isomorphism in every degree.
]

// Base case for 2.G, using XP-14.
#lemma(number: "2.F", title: "The Zero-dimensional Case")[
  Let $X$ be a quasi-compact, quasi-separated scheme, and let
  $T subset X$ be a quasi-compact subset stable under generization,
  with its subspace topology. If $dim T=0$, the functor
  $Gamma(T, -):cat.ab(T) to cat.ab$ is exact. In particular,
  $
    H^(q)(T, shf.f)=0 quad (q>0)
  $
  for every abelian sheaf $shf.f$ on $T$.
]
#proof[
  _Sketch._

  - Given a surjection of abelian sheaves, a global section
    of the target lifts on an open cover of $T$.
  - #supplement-link(<sup-xp-13>)[XP-13] makes $T$ spectral, and
    #supplement-link(<sup-xp-14>)[XP-14] refines this cover by finitely
    many disjoint opens.
  - The local lifts glue,
    since there are no nonempty overlaps.
  - Thus global sections preserve
    surjections and are exact. Their higher derived functors vanish.
]

// Stacks Project, Cohomology, Proposition 20.22.4(1)--(2).
// Simultaneous induction: XP-13--XP-14, 2.E--2.F, and 2.B give top-degree surjectivity;
// 2.C applied to a truncated injective resolution gives vanishing.
#proposition(number: "2.G", title: "Vanishing and Restriction in Top Degree")[
  Let $X$ be a quasi-compact, quasi-separated scheme, and let
  $T subset X$ be a quasi-compact subset stable under generization,
  with its subspace topology. Suppose that $dim T<=d$ for an integer $d>=0$.
  For every abelian sheaf $shf.f$ on $T$,

  + $H^(q)(T, shf.f)=0$ for every $q>d$.
  + The restriction map
    $
      H^(d)(T, shf.f) to H^(d)(U, shf.f)
    $
    is surjective for every quasi-compact open subset $U subset T$.
]
#proof[
  _Sketch._

  *(I).* Start the induction.

  - Induct on $d$, simultaneously for all subspaces $T$ in
    the statement.
  - Empty subspaces are immediate. For $d=0$, use _(2.F)_.
  - By #supplement-link(<sup-xp-14>)[XP-14], a quasi-compact open of $T$
    is also closed, so a section
    on it extends by zero to $T$. This also proves the restriction assertion.

  *(II).* Restriction in top degree.

  - Let $d>=1$ and first prove (b). For a quasi-compact open $U subset T$,
    put $Z=T minus U$ and let $W$ be its generizations in $T$, as in _(2.E)_.
  - By #supplement-link(<sup-xp-13>)[XP-13(c)], $W minus Z$ is again
    quasi-compact and stable under generization in $X$.
  - Every strict specialization chain in $W minus Z$ extends by a point
    of $Z$ specializing from its last point. By
    #supplement-link(<sup-xp-4>)[XP-4], its length is at most $d-1$,
    so $dim(W minus Z)<=d-1$.
  - Given $xi in H^(d)(U, shf.f)$, its restriction to $W minus Z$ is zero:
    this subspace has dimension at most $d-1$, so induction applies.
  - By _(2.E)_, there is a quasi-compact open $V$ containing $Z$ such that
    $xi|_(V inter U)=0$. Since $T=U union V$, exactness in _(2.B)_ lifts
    the pair $(xi,0)$ to $H^(d)(T, shf.f)$.

  *(III).* Deduce vanishing.

  - To deduce (a), choose an injective resolution $shf.f to sym.cplx(I)$,
    and put $shf.g=ops.ker(I^(d) to I^(d+1))$.
  - For each quasi-compact
    open $U subset T$, the truncated resolution gives exact rows
    $
      Gamma(T, I^(d-1)) & to Gamma(T, shf.g)
                          to H^(d)(T, shf.f) to 0, \
      Gamma(U, I^(d-1)) & to Gamma(U, shf.g)
                          to H^(d)(U, shf.f) to 0.
    $
  - The first and third restriction maps are surjective, by flasqueness
    and (b). A diagram chase makes $Gamma(T, shf.g) to Gamma(U, shf.g)$
    surjective.
  - This also gives surjectivity between any two
    quasi-compact opens, by first extending to $T$.
  - Lemma _(2.C)_ makes $shf.g$ acyclic on these opens.
  - Therefore
    $
      0 to shf.f to I^(0) to dots.c to I^(d-1) to shf.g to 0
    $
    is an acyclic resolution of length $d$. By III.1.2 it computes
    $H^(q)(T, shf.f)$, which vanishes for $q>d$.
]

// The case T=X of 2.G. The extension to qcqs schemes is due to Scheiderer.
#theorem(number: "2.7", title: "Grothendieck Vanishing")[
  Let $X$ be a quasi-compact, quasi-separated scheme with $dim X<=d$
  for an integer $d>=0$. Then
  $
    H^(q)(X, shf.f)=0 quad (q>d)
  $
  for every abelian sheaf $shf.f$ on $X$.
]
#proof[
  _Sketch._

  - Take $T=X$ in _(2.G)(a)_. The whole space is quasi-compact
    and stable under generization, so all its hypotheses hold.
]
