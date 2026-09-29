#import "@preview/theorion:0.6.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *
#import "proof-layout.typ": proof

#import "environments.typ": supplement-numbering, theorem, lemma, corollary, definition, proposition, example, remark
#supplement-numbering("LP")

== LP — A Locality Calculus for Morphisms <sup-lp>

Many definitions in algebraic geometry begin with a property of a ring map
$A -> B$ and then pass to affine charts.  The passage rests on three standard
methods: induction over affine open covers, criteria involving the whole
inverse image of an affine open, and criteria involving all affine pairs.
The letters below abbreviate the restriction and gluing operations used in
these arguments.

*Reading route.* After #book-link(<text-ii-2>)[II.2], read
#book-link(<sup-xl>)[XL-1\~XL-7] and then LP-1\~LP-15 for the locality framework.
The whole-inverse-image argument uses the affineness criterion of
#supplement-link(<sup-xl-7>)[XL-7]. Ring-level BC is a tensor-product
condition; the scheme-level BC conclusions require the fiber products of
#book-link(<text-ii-3>)[II.3, Theorem 3.3]. Read the finite-type and finite
cases alongside II.3. Revisit the diagonal and universal-closedness cases
with #book-link(<text-ii-4>)[II.4]; the integral GS proof also uses the
additional characterization of integral morphisms as affine and universally
closed. The affine closed-immersion dictionary is proved in
#supplement-link(<sup-cs-1>)[CS-1] using II.5.9\~5.10. Flatness and faithful flatness
require their stated module-theoretic criteria. See the
#book-link(<sup-roadmap>)[reading roadmap] for these separate dependencies.

=== Ring-local conditions

#definition(key: "sup-lp-1", title: "The conditions BC, T, and S")[

  Let $cal(P)$ be a property invariant under isomorphisms of ring
  maps. The following are preservation conditions:

  - *(BC), Base-change stability.* For every $A$-algebra $A'$, one has
    $ cal(P)(A -> B) Rightarrow cal(P)(A' -> tensor(B, A', over: A)). $
  - *(T), Target localization.* For every $f in A$, one has
    $cal(P)(A -> B) Rightarrow cal(P)(A_f -> B_f)$.
  - *(S), Source localization.* For every $g in B$, one has
    $cal(P)(A -> B) Rightarrow cal(P)(A -> B_g)$.

  Note that source and target in the letters S and T, respectively, refer to the scheme map $ops.spec B -> ops.spec A$, not to the ring map.
]

#definition(key: "sup-lp-2", title: "Gluing conditions")[

  All covers in these conditions are finite distinguished covers.

  - *(GS), Source gluing.* If $g_1, dots, g_n in B$ generate the unit ideal and
    $cal(P)(A -> B_(g_i))$ holds for every $i$, then $cal(P)(A -> B)$ holds.
  - *(GT), Target gluing.* If $f_1, dots, f_n in A$ generate the unit ideal and
    $cal(P)(A_(f_i) -> B_(f_i))$ holds for every $i$, then $cal(P)(A -> B)$ holds.
]

#definition(key: "sup-lp-3", title: "Principal-target Extension")[
  - *(PL), Principal-target extension,* is the following compatibility condition: if $a in A$ maps to a unit in an $A$-algebra $C$, then $ cal(P)(A_a -> C) Rightarrow cal(P)(A -> C). $ It follows, for example, when every principal localization $A -> A_a$ has $cal(P)$ and $cal(P)$ is stable under composition.
]

#remark(key: "sup-lp-4", title: "PL is an optional way to prove GT")[
  + *Examples of PL.* Finite type, finite presentation, and flatness satisfy PL: the principal
    localization $A -> A_a$ has the same property, and that property is stable
    under composition.

  + *Deriving GT.* If GS and PL hold, then GT follows.  Indeed, from
    $cal(P)(A_(a_i) -> B_(a_i))$, PL gives $cal(P)(A -> B_(a_i))$; the images of the
    $a_i$ generate the unit ideal of $B$, so GS gives $cal(P)(A -> B)$.
]

#proposition(key: "sup-lp-5", title: "Base Change Contains Target Localization")[

  Every property satisfying BC satisfies T.
]

#proof[
  For $f in A$, the canonical localization map identifies $tensor(B, A_f, over: A)$ with $B_f$ (Check!). Applying BC to $A->A_f$ gives T.
]

=== From rings to affine charts

Let $f:X -> Y$ be a morphism.  An *affine pair for* $f$ means affine opens
$U=ops.spec B subset X$ and $V=ops.spec A subset Y$ such that
$U subset f^(-1)(V)$.  The restriction $U -> V$ corresponds to a ring map
$A -> B$.

#proposition(key: "sup-lp-6", title: "Affine Locality Principle")[
  Suppose $cal(P)$ satisfies T and S.

  Let $V_i=ops.spec A_i$ be an affine cover of $Y$, and let $U_(i j)=ops.spec B_(i j)$ be an affine cover of $f^(-1)(V_i)$.
  Assume that every chart map $A_i -> B_(i j)$ has $cal(P)$. Then, for every $a in A_i$ and every $g in (B_(i j))_a$, the refined chart map $ (A_i)_a -> ((B_(i j))_a)_g $ also has $cal(P)$.

  Geometrically, this is the map from the principal open $D(g)$ in
  $U_(i j) inter f^(-1)(D(a))$ to the principal open $D(a) subset V_i$.
]

#proof[

  Start with a chart $U=ops.spec B -> V=ops.spec A$ having $cal(P)$.

  + *Restrict the target.* Restricting
    the target to $D(a) subset V$ replaces its ring map by
    $A_a -> B_a$, which has $cal(P)$ by T.

  + *Refine the source.* A principal affine refinement of the
    source then has coordinate ring $(B_a)_g$ for some $g in B_a$, and
    $A_a -> (B_a)_g$ has $cal(P)$ by S.  These are precisely the ring maps attached
    to principal refinements of the original affine pair.
]

#proposition(key: "sup-lp-7", title: "Affine Communication Lemma for Fixed Target")[

  Let $f:X -> ops.spec A$ be a morphism. Suppose $cal(P)$ satisfies S and GS.
  If $X$ has an affine cover $U_i=ops.spec B_i$ such that every $A -> B_i$ has $cal(P)$, then $A -> Gamma(U, shf.o_X)$ has $cal(P)$ for every affine open $U subset X$.
]

#proof[

  Put $U=ops.spec B$.

  + *Choose simultaneous distinguished neighborhoods.* For $x in U inter U_i$, choose a neighborhood which is distinguished in both affine opens:
    $
      x in W = D_U\(g) = D_(U_i)(h).
    $
    To construct such a neighborhood, first choose $x in D_U\(a) subset U inter U_i$, then $x in D_(U_i)(h) subset D_U\(a)$.  The restriction of $h$ to $D_U\(a)$ has the form $c/a^n$, so $D_(U_i)(h)=D_U\(a c)$.

  + *Restrict the known property.* By S applied in $U_i$, the map $A -> Gamma(W, shf.o_X)$ has $cal(P)$.
    Isomorphism invariance identifies this with $A -> B_g$.

  + *Glue on the chosen affine open.* These $W$ cover
    $U$; quasi-compactness selects finitely many, and their defining elements
    generate the unit ideal of $B$.  GS gives $cal(P)(A -> B)$.

    The simultaneous distinguished neighborhood is essential: mere inclusion
    $D_U\(g) subset U_i$ does not make $g$ a section on $U_i$.
]

#proposition(key: "sup-lp-8")[
  Let $cal(P)$ be a property of ring maps.  Then following
  two conditions are equivalent:

  + $cal(P)$ satisfies S and GS.
  + For every morphism $X -> ops.spec A$ and every affine cover
    $U_i=ops.spec B_i$ of $X$,
    #align(center)[
      $cal(P)(A -> B_i)$ for every $i$ $=>$ $cal(P)(A->B)$ for every affine open $U=ops.spec B subset X$.
    ]

  In other words, over a fixed affine target $ops.spec A$, checking
  $cal(P)$ on one affine cover of $X$ is enough to check it on every affine
  open of $X$.
]

#proof[

  - $(Rightarrow)$ Apply the preceding proposition.
  - $(Leftarrow)$
    + *Necessity of S.* For S, take $X=ops.spec B$ with its one-member cover, and apply communication to $D(g) subset X$.
    + *Necessity of GS.* For GS, cover $ops.spec B$ by the given $D(g_i)$ and apply communication to the affine open $X$ itself.
]

#proposition(key: "sup-lp-9", title: "Strong Affine Locality from Ring-Local Conditions")[

  Suppose $cal(P)$ satisfies T, S, GS, and GT.

  + *Affine pairs.* If one system of affine charts for
    $f:X -> Y$ has $cal(P)$, then the ring map associated with every affine pair for
    $f$ has $cal(P)$.  In this situation, the resulting morphism property is *strongly
    affine local*.

  + *Locality.* It is Zariski local on both source and target.
]

#proof[

  For an affine target $V=ops.spec A$, we let the property $cal(H)$ be that
  #align(center)[
    $cal(H)(V) :=$ every affine open
    $U=ops.spec B subset f^(-1)(V)$ has $cal(P)(A -> B)$.
  ]

  + *Start on the given target cover.* S and GS give $cal(H)(V_i)$ on each member of the original target
    cover, by fixed-target communication.

  + *Restrict the target.* $cal(H)(V)$ implies $cal(H)(D(a))$.  If $U=ops.spec B$ lies over $D(a)$,
    then $cal(P)(A -> B)$ holds and the image of $a$ is a unit in $B$.  T and
    $B_a simeq B$ give $cal(P)(A_a -> B)$.

  + *Glue over a distinguished target cover.* Suppose the $D(a_i)$ cover $V$ and $cal(H)(D(a_i))$ holds.  For any
    affine $U=ops.spec B subset f^(-1)(V)$, the opens
    $U inter f^(-1)(D(a_i))=ops.spec B_(a_i)$ give
    $cal(P)(A_(a_i) -> B_(a_i))$.  GT gives $cal(P)(A -> B)$, hence $cal(H)(V)$.

  + *Pass to every affine target.* The second step permits restriction to a distinguished open of any affine
    target on which $cal(H)$ holds, and the third glues over a finite distinguished
    cover.  Every affine open is quasi-compact, so any affine cover of it has a
    finite refinement by distinguished opens.  Starting from the original
    affine target cover and applying these two operations therefore proves
    $cal(H)(V)$ for every affine open $V subset Y$.  This is precisely the
    assertion about every affine pair.

  + *Check locality on both sides.*
    + Restriction to an open source or target preserves the all-affine-pairs condition.
    + For source gluing, restrict to an affine target, refine the source cover by affine opens, and use fixed-target communication.
    + For target gluing, refine the target cover by affine opens and repeat the distinguished-open induction above.

    Thus the condition is local on both
    source and target.
]

=== Locality directly on schemes

Ring-local conditions describe affine charts.  For a property $cal(Q)(f)$ of
scheme morphisms, locality on an arbitrary open cover is expressed directly at
scheme level.

#definition(key: "sup-lp-10", title: "Zariski Locality")[

  Let $cal(Q)$ be a property of scheme morphisms and let $f:X->Y$.

  - $cal(Q)$ is *Zariski local on the source* if, for every open cover
    $cov(U_i, "")$ of $X$,
    $
      cal(Q)(f) "if and only if" cal(Q)(U_i->Y) "for every" i.
    $

  - $cal(Q)$ is *Zariski local on the target* if, for every open cover
    $cov(V_j, "")$ of $Y$,
    $
      cal(Q)(f) "if and only if" cal(Q)(f^(-1)(V_j)->V_j) "for every" j.
    $

  - A property $cal(R)$ of schemes is *Zariski local* if, for every open cover $cov(U_i, "")$ of $X$,
  $
    cal(R)(X) "if and only if" cal(R)(U_i) "for every" i.
  $
  This is the scheme-only version of locality on the source; there is no
  target until the property is made relative.
]

#corollary(key: "sup-lp-11")[
  Let $cal(Q)$ be a property of scheme morphisms.

  + The following are equivalent:
    + $cal(Q)$ is Zariski local on the source.
    + $cal(Q)$ satisfies both source implications:
      + *(RS), restriction:* $cal(Q)(f)$ implies $cal(Q)(U->Y)$ for every open
        $U subset X$.
      + *(GSS), gluing:* if $X=union_i U_i$ and every $U_i->Y$ has $cal(Q)$,
        then $f$ has $cal(Q)$.

  + The following are equivalent:
    + $cal(Q)$ is Zariski local on the target.
    + $cal(Q)$ satisfies both target implications:
      + *(RT), restriction:* $cal(Q)(f)$ implies
        $cal(Q)(f^(-1)(V)->V)$ for every open $V subset Y$.
      + *(GTT), gluing:* if $Y=union_j V_j$ and every
        $f^(-1)(V_j)->V_j$ has $cal(Q)$, then $f$ has $cal(Q)$.

  + Let $cal(R)$ be a property of schemes.  The following are equivalent:
    + $cal(R)$ is Zariski local.
    + $cal(R)$ satisfies both implications:
      + *restriction:* $cal(R)(X)$ implies $cal(R)(U)$ for every open
        $U subset X$;
      + *gluing:* if $X=union_i U_i$ and every $U_i$ has $cal(R)$, then $X$
        has $cal(R)$.
]

#proof[
  For a fixed open cover, the forward implication in LP-10 restricts the
  property to every member, and the reverse implication glues the restricted
  properties.  To obtain restriction to an arbitrary open $U subset X$, apply
  the forward implication to the cover consisting of $U$ and $X$; for an
  arbitrary open $V subset Y$, use the cover consisting of $V$ and $Y$.
  The same argument applies to a property of schemes.  Conversely, restriction
  followed by gluing gives the equivalence in LP-10 for every open cover.
]

=== From ring properties to scheme properties

#corollary(key: "sup-lp-12", title: "Source-local Affine-Pair Criterion")[

  Let $cal(P)$ be a ring property that respects isomorphisms and satisfies S and GS.  Define the
  corresponding property $cal(Q)$ of a morphism $f:X->Y$ by requiring
  $cal(P)(A->B)$ for every affine pair
  $ops.spec B subset X$ and $ops.spec A subset Y$ of $f$.

  Let $X=union_r X_r$ be any open cover.  The following are equivalent:

  - $f$ has $cal(Q)$.
  - Every restriction $X_r->Y$ has $cal(Q)$.
  - For every affine open $V=ops.spec A subset Y$, the inverse image
    $f^(-1)(V)$ has an affine cover
    $U_j=ops.spec B_j$ such that every $A->B_j$ has $cal(P)$.

  Hence $cal(Q)$ is Zariski local on the source.
]

#proof[
  + *Restrict to the source cover.* Every affine pair for $X_r->Y$ is also an
    affine pair for $f$, so the first condition implies the second.

  + *Produce affine charts over each affine target.* Assume the second
    condition.  For $V=ops.spec A subset Y$, the opens
    $X_r inter f^(-1)(V)$ cover $f^(-1)(V)$.  Refine each of them by affine
    opens $U_j=ops.spec B_j$.  Each $U_j->V$ is an affine pair for
    $X_r->Y$, so its coordinate map $A->B_j$ has $cal(P)$.  This proves the
    third condition.

  + *Communicate across an affine source cover.* Assume the third condition,
    and let $U=ops.spec B subset f^(-1)(V)$ be an arbitrary affine pair, with
    $V=ops.spec A$.  Apply #supplement-link(<sup-lp-7>)[LP-7] to
    $f^(-1)(V)->V$ and the asserted affine cover of $f^(-1)(V)$.  It gives
    $cal(P)(A->B)$, proving the first condition.  LP-11 now gives source
    locality.
]

#corollary(key: "sup-lp-13", title: "Whole-Inverse-Image Criterion")[

  Let $cal(P)$ be a ring property that respects isomorphisms and satisfies T and GT.  Define the
  corresponding property $cal(Q)$ of a morphism $f:X->Y$ by requiring
  that, for every affine open $V=ops.spec A subset Y$,

  - $f^(-1)(V)$ is affine, say $f^(-1)(V)=ops.spec B$; and
  - the ring map $A->B$ has $cal(P)$.

  Let $Y=union_i V_i$ be any affine open cover, with
  $V_i=ops.spec A_i$.  The following are equivalent:

  - $f$ has $cal(Q)$.
  - Every restriction $f^(-1)(V_i)->V_i$ has $cal(Q)$.
  - For every $i$, the whole inverse image is affine,
    $f^(-1)(V_i)=ops.spec B_i$, and $A_i->B_i$ has $cal(P)$.

  Hence $cal(Q)$ is Zariski local on the target.  If $cal(P)$ also satisfies
  BC, then $cal(Q)$ is stable under base change.
]

#proof[
  + *Restriction to the cover.* The first condition implies the second because
    every affine open of $V_i$ is also an affine open of $Y$.  The second
    condition implies the third by taking the affine target $V_i$ itself.

  + *Recover the property from one affine target cover.* Assume the third
    condition.  Restricting $V_i=ops.spec A_i$ to a distinguished open
    $D(a)$ replaces its whole inverse image by $ops.spec (B_i)_a$ and its ring
    map by $(A_i)_a->(B_i)_a$; T preserves $cal(P)$.

    Now let $V=ops.spec A subset Y$ be arbitrary.  Every point of
    $V inter V_i$ has a neighborhood that is distinguished in both affine
    opens, say $D_V(a_k)=D_(V_i)(c_k)$; this is the simultaneous distinguished
    neighborhood construction used in LP-7.  Quasi-compactness of $V$ selects
    finitely many such neighborhoods covering $V$.  Their whole inverse images
    are affine by the preceding paragraph.  The pulled-back sections $a_k$
    generate the unit ideal and have those affine inverse images as their
    nonvanishing loci, so #supplement-link(<sup-xl-7>)[XL-7] makes $f^(-1)(V)$ affine,
    say $ops.spec B$.  The restricted coordinate maps are
    $A_(a_k)->B_(a_k)$ and have $cal(P)$; GT gives $cal(P)(A->B)$.  Thus the
    first condition holds.

  + *Base change.* If $ops.spec A'->ops.spec A$ is an affine base change, then
    $ops.spec B->ops.spec A$ pulls back to
    $ops.spec tensor(B, A', over: A)->ops.spec A'$.  BC gives the required ring
    property.  Target locality glues these affine calculations.
]

#corollary(key: "sup-lp-14", title: "Affine-Pair Criterion")[

  Let $cal(P)$ be a ring property that respects isomorphisms and satisfies T, S, GS, and GT.  Define
  the corresponding property $cal(Q)$ by requiring
  $cal(P)(A->B)$ for every affine pair
  $ops.spec B subset X$ and $ops.spec A subset Y$ of $f:X->Y$.

  Choose any source cover $X=union_r X_r$, any target cover
  $Y=union_s Y_s$, and any affine atlas
  $
    Y=union_i V_i, quad V_i=ops.spec A_i,
    quad f^(-1)(V_i)=union_j U_(i j), quad U_(i j)=ops.spec B_(i j).
  $
  The following are equivalent:

  - $f$ has $cal(Q)$.
  - Every restriction $X_r->Y$ has $cal(Q)$.
  - Every restriction $f^(-1)(Y_s)->Y_s$ has $cal(Q)$.
  - Every chart map $A_i->B_(i j)$ has $cal(P)$.
  - The ring map of every affine pair for $f$ has $cal(P)$.

  Thus $cal(Q)$ is strongly affine local and Zariski local on both source and
  target.
]

#proof[
  The first and last conditions are equivalent by the definition of
  $cal(Q)$.  LP-9 shows that the condition on one affine atlas is
  equivalent to the condition on every affine pair.  It also proves that
  $cal(Q)$ is Zariski local on both source and target.  Applying LP-10
  to the chosen source and target covers gives the second and third
  equivalences.
]

#remark(key: "sup-lp-15", title: "Maximum Local Reduction")[
  Use the strongest row whose hypotheses are known.

  #table(
    columns: (1.25fr, 1.15fr, 1.15fr, 2.5fr),
    align: (left, center, center, left),
    inset: 4pt,
    table.header([*Available data*], [*Source cover*], [*Target cover*], [*Smallest test objects*]),
    [A scheme property $cal(R)$], [if restriction and gluing hold], [not applicable], [open subschemes],
    [A morphism property $cal(Q)$], [if RS and GSS], [if RT and GTT], [restricted morphisms over open subsets],
    [A ring property $cal(P)$ with S and GS],
    [$checkmark$],
    [not in general],
    [affine source charts over each affine target],

    [A ring property $cal(P)$ with T and GT], [not in general], [$checkmark$], [whole inverse images of affine targets],
    [A ring property $cal(P)$ with T, S, GS, and GT], [$checkmark$], [$checkmark$], [arbitrary affine pairs],
  )
]
=== Ring-property case studies

==== Finite type

#definition(key: "sup-lp-16", title: "Finite Type Ring Map")[
  A ring map $A -> B$ is *of finite type* if
  $B=A[b_1, dots, b_n]$ for finitely many elements of $B$.
]

#proposition(key: "sup-lp-17", title: "Locality Profile: Finite Type")[
  Finite type satisfies BC, T, S, GS, and GT.
]

#proof[

  + *BC and T.* If $B$ is generated over $A$ by $b_1,dots,b_n$, then
    $tensor(B, A', over: A)$ is generated over $A'$ by the elements
    $b_j tensor 1$.  This proves BC and hence T.

  + *S and PL.* A principal
    localization is generated by one inverse; together with composition
    stability this gives S and PL.

  + *Source gluing.* For GS, choose coefficients $c_i$
    with $sum_i c_i g_i=1$ and let $C$ be the $A$-subalgebra generated by
    the $g_i$, the $c_i$, and numerators of finite generating sets for the
    $B_(g_i)$.  For $b in B$, clearing denominators gives
    $g_i^(n_i) b in C$.  The powers $g_i^(n_i)$ still generate the unit ideal
    in $C$, so $b in C$.  Hence $C=B$.

  + *Target gluing.* Finally, given a distinguished target
    cover, PL converts each $cal(P)(A_(a_i) -> B_(a_i))$ into
    $cal(P)(A -> B_(a_i))$, and GS then gives $cal(P)(A -> B)$.  Thus GT holds.
]

#corollary(key: "sup-lp-18", title: "Locally Finite-type Morphisms")[
  The corresponding chartwise property is *locally of finite type*.

  + *Locality and base change.*

    - strongly affine local;
    - Zariski local on the source;
    - Zariski local on the target;
    - stable under base change.

  + *Important property.* A morphism is of finite type $arrow.double.l.r$ it is locally
    of finite type and quasi-compact.
]

#proof[

  + *Affine locality.* Apply #supplement-link(<sup-lp-14>)[LP-14] to the ring
    property of the preceding proposition.  It identifies the condition on one
    affine atlas with the condition on every affine pair and gives Zariski
    locality on both source and target.

  + *Base change.* On affine pairs, base change is the tensor-product construction,
    so BC gives stability under base change and locality glues the result.

  + *Finite type implies quasi-compactness.* If $f$ is of finite type, the finitely many source charts in its defining
    affine atlas show that inverse images of affine opens are quasi-compact.

  + *Quasi-compactness gives a finite atlas.* Conversely, if $f$ is quasi-compact and locally of finite type, cover the
    inverse image of an affine target by finite-type affine charts and use
    quasi-compactness to retain finitely many of them.  This is precisely the
    finite atlas required in the definition of a finite-type morphism.
]

==== Finite presentation

#definition(key: "sup-lp-19", title: "Finite Presentation Ring Map")[
  A ring map $A -> B$ is *of finite presentation* if
  $B simeq A[x_1, dots, x_n]\/ideal((r_1, dots, r_m))$ for finite lists of
  generators and relations.
]

#proposition(key: "sup-lp-20", title: "Locality Profile: Finite Presentation")[
  Finite presentation satisfies BC, T, S, GS, and GT.
]

#proof[

  + *BC and T.* Tensoring a finite list of generators and relations with an $A$-algebra
    gives a finite presentation after base change, so BC and T hold.

  + *S and PL.* The
    presentation
    $A_a simeq A[t]\/ideal((a t-1))$, together with composition stability,
    gives S and PL.

  + *Source gluing.* For GS, first apply finite-type GS, then choose a surjection from a
    polynomial algebra in finitely many variables onto $B$.  Its kernel must be
    shown finitely generated.  Lifts of the $g_i$ need not generate the unit
    ideal in the polynomial algebra, so choose lifts of a relation
    $sum_i c_i g_i=1$ and impose the single relation
    $sum_i tilde(c)_i tilde(g)_i-1$.  In the resulting finitely presented
    intermediate algebra the lifted distinguished opens cover.  The localized
    kernels are finitely generated by the local finite presentations.  Clearing
    denominators in finite generating sets and using the unit-ideal relation
    then gives finitely many generators of the global kernel.  Thus GS holds.

  + *Target gluing.* As in the finite-type case, GS and PL imply GT.

]

#corollary(key: "sup-lp-21", title: "Locally Finite-presentation Morphisms")[
  The corresponding chartwise property is *locally of finite presentation*.

  + *Locality and base change.*

    - strongly affine local;
    - Zariski local on the source;
    - Zariski local on the target;
    - stable under base change.
]

#proof[
  Apply #supplement-link(<sup-lp-14>)[LP-14] to the ring property in LP-20: its T,
  S, GS, and GT conditions give independence of the affine atlas and locality
  on both source and target. On affine pairs, a base change replaces the
  coordinate algebra by its tensor product, so LP-20's BC condition applies.
  The affine-cover comparison then gives stability for arbitrary scheme base
  changes, exactly as in LP-18.
]

==== Finite

#definition(key: "sup-lp-22", title: "Finite Ring Map")[
  A ring map $A -> B$ is *finite* if $B$ is a finitely generated $A$-module.
]

#proposition(key: "sup-lp-23", title: "Locality Profile: Finite")[
  Finite satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[

  + *BC and T.* A finite set of $A$-module generators of $B$ tensors to a finite set of
    $A'$-module generators after any base change $A -> A'$, proving BC and
    hence T.

  + *Target gluing.* For GT, lift finite generating sets from the localizations
    $B_(a_i)$ and clear denominators.  For each $b in B$, a power
    of each covering element times $b$ lies in the span of these lifts;
    the unit-ideal condition then puts $b$ itself in that span.

  + *Source gluing.* GS follows from integral GS proved below and finite-type GS, using
    the equivalence of module-finiteness with integrality plus finite type
    (Check!).

  + *Failure of source localization.* See
    #supplement-link(<sup-lp-37>)[LP-37].
]

#corollary(key: "sup-lp-24", title: "Finite Morphisms")[
  + *Affine criterion.* A morphism $f:X -> Y$ is finite if and only if, for
    every affine open $V=ops.spec A subset Y$, the whole inverse image is
    $f^(-1)(V)=ops.spec B$ with $A -> B$ finite.

  + *Target locality and base change.*

    - checkable on any affine open cover of the target;
    - Zariski local on the target;
    - stable under base change.

  + *Source locality.* It fails to be:

    - Zariski local on the source;
    - strongly affine local on arbitrary affine pairs.
]

#proof[

  + *Target locality.* Apply #supplement-link(<sup-lp-13>)[LP-13] to ring
    finiteness, using T and GT from the preceding proposition.  This proves
    that the criterion may be checked on one affine cover of the target or on
    every affine target.

  + *Base change.* The BC clause of LP-13 transports ring-level BC from the
    preceding proposition to schemes.

  + *Failure of source locality.* The example in
    #supplement-link(<sup-lp-37>)[LP-37] is both an open-source restriction and an
    affine pair for the identity of $ops.spec k[t]$. It therefore disproves
    source locality and strong affine locality.
]

==== Integral

#definition(key: "sup-lp-25", title: "Integral Ring Map")[
  A ring map $A -> B$ is *integral* if every $b in B$ satisfies a monic
  polynomial with coefficients in $A$.
]

#proposition(key: "sup-lp-26", title: "Locality Profile: Integral")[
  Integral satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[

  + *BC and T.* A monic equation remains monic after extension of scalars, which proves BC
    and hence T.

  + *Target gluing.* For GT, clear denominators in local monic equations.  A power
    of each covering element times a given
    $b in B$ belongs to the integral closure of $A$ in $B$; gluing membership
    in this $A$-submodule shows that $b$ belongs to the integral closure.

  + *Source gluing.* For GS, use the affine characterization that a morphism is integral if and
    only if it is affine and universally closed.  If finitely many $D(g_i)$ cover
    $ops.spec B$ and their maps to $ops.spec A$ are integral, these maps are
    universally closed.  After any base change, the image of a closed subset
    of the whole source is the finite union of its images from the $D(g_i)$;
    each is closed.  Hence the whole affine morphism is universally closed
    and therefore integral.  This argument uses a finite distinguished cover;
    it does not assert gluing over arbitrary open covers of the source.

  + *Failure of source localization.* See
    #supplement-link(<sup-lp-37>)[LP-37].
]

#corollary(key: "sup-lp-27", title: "Integral Morphisms")[
  + *Affine criterion.* A morphism is integral if and only if inverse images of affine targets are
    affine and induce integral ring maps.

  + *Target locality and base change.* It is:

    - checkable on any affine open cover of the target;
    - Zariski local on the target;
    - stable under base change.

  + *Source locality.* It fails to be:

    - Zariski local on the source;
    - strongly affine local on arbitrary affine pairs.
]

#proof[

  + *Target locality and base change.* Apply #supplement-link(<sup-lp-13>)[LP-13]
    with T and GT for integral ring maps.  It gives the stated
    every-affine-target criterion and target locality; its BC clause gives
    stability under base change.

  + *Failure of source locality.* The open restriction in
    #supplement-link(<sup-lp-37>)[LP-37] is also an affine pair for the identity.
    It disproves source locality and strong affine locality.
]

==== Surjective

#definition(key: "sup-lp-28", title: "Surjective Ring Map")[
  A ring map $phi:A->B$ is *surjective* if every element of $B$ is the
  image of an element of $A$. Equivalently, the canonical map
  $
    A\/ops.ker(phi)->B, quad a+ops.ker(phi) mapsto phi(a),
  $
  is an isomorphism. Thus the quotient description must identify $phi$
  with the quotient map; an abstract ring isomorphism $B simeq A\/I$
  alone does not characterize the given map $phi$.
]

#proposition(key: "sup-lp-29", title: "Locality Profile: Surjective")[
  Surjectivity satisfies BC, T, and GT, but it satisfies neither S nor GS.
]

#proof[

  + *BC and T.* Every tensor is a sum of pure tensors.  If $A -> B$ is surjective, lift the
    $B$-entry of each pure tensor to $A$; this proves that the base-changed map
    is surjective.  Thus BC, and hence T, holds.

  + *Target gluing.* For GT, regard the image of
    $A -> B$ as an $A$-submodule.  Local surjectivity and clearing
    denominators put a suitable covering-element power times each $b$ in
    this image; the unit-ideal condition gives $b$ itself.

  + *Failure of S and GS.* #supplement-link(<sup-lp-37>)[LP-37] and
    #supplement-link(<sup-lp-38>)[LP-38] disprove S and GS, respectively.
]

#corollary(key: "sup-lp-30", title: "Closed Immersions")[
  + *Affine description.* Use the affine quotient dictionary of
    #supplement-link(<sup-cs-1>)[CS-1]; the assertions here concern its locality
    and base-change consequences.

  + *Target locality and base change.*

    - checkable on any affine open cover of the target;
    - Zariski local on the target;
    - stable under base change.

  + *Source locality.* It fails to be:

    - Zariski local on the source;
    - strongly affine local on arbitrary affine pairs.
]

#proof[

  + *Target locality from the definition.* A closed immersion is a homeomorphism onto a closed subset together with a
    surjective morphism of structure sheaves.  Both conditions may be checked
    after restricting the target to an open cover: closed subsets and the
    induced homeomorphisms glue, while surjectivity of a sheaf morphism is
    equivalent to surjectivity on every stalk.  Thus closed immersions are
    target local.

  + *Affine criterion and base change.* By #supplement-link(<sup-cs-1>)[CS-1], a closed immersion over
    $V=ops.spec A$ has affine whole inverse image with a surjective coordinate
    map, and conversely. Apply #supplement-link(<sup-lp-13>)[LP-13] with the
    ring-surjectivity conditions of #supplement-link(<sup-lp-29>)[LP-29]. This shows
    that one affine target cover suffices and gives base-change stability.

  + *Failure of source locality.* The examples in
    #supplement-link(<sup-lp-37>)[LP-37] and #supplement-link(<sup-lp-38>)[LP-38]
    disprove source restriction and source gluing, respectively. The first is
    also an affine pair, so strong affine locality fails.
]

==== Flat

#definition(key: "sup-lp-31", title: "Flat Ring Map")[
  A ring map $A -> B$ is *flat* if $B$ is a flat $A$-module, that is, tensoring
  an exact sequence of $A$-modules with $B$ preserves exactness.
]

#proposition(key: "sup-lp-32", title: "Locality Profile: Flat")[
  Flatness satisfies BC, T, S, GS, and GT.
]

#proof[

  + *BC, T, S, and PL.* Module flatness is stable under tensor-product base change and composition,
    and every localization is flat. These algebraic flatness facts are left
    to the reader (Check!). They give BC, T, S, and PL.

  + *Source gluing.* To prove GS, use the criterion that $B$ is flat over $A$ if and only if, for
    every injection $M' -> M$ of $A$-modules, the induced map
    $tensor(M', B, over: A) -> tensor(M, B, over: A)$ is injective.  After localizing at every
    $g_i$, this map is injective by hypothesis.  Its kernel localizes to zero
    at each $g_i$; because the $g_i$ generate the unit ideal, the kernel itself
    is zero.  Hence $B$ is flat over $A$.

  + *Target gluing.* Finally, GS and PL imply GT by the
    principal-target-extension argument above.
]

#corollary(key: "sup-lp-33", title: "Flat Morphisms")[
  Let $f:X->Y$ be a morphism of schemes.

  #set enum(spacing: 0.8em)

  + *Affine and stalk criteria.* The following conditions are equivalent:

    + $f$ is flat.
    + For every affine pair $U=ops.spec B subset X$ and
      $V=ops.spec A subset Y$ with $f(U) subset V$, the induced
      ring map $A->B$ is flat.
    + For every $x in X$, the local ring map
      $shf.o_(Y,f(x))->shf.o_(X,x)$ is flat.

  + *Locality & base change.*

    - strongly affine local;
    - Zariski local on the source;
    - Zariski local on the target;
    - stable under base change.
]

#proof[

  + *Affine-pair criterion and locality.* Apply #supplement-link(<sup-lp-14>)[LP-14]
    to LP-32.  This gives the affine-pair criterion, strong affine locality,
    and Zariski locality on both source and target.  On an affine pair
    $ops.spec B -> ops.spec A$, the stalk map at the prime
    $q subset B$, with inverse image $p subset A$, is the localized ring
    map $A_p -> B_q$.

  + *Pass from an affine pair to stalks.* Flatness of $A -> B$ implies flatness of all these maps
    by localization.

  + *Recover flatness from stalks.* Conversely, if every $A_p -> B_q$ is flat, then for each
    prime $q$ the localization $B_q$ is flat over $A$ by composition with the
    flat map $A -> A_p$; flatness of $B$ over $A$ follows because it may be
    checked after localization at all primes of $B$ (Check! a module whose
    localizations at every prime vanish is zero). Thus the affine and stalk
    criteria agree.

  + *Base change.* On affine charts a base change replaces $A->B$ by its
    tensor-product base change.  Ring-level BC and the affine-cover comparison
    of LP-14 therefore give BC for morphisms.
]

==== Faithfully flat

#definition(key: "sup-lp-34", title: "Faithfully Flat Ring Map")[
  A ring map $A -> B$ is *faithfully flat* if $B$ is flat over $A$ and the functor $tensor(-, B, over: A)$ detects exactness.  Equivalently, $A -> B$ is flat and
  $ops.spec B -> ops.spec A$ is surjective.
]

#proposition(key: "sup-lp-35", title: "Locality Profile: Faithfully Flat")[
  + Faithful flatness satisfies BC, T, and GT.

  + It satisfies neither S nor
    GS when empty distinguished covers are allowed.

  + GS does hold for
    nonempty finite distinguished covers.
]

#proof[

  Use the equivalence between faithful flatness of $A -> B$ and the
  conjunction of flatness with surjectivity of
  $ops.spec B -> ops.spec A$.

  + *BC and T.* Both conditions survive base change, so BC
    and hence T hold.

  + *Source gluing for a nonempty cover.* Under GS hypotheses for a nonempty indexing family,
    flatness glues and any member's faithfully flat map already surjects onto
    $ops.spec A$.
    Thus the whole spectrum map is surjective.

  + *Target gluing, including the empty cover.* Under GT hypotheses
    flatness again glues,
    and surjectivity is checked over the covering $D(a_i)$ of $ops.spec A$.
    If that target cover is empty, $A$ and hence $B$ are zero rings, and
    faithful flatness holds.  This proves nonempty-cover GS and unrestricted
    GT.

  + *Failure of S and unrestricted GS.* #supplement-link(<sup-lp-37>)[LP-37]
    and #supplement-link(<sup-lp-39>)[LP-39] disprove S and unrestricted GS,
    respectively.
]

#corollary(key: "sup-lp-36", title: "Faithfully Flat Morphisms")[
  + *Affine spectra.* A faithfully flat ring map gives an affine, flat, surjective morphism of
    spectra.

  + *General schemes.* For a general morphism, faithful flatness means flatness together
    with surjectivity.

  + *Target locality and base change.*

    - Zariski local on the target;
    - stable under base change.

  + *Source locality.* It fails to be:

    - Zariski local on the source;
    - strongly affine local on arbitrary affine pairs.
]

#proof[

  + *Identify faithful flatness.* On affine spectra, the equivalence in the preceding proof identifies a
    faithfully flat ring map with a flat and surjective morphism.  This
    identification is compatible with restriction to affine targets, so for
    general schemes faithful flatness is equivalent to flatness together with
    surjectivity.

  + *Target locality and base change.* Both properties are local on the target and stable under
    base change, hence so is their conjunction.

  + *Failure of source locality.* The localization in
    #supplement-link(<sup-lp-37>)[LP-37] is both an open-source restriction and an
    affine pair. It rules out source locality and strong affine locality.
]

#example(key: "sup-lp-37", title: "Failures under source localization")[
  None of finiteness, integrality, surjectivity, and faithful flatness
  satisfies S.
]
#proof[
  Let $k$ be a field and consider the source localization
  $k[t] -> k[t,t^(-1)]$ of the identity map of $k[t]$.

  + *Finiteness.* The identity is finite, whereas $k[t,t^(-1)]$ is not a
    finite $k[t]$-module.

  + *Integrality.* The identity is integral, whereas $t^(-1)$ is not integral
    over $k[t]$.

  + *Surjectivity.* The identity is surjective, whereas $t^(-1)$ is not in
    the image of $k[t]$.

  + *Faithful flatness.* The identity is faithfully flat, whereas the
    localized map is not: the nonzero $k[t]$-module
    $k[t]\/ideal((t))$ tensors to zero with $k[t,t^(-1)]$.
]

#example(key: "sup-lp-38", title: "Failure of source gluing for surjectivity")[
  Surjectivity does not satisfy GS.
]
#proof[
  Let $e_1=(1,0)$ and $e_2=(0,1)$ in $k times k$. The principal opens
  $D(e_1)$ and $D(e_2)$ cover $ops.spec(k times k)$, and both localized
  diagonal maps $k -> (k times k)_(e_i)$ are isomorphic to $k -> k$ and hence
  surjective. The diagonal map $k -> k times k$ is not surjective, so GS
  fails.
]

#example(key: "sup-lp-39", title: "Failure of source gluing for the empty cover")[
  Faithful flatness does not satisfy GS when the empty distinguished cover is
  allowed.
]
#proof[
  Take $A=k$ and $B=0$. The empty family generates the unit ideal in the zero
  ring because $0=1$, and all localized-map hypotheses hold vacuously. The
  map $k -> 0$ is not faithfully flat, since the nonzero $k$-module $k$
  tensors to zero. Thus unrestricted GS fails. If GS is formulated only for
  nonempty finite distinguished covers, faithful flatness does satisfy it, as
  proved in LP-35.
]

=== Geometric-property case studies

The next properties are not properties of one arbitrary ring map.  They are
best tested using RS, GSS, RT, and GTT directly.

==== Quasi-compact

#definition(key: "sup-lp-40", title: "Quasi-compact Morphism")[
  A morphism $f:X -> Y$ is *quasi-compact* if $f^(-1)(V)$ is quasi-compact for
  every quasi-compact open $V subset Y$.  It is enough to test affine opens
  $V subset Y$.
]

#proposition(key: "sup-lp-41", title: "Locality Profile: Quasi-compact")[
  Quasi-compactness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[

  + *Target restriction.* Let $V=ops.spec A subset Y$.  If $f^(-1)(V)$ is quasi-compact, then the
    inverse image of a distinguished open $D(a) subset V$ is the
    nonvanishing locus of the pulled-back section.  Choose finitely many affine
    charts covering $f^(-1)(V)$; on each chart that locus is distinguished and
    hence quasi-compact.  Their finite union is quasi-compact, proving target
    restriction.

  + *Target gluing.* Conversely, quasi-compact inverse images over a finite
    distinguished cover of $V$ have quasi-compact union, proving target gluing.
    Quasi-compactness of affine targets upgrades these distinguished tests to
    arbitrary target covers.

  + *Base change.* For base change, work over affine bases and cover the quasi-compact source
    by finitely many affine opens.  Their pullbacks are affine and form a finite
    cover of the new source, which is therefore quasi-compact.  Target locality
    glues this calculation.

  + *Failure of source locality.* The source-restriction and source-gluing
    counterexamples are #supplement-link(<sup-lp-48>)[LP-48] and
    #supplement-link(<sup-lp-49>)[LP-49], respectively.
]

==== Affine

#definition(key: "sup-lp-42", title: "Affine Morphism")[
  A morphism $f:X -> Y$ is *affine* if $f^(-1)(V)$ is affine for every affine
  open $V subset Y$.
]

#proposition(key: "sup-lp-43", title: "Locality Profile: Affine")[
  Affineness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[

  + *Apply the whole-inverse-image criterion.* In #supplement-link(<sup-lp-13>)[LP-13], take
    $cal(P)(A -> B)$ to hold for every ring map. Isomorphism invariance, T, GT,
    and BC are then automatic. The resulting property $cal(Q)$ is precisely
    affineness, so LP-13 gives RT, GTT, and base-change stability.

  + *Failure of source locality.* The source-restriction and source-gluing
    counterexamples are #supplement-link(<sup-lp-48>)[LP-48] and
    #supplement-link(<sup-lp-49>)[LP-49], respectively.
]

==== Separated

#definition(key: "sup-lp-44", title: "Separated Morphism")[
  A morphism $f:X -> Y$ is *separated* if its diagonal
  $Delta_f:X -> fiber(X, X, base: Y)$ is a closed immersion.
]

#proposition(key: "sup-lp-45", title: "Locality Profile: Separated")[
  Separatedness satisfies RS, RT, and GTT and is stable under base change.  It
  does not satisfy GSS.
]

#proof[

  + *Base change.* The diagonal of a base change of $f$ is the base change of $Delta_f$.
    Since closed immersions are stable under base change, separatedness is also
    stable under base change.

  + *Target restriction and gluing.* For a target
    cover $Y=union_i V_i$, the opens
    $f^(-1)(V_i) times_(V_i) f^(-1)(V_i)$ cover $fiber(X, X, base: Y)$,
    so target locality for closed immersions gives RT and GTT.

  + *Source restriction.* Restricting
    the source to $U$ pulls the diagonal back to the open
    $fiber(U, U, base: Y)$, proving RS.

  + *Failure of source gluing.* A source cover does not generally
    cover the fiber product by these self-products: the mixed products
    still have to be checked. The doubled-origin counterexample in
    #supplement-link(<sup-lp-49>)[LP-49] shows that GSS fails.
]

==== Universally closed

#definition(key: "sup-lp-46", title: "Universally Closed Morphism")[
  A morphism $f:X -> Y$ is *universally closed* if every base change
  $f':fiber(X, Y', base: Y) -> Y'$ is a closed map on underlying topological
  spaces.
]

#proposition(key: "sup-lp-47", title: "Locality Profile: Universally Closed")[
  Universal closedness satisfies RT and GTT and is stable under base change.
  It satisfies neither RS nor GSS.
]

#proof[

  + *Base change.* A further base change of a base change of $f$ is again a base change of
    $f$, so universal closedness is stable under base change.

  + *Target restriction and gluing.* Closedness of a continuous map is local on the target: for a closed
    $Z subset X$, check $f(Z) inter V_i$ in each member of an open target
    cover.  Apply this after every base change, whose pulled-back target
    opens still cover.  This proves RT and GTT.

  + *Failure of source locality.* The source-restriction and source-gluing
    counterexamples are #supplement-link(<sup-lp-48>)[LP-48] and
    #supplement-link(<sup-lp-49>)[LP-49], respectively.
]

#example(key: "sup-lp-48", title: "Failures under source restriction")[
  None of quasi-compactness, affineness, and universal closedness satisfies
  RS.
]
#proof[
  + *Quasi-compactness.* Let $A=k[x_1,x_2,dots]$ and
    $U=union_(i>=1) D(x_i) subset ops.spec A$. The identity of $ops.spec A$ is
    quasi-compact, but its restriction $U -> ops.spec A$ is not. Indeed, the
    displayed cover has no finite subcover: after choosing
    $D(x_1),dots,D(x_n)$, the prime $(x_1,dots,x_n)$ lies in $U$ but in none
    of those opens. Thus RS fails for quasi-compactness.

  + *Affineness.* The morphism $sch.a^2_k -> ops.spec k$ is affine, whereas
    $(sch.a^2_k minus {0}) -> ops.spec k$ is not affine; the nonaffineness
    calculation is in #supplement-link(<sup-mg-8>)[MG-8]. Thus RS fails for
    affineness.

  + *Universal closedness.* The morphism $sch.p^1_k -> ops.spec k$ is
    universally closed, but its restriction $sch.a^1_k -> ops.spec k$ is not.
    After base change to $sch.a^1_k$, the latter becomes the projection
    $sch.a^2_k -> sch.a^1_k$. The closed hyperbola $V(x y-1)$ has image
    $D(x)$, which is not closed. Thus RS fails for universal closedness.
]

#example(key: "sup-lp-49", title: "Failures under source gluing")[
  None of quasi-compactness, affineness, universal closedness, and
  separatedness satisfies GSS.
]
#proof[
  + *One example for three failures.* Assume that $k$ is algebraically closed
    and infinite. Map
    $X=coprod(ops.spec k, a in k)$ to $sch.a^1_k$ by sending its
    $a$-component to the closed point $a$. Every component map is a closed
    immersion, hence quasi-compact, affine, and universally closed. The whole
    morphism is not quasi-compact because $X$ is not quasi-compact; it is
    therefore not affine. It is not universally closed either, since its
    image is the nonclosed set of closed points of $sch.a^1_k$. Thus GSS
    fails for all three properties.

  + *Separatedness.* Use the doubled-origin line of
    #supplement-link(<sup-xp-11>)[XP-11], where its nonclosed diagonal is computed.
    Its two standard affine charts are separated over $ops.spec k$, whereas
    the whole scheme is not. Thus GSS fails for separatedness.
]

=== Projectivity and global polarizations

#definition(key: "sup-lp-50", title: "Three projective conditions")[
  A morphism $f:X->Y$ is *projective* in Hartshorne's sense if it factors
  through a closed immersion $X->sch.p^n_Y$ for a finite integer $n$.
  It is *locally projective* if such factorizations exist over an open
  cover of $Y$. A specified invertible sheaf is *very ample relative to*
  $Y$ if it is the pullback of $shf.o (1)$ under an immersion into some
  $sch.p^n_Y$; if $f$ is proper this immersion is closed.

  An embedding into $sch.p (shf.e)$ for a finite-type quasi-coherent module
  is a different convention for projectivity. A quotient
  $shf.o_Y^(N+1)->shf.e$ supplies the missing embedding into $sch.p^N_Y$;
  without such global data the conventions must not be identified.
  Compare Hartshorne II.4, II.7 and
  #link("https://stacks.math.columbia.edu/tag/01W7")[Stacks, Projective morphisms].
]

#proposition(key: "sup-lp-51", title: "Stability of projective morphisms")[
  Projectivity is preserved by arbitrary base change, target open
  restriction, composition, and products over a base.
]
#proof[
  Base change pulls the specified closed immersion back to
  $fiber(X, Y', base: Y)->sch.p^n_(Y')$; the latter identification sends
  homogeneous coordinates to the same coordinates after scalar extension.
  Target restriction is the case of an open immersion $Y'->Y$.
  For composition and products use the closed immersions and the Segre
  construction in #supplement-link(<sup-pj-11>)[PJ-11]. Its coordinates are the
  products of the two sets of homogeneous coordinates, so the construction
  commutes with restrictions and gives a single global embedding.
]

#example(key: "sup-lp-52", title: "Source and principal-target failures")[
  Restrict $sch.p^1_k->ops.spec k$ to $sch.a^1_k$. The restriction is not
  proper: after base change to $sch.a^1_k$, the closed hyperbola
  $V(x y-1)$ projects onto the nonclosed subset $D(x)$, as in LP-48.
  Hence projectivity does not survive arbitrary source restriction.

  Glue two copies of $sch.p^1_k$ along their common $sch.a^1_k$, using the
  identity. Both members of this open source cover are projective over
  $k$. The resulting scheme is not separated: on the product of the two
  charts its diagonal has closure containing the pair of distinct points
  at infinity. Equivalently, the two maps from $ops.spec k[s]_(s)$ near
  infinity agree on $ops.spec k(s)$ but have different closed points.
  Thus source open-cover gluing fails.

  The identity $D(t)->D(t)$ is projective, whereas its composite with
  $D(t)->sch.a^1_k$ is not closed and hence not proper. This is the
  failure of extension from a principal target open. These examples concern
  whole schemes; affine charts of a projective source need not be
  projective over the original target.
]

#example(key: "sup-lp-53", title: "A proper, locally projective morphism which is not projective")[
  Let $k$ be algebraically closed with $ops.char k != 2$, and let
  $C=V(y^2z-x^3-x^2z) subset sch.p^2_k$. Write $q$ for its node.
  Identify $C minus {q}$ with $shf.g_m$, with coordinate $w$ on its
  normalization $sch.p^1$, whose points $0,infinity$ map to $q$.
  Explicitly, the affine normalization parameter $a$ gives
  $x=a^2-1$, $y=a(a^2-1)$ and $w=(a-1)/(a+1)$; the two branches
  $a=1,-1$ become $w=0,infinity$.
  Multiplication $w mapsto u w$ extends to an automorphism of $C$ over
  $k[u,u^(-1)]$: on the normalization it preserves the two branches and
  their identification. Glue $C times ops.spec k[u]$ to
  $C times ops.spec k[v]$ on $v=u^(-1)$ using this automorphism. The
  resulting morphism $pi:X->sch.p^1_k$ is proper and locally projective,
  but is not projective. Every invertible sheaf on $X$ has degree zero
  on every fiber. (Ex. II.7.13)
]
#proof[
  *The scheme and its properness.* The overlap isomorphism and its inverse
  are specified by $w mapsto u w$ and $w mapsto u^(-1)w$; scheme gluing in
  #book-link(<sup-xl>)[XL] constructs $X$ and $pi$. Each restriction of
  $pi$ is the projective projection $C times sch.a^1->sch.a^1$.
  Locally finite type, quasi-compactness, separatedness, and universal
  closedness are target local by LP-18, LP-41, LP-45, and LP-47,
  respectively.  Thus $pi$ has all four properties globally; LP-18 identifies
  the first two with finite type, so $pi$ is proper. Its composite with
  $sch.p^1_k->ops.spec k$ is proper as well.

  *Line bundles on each normalization.* Put $R=k[u]$ or
  $R=k[u,u^(-1)]$. The normalization of $C_R$ is $sch.p^1_R$ and the
  conductor identifies the two disjoint sections $0,infinity$ with
  $q_R$. Both charts $ops.spec R[w]$ and $ops.spec R[w^(-1)]$ are
  factorial, so their Picard groups vanish by the divisor dictionary in
  II.6. Every line bundle on $sch.p^1_R$ is therefore specified by a unit
  on their overlap. The algebraic assertions that these rings are
  factorial and that
  $R[w,w^(-1)]^times=R^times w^ZZ$ are left to the reader.
  Changing the two frames removes the factor in $R^times$, leaving
  precisely $shf.o (n)$, $n in ZZ$.

  *Descent across the node.* An invertible sheaf on $C_R$ is an invertible
  sheaf on $sch.p^1_R$ together with an identification of its fibers at
  $0$ and $infinity$. Here is the affine check, rather than a use of a
  cohomology sequence. The conductor square of rings writes a nodal
  affine chart as $B times_(R times R) R$, where $B$ is its normalization,
  the first map evaluates at the two branches, and $R->R times R$ is
  diagonal. Patch a rank-one module on $B$ and a rank-one module on $R$
  by their two fiber identifications. The assertion that this fiber-product
  module is invertible and that extension of scalars recovers the two
  modules is a purely algebraic patching lemma; its proof is left to the
  reader. The construction commutes with localization. It therefore
  glues with the unchanged line bundle away from the node, by SL.
  Conversely, restriction of an invertible sheaf gives exactly these
  data. Since $ops.pic R=0$, the remaining datum for $shf.o (n)$ is a
  unit $lambda in R^times$. An automorphism of $shf.o (n)$ multiplies
  both branch fibers by the same unit, and cannot change $lambda$.
  Consequently
  $
    ops.pic (C_(k[u])) simeq k^times times ZZ, quad
    ops.pic (C_(k[u,u^(-1)])) simeq k^times times ZZ times ZZ.
  $
  In the second expression write $lambda=a u^d$ and list the coordinates
  as $(a,d,n)$.

  *The change on the overlap.* Choose the direction of the branch
  identification so that a frame at $0$ maps to $lambda$ times the frame
  at $infinity$. For $shf.o (n)$ choose frames with
  $e_infinity=w^n e_0$ on the overlap. Under $w mapsto u w$, identify the
  pulled-back frame at $0$ with $e_0$; the frame at infinity then becomes
  $u^n e_infinity$. Thus pullback is
  $(a,d,n) mapsto (a,d+n,n)$. Restriction from either polynomial base chart
  has middle coordinate zero: its units are constants. An invertible
  sheaf on $X$ must therefore satisfy $0=0+n$ on the overlap, and $n=0$.
  Normalization pulls its restriction on every fiber back to
  $shf.o_(sch.p^1)(n)$. This also computes its Cartier degree on the
  singular fiber; the normal-curve formula alone would not justify this.
  Indeed, at the node let $A$ be its local ring and $B$ its finite
  semilocal normalization. The module $B\/A$ has finite length. For a
  regular local equation $a$, multiplication by $a$ in
  $0->A->B->B\/A->0$ gives
  $0->(B\/A)[a]->A\/a A->B\/a B->(B\/A)\/a(B\/A)->0$.
  The kernel and cokernel of multiplication by $a$ on the finite-length
  module $B\/A$ have equal lengths. Thus the lengths of $A\/a A$ and
  $B\/a B$ agree. This exact-sequence and length computation is purely
  algebraic and is left to the reader. Away from the node normalization
  is an isomorphism; summing these lengths, and taking differences for
  meromorphic equations, proves equality of the two degrees.

  *The obstruction.* If $pi$ were projective, the pullback of the ambient
  $shf.o (1)$ would restrict to a very ample line bundle on $C$. Its
  pullback to the normalization has positive degree: a nonconstant map
  from $sch.p^1$ defined by sections of $shf.o (n)$ requires $n>0$,
  since for $n<0$ there are no sections and for $n=0$ all sections are
  constant. This contradicts $n=0$. The same argument rules out a
  projective embedding of $X$ over $k$.
]

#remark(key: "sup-lp-54", title: "The extra global datum")[
  If $Y$ is Noetherian with an ample invertible sheaf and $f:X->Y$ is
  proper, a *single* $f$-ample invertible sheaf on $X$ implies that $f$
  is projective; see #supplement-link(<sup-pm-2>)[PM-2]. In LP-53 the individual
  polarizations on the two charts cannot be restrictions of such a
  sheaf. Local projective embeddings alone do not supply it.
]

=== Dominance and information on dense opens

#proposition(key: "sup-lp-55", title: "Target locality and composition of dominance")[
  A morphism is dominant if its image is dense. For an open cover
  $Y=union_i V_i$, $f:X->Y$ is dominant if and only if all maps
  $f^(-1)(V_i)->V_i$ are dominant. Composites of dominant morphisms are
  dominant. On integral schemes the generic-point and injective-ring-map
  criteria are those of #book-link(<sup-xp-generic-points>)[XP-1\~XP-7].
]
#proof[
  The precise terminal topological assertions are: a subset is dense if
  and only if it meets every nonempty open; its intersection with each
  member of an open cover is dense there if and only if it is dense;
  and a continuous map sends the closure of a set into the closure of
  its image. Their proofs are left to the reader. Apply the first two to
  $f(X) inter V_i=f(f^(-1)(V_i))$. For $X->Y->Z$, apply the third to
  the dense image in $Y$, then use density of the image of $Y$ in $Z$.
  These are statements about the underlying continuous maps, so no
  affine refinement or sheaf gluing is needed.
]

#proposition(key: "sup-lp-56", title: "Restriction of the source")[
  If $X$ is integral and $f:X->Y$ is dominant, its restriction to every
  nonempty open $U subset X$ is dominant. This need not hold for a
  reducible source.
]
#proof[
  The generic point $eta$ of $X$ belongs to $U$, and
  $overline({f(eta)})=overline(f(X))=Y$ by continuity and
  $overline({eta})=X$. Hence $f(U)$ is dense. The generic-point and
  closure facts are the topological facts of XP-1\~XP-7, whose purely
  topological proofs are left to the reader. For failure, restrict the
  identity of two disjoint points to just one point; its image is closed
  and proper.
]

#proposition(key: "sup-lp-57", title: "Flat base change of a quasi-compact dominant map")[
  Let $f:X->Y$ be quasi-compact and dominant, and let $g:Y'->Y$ be flat.
  Then $fiber(X, Y', base: Y)->Y'$ is dominant. Arbitrary base change does
  not suffice: pulling $D(t)->ops.spec k[t]$ back to $t=0$ gives the
  empty scheme over a nonempty point.
]
#proof[
  Choose an affine open cover of $Y$, pull it back to $Y'$, and refine the
  resulting cover by affine opens $V'=ops.spec A'$ of $Y'$.  Each $V'$ maps
  into some affine $V=ops.spec A$ of $Y$.  By LP-55 it is enough to prove
  dominance over all these $V'$. Quasi-compactness gives
  a finite affine cover $U_i=ops.spec B_i$ of $f^(-1)(V)$. Let
  $B=product_i B_i$ and $I=ops.ker (A->B)$. The affine spectrum criterion
  says that the density of $union_i f(U_i)$ is equivalent to every
  element of $I$ being nilpotent. This uses the finite product, whose
  spectrum is the finite disjoint union of the $U_i$.

  The map $A->A'$ is flat by #supplement-link(<sup-lp-33>)[LP-33]. Flatness
  identifies the kernel of $A'->tensor(B, A', over: A)$ with $I A'$;
  a finite sum of multiples of nilpotent elements is nilpotent. Thus
  this kernel is a nil ideal. The spectrum criterion, exactness of flat
  tensor product, its commutation with finite products, and the assertion
  about nil ideals are the terminal algebraic facts; their proofs are
  left to the reader. By #supplement-link(<sup-mg-1>)[MG-1], the spectra of
  $tensor(B_i, A', over: A)$ cover the base-changed inverse image of $V'$.
  Their union has dense image in $V'$, as required. The affine target
  cover now gives dominance globally by LP-55.
  Compare #link("https://stacks.math.columbia.edu/tag/01RI")[Stacks, Dominant morphisms].
]

#proposition(key: "sup-lp-58", title: "Associated points and restriction injectivity")[
  Let $X$ be locally Noetherian, $shf.f$ coherent, and $j:U->X$ an open
  immersion. The map $shf.f->j_*(shf.f|_U)$ is injective if and only if
  $U$ contains every point of $ops.ass(shf.f)$. In particular,
  $shf.o_X->j_*shf.o_U$ is injective if and only if
  $ops.ass(shf.o_X) subset U$; such an open is called
  *schematically dense*.
]
#proof[
  Sheaf injectivity is checked on an affine open cover by SL. On
  $V=ops.spec A$, write $shf.f|_V=tildeOf(M)$ with $M$ finite.
  The open $U inter V$ is quasi-compact since $A$ is Noetherian; choose
  a finite principal cover $union_(i=1)^r D(a_i)$. Restriction on $V$
  is injective precisely when
  $M->product_i M_(a_i)$ is injective; the sheaf condition identifies
  its kernel with the kernel of restriction to $U inter V$.
  The associated-prime criterion in #book-link(<sup-al2>)[AL2] says that
  this happens if and only if every associated prime of $M$ avoids at
  least one $a_i$. Its purely algebraic proof is left to the reader.
  Associated primes localize, so these are exactly the associated
  points of $shf.f$ in $V$. Applying the same statement to every
  principal subopen checks injectivity of the sheaf map, and the
  affine cover proves both implications globally.
]

#corollary(key: "sup-lp-59", title: "Equality on a schematically dense open")[
  Let $j:U->X$ be an open immersion for which
  $shf.o_X->j_*shf.o_U$ is injective. If $Y/S$ is separated, two
  $S$-morphisms $X->Y$ agreeing on $U$ are equal.

  The reduced-source, topologically dense case is MG-6. For the distinction
  between topological and schematic density, see the counterexample
  in MG-7 and its associated-prime calculation in AL2-4.
]
#proof[
  As in MG-6, pull back the closed diagonal of $Y/S$ to obtain the
  equalizer $E->X$ with ideal sheaf $shf.i$. Agreement on $U$ says
  $shf.i|_U=0$. The inclusion $shf.i->shf.o_X$ therefore has zero composite
  with $shf.o_X->j_*shf.o_U$. Injectivity forces $shf.i=0$, so $E=X$
  and the two morphisms are equal. LP-58 supplies the associated-point
  criterion for the hypothesis when $X$ is locally Noetherian.
]

#proposition(key: "sup-lp-60", title: "Hartogs extension on a normal scheme")[
  Let $X$ be integral, normal and Noetherian. If $Z subset X$ is closed
  and every point of $Z$ has codimension at least two, restriction
  gives an isomorphism $shf.o_X -> j_*shf.o_(X minus Z)$.
]
#proof[
  Construct the comparison by restriction. On any affine
  $V=ops.spec A$, $A$ is a Noetherian normal domain with fraction field
  $K=k(X)$. A section on $V minus Z$ determines an element of $K$
  because it restricts to the generic stalk; injectivity follows from
  integrality, or LP-58. Every height-one prime of $A$ lies outside $Z$,
  so that rational function lies in all $A_idl.p$ of height one.
  The algebraic theorem
  $ A=inter.big_(ops.ht idl.p=1) A_idl.p subset K $
  for Noetherian normal domains (II.6 and AL2) gives membership in $A$;
  its proof is left to the reader. This proves surjectivity on each
  affine $V$. The inverse is unique inside $K$, hence agrees on affine
  refinements of overlaps. SL gives the sheaf isomorphism. In particular,
  global regular functions extend uniquely.
]

#pagebreak(weak: true)

=== Summary tables

#figure(
  table(
    columns: (2.2fr, 0.72fr, 0.72fr, 0.72fr, 0.72fr, 0.72fr),
    align: (left, center, center, center, center, center),
    inset: 4pt,
    table.header([*Ring property*], [*BC*], [*T*], [*S*], [*GS*], [*GT*]),
    [finite type (LP-17)], [$checkmark$], [$checkmark$], [$checkmark$], [$checkmark$], [$checkmark$],
    [finite presentation (LP-20)], [$checkmark$], [$checkmark$], [$checkmark$], [$checkmark$], [$checkmark$],
    [finite (LP-23)], [$checkmark$], [$checkmark$], [$crossmark$ (LP-37)], [$checkmark$], [$checkmark$],
    [integral (LP-26)], [$checkmark$], [$checkmark$], [$crossmark$ (LP-37)], [$checkmark$], [$checkmark$],
    [surjective (LP-29)], [$checkmark$], [$checkmark$], [$crossmark$ (LP-37)], [$crossmark$ (LP-38)], [$checkmark$],
    [flat (LP-32)], [$checkmark$], [$checkmark$], [$checkmark$], [$checkmark$], [$checkmark$],
    [faithfully flat (LP-35)],
    [$checkmark$],
    [$checkmark$],
    [$crossmark$ (LP-37)],
    [$crossmark$ (LP-39)],
    [$checkmark$],
  ),
  caption: [Ring-locality profiles.],
)

For faithfully flat maps, GS is no because the definition includes the
empty distinguished cover of the zero ring.  With a nonempty-cover
convention, this entry alone would be yes.

#figure(
  table(
    columns: (1.8fr, 0.78fr, 0.78fr, 0.78fr, 0.78fr, 0.78fr),
    align: (left, center, center, center, center, center),
    inset: 3pt,
    table.header([*Morphism property*], [*RS*], [*GSS*], [*RT*], [*GTT*], [*BC*]),
    [quasi-compact (LP-41)], [$crossmark$ (LP-48)], [$crossmark$ (LP-49)], [$checkmark$], [$checkmark$], [$checkmark$],
    [affine (LP-43)], [$crossmark$ (LP-48)], [$crossmark$ (LP-49)], [$checkmark$], [$checkmark$], [$checkmark$],
    [separated (LP-45)], [$checkmark$], [$crossmark$ (LP-49)], [$checkmark$], [$checkmark$], [$checkmark$],
    [universally closed (LP-47)],
    [$crossmark$ (LP-48)],
    [$crossmark$ (LP-49)],
    [$checkmark$],
    [$checkmark$],
    [$checkmark$],

    [projective (LP-51)],
    [$crossmark$ (LP-52)],
    [$crossmark$ (LP-52)],
    [$checkmark$],
    [$crossmark$ (LP-53)],
    [$checkmark$],
  ),
  caption: [Scheme-level locality profiles.],
)

#remark(key: "sup-lp-61", title: "A Procedure for Checking Locality")[
  When studying a new property, proceed in the following order.

  + Distinguish the all-affine-pairs route from the affine-whole-inverse-image
    route before choosing hypotheses.
  + Use T and S for affine refinements.  For a fixed affine target, S and GS
    give affine communication.
  + For a criterion imposed on every affine pair, S and GS give source
    locality by #supplement-link(<sup-lp-12>)[LP-12].  Add T and GT when the criterion
    must be testable on one affine atlas and local on the target, as in
    #supplement-link(<sup-lp-14>)[LP-14]. PL can help prove GT, but is not an
    additional hypothesis once GT is known.
  + For an affine whole inverse image with a ring property, use T and GT
    to pass between affine target charts and glue the inverse images.
  + If the property involves the topology of a whole inverse image, a
    diagonal, or all base changes, test RS, GSS, RT, and GTT directly.
  + Record base-change stability separately: it is a transport principle,
    not a gluing principle.

  In short,
  #align(center)[
    $"ring locality" -> "affine criteria"$ \
    $"scheme restriction and gluing" -> "source/target locality"$
  ]
]
