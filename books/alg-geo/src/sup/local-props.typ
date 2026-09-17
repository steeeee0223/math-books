#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *
#import "proof-layout.typ": proof

=== LP — A Locality Calculus for Morphisms <sup-lp>

Many definitions in algebraic geometry begin with a property of a ring map
$A -> B$ and then pass to affine charts.  The passage rests on three standard
methods: induction over affine open covers, criteria involving the whole
inverse image of an affine open, and criteria involving all affine pairs.
The letters below abbreviate the restriction and gluing operations used in
these arguments.

*Reading route.* After #book-link(<text-ii-2>)[II.2], read
#book-link(<sup-xl>)[XL-1–7] and then LP-1–15 for the locality framework.
The whole-inverse-image argument uses the affineness criterion of
#book-link(<sup-proof-2-17>)[II.2.17(b)]. Ring-level BC is a tensor-product
condition; the scheme-level BC conclusions require the fiber products of
#book-link(<text-ii-3>)[II.3, Theorem 3.3]. Read the finite-type and finite
cases alongside II.3. Revisit the diagonal and universal-closedness cases
with #book-link(<text-ii-4>)[II.4]; the integral GS proof also uses the
additional characterization of integral morphisms as affine and universally
closed. The affine closed-immersion dictionary is proved in
#book-link(<sup-cs-1>)[CS-1] using II.5.9–5.10. Flatness and faithful flatness
require their stated module-theoretic criteria. See the
#book-link(<sup-roadmap>)[reading roadmap] for these separate dependencies.

==== Ring-local conditions

The zero ring and empty schemes are allowed.  In the counterexamples, $k$ is
a field.  Fix a property $cal(P)(A -> B)$ invariant under isomorphisms of ring
maps.  Source and target in the letters S and T refer to the scheme map
$ops.spec B -> ops.spec A$, not to the ring map.

#metadata(none) <sup-lp-1>
#definition(number: "LP-1", title: "The conditions BC, T, and S")[
  The following are preservation conditions.

  - *(BC), Base-change stability.* For every $A$-algebra $A'$, one has
    $ cal(P)(A -> B) Rightarrow cal(P)(A' -> tensor(B, A', over: A)). $
  - *(T), Target localization.* For every $f in A$, one has
    $cal(P)(A -> B) Rightarrow cal(P)(A_f -> B_f)$.
  - *(S), Source localization.* For every $g in B$, one has
    $cal(P)(A -> B) Rightarrow cal(P)(A -> B_g)$.
]

#metadata(none) <sup-lp-2>
#definition(number: "LP-2", title: "The conditions GS and GT")[
  The following are gluing conditions.  All covers in these conditions are
  finite distinguished covers, including the empty cover of the empty
  spectrum.  Allowing arbitrary distinguished covers gives equivalent
  conditions: an ideal containing $1$ already contains a finite expression
  for $1$ in its generators.

  - *(GS), Source gluing.* If $g_1, dots, g_n in B$ generate the unit ideal and
    $cal(P)(A -> B_(g_i))$ holds for every $i$, then $cal(P)(A -> B)$ holds.
  - *(GT), Target gluing.* If $f_1, dots, f_n in A$ generate the unit ideal and
    $cal(P)(A_(f_i) -> B_(f_i))$ holds for every $i$, then $cal(P)(A -> B)$ holds.
]

#metadata(none) <sup-lp-3>
#definition(number: "LP-3", title: "Principal-target Extension")[
  - *(PL), Principal-target extension,* is the following compatibility condition: if $a in A$ maps to a unit in an $A$-algebra $C$, then $ cal(P)(A_a -> C) Rightarrow cal(P)(A -> C). $ It follows, for example, when every principal localization $A -> A_a$ has $cal(P)$ and $cal(P)$ is stable under composition.
]

#metadata(none) <sup-lp-4>
#remark(number: "LP-4", title: "PL is an optional way to prove GT")[
  - *Examples of PL.* Finite type, finite presentation, and flatness satisfy PL: the principal
    localization $A -> A_a$ has the same property, and that property is stable
    under composition.

  - *Deriving GT.* If GS and PL hold, then GT follows.  Indeed, from
    $cal(P)(A_(a_i) -> B_(a_i))$, PL gives $cal(P)(A -> B_(a_i))$; the images of the
    $a_i$ generate the unit ideal of $B$, so GS gives $cal(P)(A -> B)$.
]

#metadata(none) <sup-lp-5>
#proposition(number: "LP-5", title: "Base Change Contains Target Localization")[
  - Every property satisfying BC satisfies T, since $B_f simeq tensor(B, A_f, over: A)$.
  - Source localization is different: $B_g$ is obtained by localizing the codomain ring $B$, and need not be a base change from $A$.
]

==== From rings to affine charts

Let $f:X -> Y$ be a morphism.  An *affine pair for* $f$ means affine opens
$U=ops.spec B subset.eq X$ and $V=ops.spec A subset.eq Y$ such that
$U subset.eq f^(-1)(V)$.  The restriction $U -> V$ corresponds to a ring map
$A -> B$.

#metadata(none) <sup-lp-6>
#proposition(number: "LP-6", title: "Affine Locality Principle")[
  Suppose $cal(P)$ satisfies T and S.  If an affine cover of $Y$, together with
  affine covers of its inverse images, consists of charts whose ring maps have
  $cal(P)$, then every principal affine refinement of those charts also has $cal(P)$.
  Thus the chartwise condition survives the common refinements used in scheme
  arguments.
]

#proof[
  #set enum(numbering: "1.")

  Start with a chart $U=ops.spec B -> V=ops.spec A$ having $cal(P)$.

  + *Restrict the target.* Restricting
    the target to $D(a) subset.eq V$ replaces its ring map by
    $A_a -> B_a$, which has $cal(P)$ by T.

  + *Refine the source.* A principal affine refinement of the
    source then has coordinate ring $(B_a)_g$ for some $g in B_a$, and
    $A_a -> (B_a)_g$ has $cal(P)$ by S.  These are precisely the ring maps attached
    to principal refinements of the original affine pair.
]

#metadata(none) <sup-lp-7>
#proposition(number: "LP-7", title: "Affine Communication Lemma (Fixed Target)")[
  Let $f:X -> ops.spec A$ be a morphism.  Suppose $cal(P)$ satisfies S and GS.  If
  $X$ has an affine cover $U_i=ops.spec B_i$ such that every
  $A -> B_i$ has $cal(P)$, then $A -> Gamma(U, shf.o_X)$ has $cal(P)$ for every affine
  open $U subset.eq X$.
]

#proof[
  #set enum(numbering: "1.")

  Put $U=ops.spec B$.

  + *Choose simultaneous distinguished neighborhoods.* For $x in U inter U_i$, choose a neighborhood which
    is distinguished in both affine opens:
    $
      x in W = D_U\(g) = D_(U_i)(h).
    $
    To construct such a neighborhood, first choose
    $x in D_U\(a) subset.eq U inter U_i$, then
    $x in D_(U_i)(h) subset.eq D_U\(a)$.  The restriction of $h$ to $D_U\(a)$
    has the form $c/a^n$, so $D_(U_i)(h)=D_U\(a c)$.

  + *Restrict the known property.* By S applied in $U_i$, the map $A -> Gamma(W, shf.o_X)$ has $cal(P)$.
    Isomorphism invariance identifies this with $A -> B_g$.

  + *Glue on the chosen affine open.* These $W$ cover
    $U$; quasi-compactness selects finitely many, and their defining elements
    generate the unit ideal of $B$.  GS gives $cal(P)(A -> B)$.

    The simultaneous distinguished neighborhood is essential: mere inclusion
    $D_U\(g) subset.eq U_i$ does not make $g$ a section on $U_i$.
]

#metadata(none) <sup-lp-8>
#proposition(number: "LP-8", title: "Exactly what fixed-target communication requires")[
  For an isomorphism-invariant ring-map property, the fixed-target affine
  communication statement above, required for every $A$, $X$, and affine
  cover, is equivalent to S and GS together.
]

#proof[
  #set enum(numbering: "1.")

  + *Sufficiency.* Apply the preceding proposition.

  + *Necessity of S.* For S, take $X=ops.spec B$ with its
    one-member cover, and apply communication to $D(g) subset.eq X$.

  + *Necessity of GS.* For GS, cover $ops.spec B$ by the given $D(g_i)$ and apply communication
    to the affine open $X$ itself.  This also handles the zero ring with its
    empty distinguished cover.  Thus neither S nor GS can simply be omitted
    from this universal communication statement.  T, GT, BC, and PL are not
    needed for the fixed-target proof.
]

#metadata(none) <sup-lp-9>
#proposition(number: "LP-9", title: "Strong Affine Locality from Ring-Local Conditions")[

  Suppose $cal(P)$ satisfies T, S, GS, and GT.

  - *Affine pairs.* If one system of affine charts for
    $f:X -> Y$ has $cal(P)$, then the ring map associated with every affine pair for
    $f$ has $cal(P)$.  In this situation, the resulting morphism property is *strongly
    affine local*.

  - *Locality.* It is Zariski local on both source and target.
]

#proof[
  #set enum(numbering: "1.")

  For an affine target $V=ops.spec A$, let $cal(H)(V)$ mean that every affine open
  $U=ops.spec B subset.eq f^(-1)(V)$ has $cal(P)(A -> B)$.

  + *Start on the given target cover.* S and GS give $cal(H)(V_i)$ on each member of the original target
    cover, by fixed-target communication.

  + *Restrict the target.* $cal(H)(V)$ implies $cal(H)(D(a))$.  If $U=ops.spec B$ lies over $D(a)$,
    then $cal(P)(A -> B)$ holds and the image of $a$ is a unit in $B$.  T and
    $B_a simeq B$ give $cal(P)(A_a -> B)$.

  + *Glue over a distinguished target cover.* Suppose the $D(a_i)$ cover $V$ and $cal(H)(D(a_i))$ holds.  For any
    affine $U=ops.spec B subset.eq f^(-1)(V)$, the opens
    $U inter f^(-1)(D(a_i))=ops.spec B_(a_i)$ give
    $cal(P)(A_(a_i) -> B_(a_i))$.  GT gives $cal(P)(A -> B)$, hence $cal(H)(V)$.

  + *Pass to every affine target.* The second step permits restriction to a distinguished open of any affine
    target on which $cal(H)$ holds, and the third glues over a finite distinguished
    cover.  Every affine open is quasi-compact, so any affine cover of it has a
    finite refinement by distinguished opens.  Starting from the original
    affine target cover and applying these two operations therefore proves
    $cal(H)(V)$ for every affine open $V subset.eq Y$.  This is precisely the
    assertion about every affine pair.

  + *Check locality on both sides.*
    - Restriction to an open source or target preserves the all-affine-pairs condition.
    - For source gluing, restrict to an affine target, refine the source cover by affine opens, and use fixed-target communication.
    - For target gluing, refine the target cover by affine opens and repeat the distinguished-open induction above.

    Thus the condition is local on both
    source and target.
]

#metadata(none) <sup-lp-10>
#remark(number: "LP-10", title: "A Characterization of Strong Affine Locality")[
  - *Necessity.* If a scheme-morphism property $cal(Q)$ is local on both source and target and
    $cal(Q)(ops.spec B -> ops.spec A)$ is equivalent to $cal(P)(A -> B)$, then T, S,
    GS, and GT are necessary: apply restriction and gluing to distinguished
    covers of the two spectra.

  - *Sufficiency.* Conversely, the preceding proof constructs
    such a $cal(Q)$ from these four conditions: require $cal(P)$ for every affine pair.
    Its value on a morphism between affine spectra is then exactly $cal(P)$, by
    fixed-target communication and induction over distinguished target covers.

  - *Scope of the characterization.* This characterizes when $cal(P)$ extends in this way to a property local on both
    sides; it does not assert that the four conditions are logically
    independent.  A property local only on the target, such as finiteness, need
    not satisfy S or GS.  Base-change stability is a separate question, while
    PL is merely one sufficient device for proving GT.
]

#metadata(none) <sup-lp-11>
#remark(number: "LP-11", title: "Whole inverse images versus affine pairs")[
  Some important properties, such as finite and integral, fail S.  They are
  therefore not properties of every affine pair.  Instead, they use a target
  criterion: for $V=ops.spec A subset.eq Y$, require both conditions.

  - The whole inverse image is affine, say $f^(-1)(V)=ops.spec B$.
  - The map $A -> B$ has the stated ring property.
]

#metadata(none) <sup-lp-12>
#example(number: "LP-12", title: "Locality on both sides does not imply BC")[
  - *Locality.* Let $cal(P)(A -> B)$ mean that $B$ is reduced, and let $cal(Q)(f:X -> Y)$ mean
    that $X$ is reduced.  Reducedness is preserved by open restriction and
    can be checked on an open cover; consequently $cal(Q)$ is local on the source
    and on the target, and $cal(P)$ satisfies T, S, GS, and GT.

  - *Failure of BC.* But the base change of $k -> k$ along
    $k -> k[epsilon]\/ideal((epsilon^2))$ has nonreduced codomain.
    Thus BC is not necessary for locality, even on both sides.
]

#metadata(none) <sup-lp-13>
#proposition(number: "LP-13", title: "The Whole-Inverse-Image Target Criterion")[
  Suppose $cal(P)$ respects isomorphisms and satisfies T and GT.  Define $cal(Q)(f)$
  by requiring both conditions for every affine $V=ops.spec A$ in the target.

  + The entire inverse image is affine, $f^(-1)(V)=ops.spec B$.
  + The ring map satisfies $cal(P)(A -> B)$.

  Then:

  - $cal(Q)$ is Zariski local on the target.
  - If $cal(P)$ also satisfies BC, so does $cal(Q)$.
]

#proof[
  #set enum(numbering: "1.")

  + *Restrict to a distinguished target.* On an affine target, restriction to $D(a)$ replaces the whole inverse
    image $ops.spec B$ by $ops.spec B_a$; use T.

  + *Glue the whole inverse image.* For a distinguished target cover $D(a_i)$, suppose each whole inverse
    image $X_i$ is affine and has $cal(P)$.  The pullbacks of the $a_i$ are global
    sections of $X$, generate the unit ideal in $Gamma(X, shf.o_X)$, and
    have affine nonvanishing loci $X_i$.  The unit-ideal criterion of
    #book-link(<sup-xl-7>)[XL-7], proved in
    #book-link(<sup-proof-2-17>)[II.2.17(b)], therefore makes $X$ affine.
    Writing $X=ops.spec B$, the restricted coordinate
    maps are $A_(a_i) -> B_(a_i)$, and GT gives $cal(P)(A -> B)$.  Since an affine
    target is quasi-compact, an arbitrary target cover admits a finite
    distinguished refinement, so this proves target locality.

  + *Check base change.* For BC, reduce both base schemes to affine opens using target locality.
    If the base change is $ops.spec A' -> ops.spec A$, the pullback of
    $ops.spec B -> ops.spec A$ is
    $ops.spec tensor(B, A', over: A) -> ops.spec A'$.  Its source is affine and
    its ring map has $cal(P)$ by BC.  The affine-local reductions just proved glue
    these affine calculations, so $cal(Q)$ is stable under arbitrary base change.
]

==== Locality directly on schemes

Ring-local conditions describe affine charts.  For a property $cal(Q)(f)$ of
scheme morphisms, locality on an arbitrary open cover is expressed directly at
scheme level.

#metadata(none) <sup-lp-14>
#definition(number: "LP-14", title: "Source and Target Tests")[
  Let $f:X -> Y$ be a morphism.

  - *(RS), source restriction:* $cal(Q)(f)$ implies $cal(Q)(U -> Y)$ for every open
    $U subset.eq X$.
  - *(GSS), source gluing:* if $X=union_i U_i$ and every $U_i -> Y$ has $cal(Q)$,
    then $f$ has $cal(Q)$.
  - *(RT), target restriction:* $cal(Q)(f)$ implies
    $cal(Q)(f^(-1)(V) -> V)$ for every open $V subset.eq Y$.
  - *(GTT), target gluing:* if $Y=union_i V_i$ and every
    $f^(-1)(V_i) -> V_i$ has $cal(Q)$, then $f$ has $cal(Q)$.
]

#metadata(none) <sup-lp-15>
#corollary(number: "LP-15", title: "Zariski Locality")[
  - A property satisfying RS and GSS is Zariski local on the source.

  - A property satisfying RT and GTT is Zariski local on the target.

  These scheme-level tests are parallel to S, GS, T, and GT, but they are not
  the same statements: the former concern arbitrary open subschemes, whereas
  the latter concern ring maps between affine schemes.
]

#proof[
  #set enum(numbering: "1.")

  + *Source locality.* Let $X=union_i U_i$.  If $cal(Q)(f)$ holds, RS gives $cal(Q)(U_i -> Y)$ for every
    $i$; conversely, if all these restrictions have $cal(Q)$, GSS gives $cal(Q)(f)$.
    Thus RS and GSS give exactly the two implications in locality on the source.

  + *Target locality.* Likewise, for $Y=union_i V_i$, RT gives the restricted properties
    $cal(Q)(f^(-1)(V_i) -> V_i)$ from $cal(Q)(f)$, while GTT gives the converse.
    Hence RT and GTT give locality on the target.
]
==== Ring-property case studies

===== Finite type

#metadata(none) <sup-lp-16>
#definition(number: "LP-16", title: "Finite Type Ring Map")[
  A ring map $A -> B$ is *of finite type* if
  $B=A[b_1, dots, b_n]$ for finitely many elements of $B$.
]

#metadata(none) <sup-lp-17>
#proposition(number: "LP-17", title: "Locality Profile: Finite Type")[
  Finite type satisfies BC, T, S, GS, and GT.
]

#proof[
  #set enum(numbering: "1.")

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

#metadata(none) <sup-lp-18>
#corollary(number: "LP-18", title: "Locally Finite-type Morphisms")[
  The corresponding chartwise property is *locally of finite type*.

  - *Locality and base change.* It is
    strongly affine local, Zariski local on both source and target, and stable
    under base change.

  - *Finite type.* A morphism is of finite type precisely when it is locally
    of finite type and quasi-compact.
]

#proof[
  #set enum(numbering: "1.")

  + *Affine locality.* The preceding proposition and #book-link(<sup-lp-9>)[the Strong Affine Locality proposition] show
    that one affine atlas with finite-type coordinate maps is equivalent to the
    same condition on every affine pair; they also give locality on both source
    and target.

  + *Base change.* On affine pairs, base change is the tensor-product construction,
    so BC gives stability under base change and locality glues the result.

  + *Finite type implies quasi-compactness.* If $f$ is of finite type, the finitely many source charts in its defining
    affine atlas show that inverse images of affine opens are quasi-compact.

  + *Quasi-compactness gives a finite atlas.* Conversely, if $f$ is quasi-compact and locally of finite type, cover the
    inverse image of an affine target by finite-type affine charts and use
    quasi-compactness to retain finitely many of them.  This is precisely the
    finite atlas required in the definition of a finite-type morphism.
]

===== Finite presentation

#metadata(none) <sup-lp-19>
#definition(number: "LP-19", title: "Finite Presentation Ring Map")[
  A ring map $A -> B$ is *of finite presentation* if
  $B simeq A[x_1, dots, x_n]\/ideal((r_1, dots, r_m))$ for finite lists of
  generators and relations.
]

#metadata(none) <sup-lp-20>
#proposition(number: "LP-20", title: "Locality Profile: Finite Presentation")[
  Finite presentation satisfies BC, T, S, GS, and GT.
]

#proof[
  #set enum(numbering: "1.")

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

  Strong Affine Locality and BC now give the assertions of the corollary.
]

#metadata(none) <sup-lp-21>
#corollary(number: "LP-21", title: "Locally Finite-presentation Morphisms")[
  The corresponding chartwise property is *locally of finite presentation*.
  It is strongly affine local, Zariski local on both source and target, and
  stable under base change.
]

===== Finite

#metadata(none) <sup-lp-22>
#definition(number: "LP-22", title: "Finite Ring Map")[
  A ring map $A -> B$ is *finite* if $B$ is a finitely generated $A$-module.
]

#metadata(none) <sup-lp-23>
#proposition(number: "LP-23", title: "Locality Profile: Finite")[
  Finite satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[
  #set enum(numbering: "1.")

  + *BC and T.* A finite set of $A$-module generators of $B$ tensors to a finite set of
    $A'$-module generators after any base change $A -> A'$, proving BC and
    hence T.

  + *Target gluing.* For GT, lift finite generating sets from the localizations
    $B_(a_i)$ and clear denominators.  For each $b in B$, a power
    of each covering element times $b$ lies in the span of these lifts;
    the unit-ideal condition then puts $b$ itself in that span.

  + *Source gluing.* GS follows from integral GS proved below and finite-type GS, using
    the equivalence of module-finiteness with integrality plus finite type.

  + *Failure of source localization.* The example proves failure of S.
]

#metadata(none) <sup-lp-24>
#example(number: "LP-24", title: "Failure of S for finite maps")[
  The identity $k[t] -> k[t]$ is finite, but the source localization
  $k[t] -> k[t,t^(-1)]$ is not finite as a map of $k[t]$-modules.
]

#metadata(none) <sup-lp-25>
#corollary(number: "LP-25", title: "Finite Morphisms")[
  - *Affine criterion.* A morphism $f:X -> Y$ is finite if, over every affine open
    $V=ops.spec A subset.eq Y$, the whole inverse image is
    $f^(-1)(V)=ops.spec B$ with $A -> B$ finite.

  - *Target locality and base change.* This criterion is affine local
    and Zariski local on the target.  Finite morphisms are stable under base
    change.

  - *Source locality.* Finiteness is not local on the source and is not strongly affine
    local on arbitrary affine pairs.
]

#proof[
  #set enum(numbering: "1.")

  + *Target locality.* Apply the whole-inverse-image target criterion to ring finiteness, using T
    and GT from the preceding proposition.  This proves that the criterion may
    be checked on one affine cover of the target or on every affine target.

  + *Base change.* The same proposition transports BC from rings to schemes.

  + *Failure of source locality.* The displayed
    localization $k[t] -> k[t,t^(-1)]$ is the coordinate map of an open-source
    restriction of the identity of $ops.spec k[t]$; since it is not finite,
    source restriction, and hence source locality, fails.
]

===== Integral

#metadata(none) <sup-lp-26>
#definition(number: "LP-26", title: "Integral Ring Map")[
  A ring map $A -> B$ is *integral* if every $b in B$ satisfies a monic
  polynomial with coefficients in $A$.
]

#metadata(none) <sup-lp-27>
#proposition(number: "LP-27", title: "Locality Profile: Integral")[
  Integral satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[
  #set enum(numbering: "1.")

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

  + *Failure of source localization.* The
    following example proves failure of S.
]

#metadata(none) <sup-lp-28>
#example(number: "LP-28", title: "Failure of S for integral maps")[
  The identity $k[t] -> k[t]$ is integral.  The source localization
  $k[t] -> k[t,t^(-1)]$ is not integral because $t^(-1)$ is not integral over
  $k[t]$.
]

#metadata(none) <sup-lp-29>
#corollary(number: "LP-29", title: "Integral Morphisms")[
  - *Affine criterion.* A morphism is integral exactly when inverse images of affine targets are
    affine and induce integral ring maps.

  - *Target locality and base change.* Integral morphisms are affine local
    and Zariski local on the target and are stable under base change.

  - *Source locality.* They are
    not local on the source and not strongly affine local on arbitrary affine
    pairs.
]

#proof[
  #set enum(numbering: "1.")

  + *Target locality and base change.* Apply the whole-inverse-image target criterion with T and GT for integral
    ring maps.  It gives the stated every-affine-target criterion and target
    locality; ring BC gives stability under base change.

  + *Failure of source locality.* The open restriction
    in the example has coordinate map $k[t] -> k[t,t^(-1)]$, which is not
    integral, so source locality fails.
]

===== Surjective

#metadata(none) <sup-lp-30>
#definition(number: "LP-30", title: "Surjective Ring Map")[
  A ring map $phi:A->B$ is *surjective* if every element of $B$ is the
  image of an element of $A$. Equivalently, the canonical map
  $
    A\/ops.ker(phi)->B, quad a+ops.ker(phi) mapsto phi(a),
  $
  is an isomorphism. Thus the quotient description must identify $phi$
  with the quotient map; an abstract ring isomorphism $B simeq A\/I$
  alone does not characterize the given map $phi$.
]

#metadata(none) <sup-lp-31>
#proposition(number: "LP-31", title: "Locality Profile: Surjective")[
  Surjectivity satisfies BC, T, and GT, but it satisfies neither S nor GS.
]

#proof[
  #set enum(numbering: "1.")

  + *BC and T.* Every tensor is a sum of pure tensors.  If $A -> B$ is surjective, lift the
    $B$-entry of each pure tensor to $A$; this proves that the base-changed map
    is surjective.  Thus BC, and hence T, holds.

  + *Target gluing.* For GT, regard the image of
    $A -> B$ as an $A$-submodule.  Local surjectivity and clearing
    denominators put a suitable covering-element power times each $b$ in
    this image; the unit-ideal condition gives $b$ itself.

  + *Failure of S and GS.* The two examples
    below disprove S and GS.
]

#metadata(none) <sup-lp-32>
#example(number: "LP-32", title: "Failures of S and GS for surjectivity")[
  - *Failure of S.* The identity $k[t] -> k[t]$ is surjective, while
    $k[t] -> k[t,t^(-1)]$ is not; hence S fails.

  - *Failure of GS.* For GS, let $e_1=(1,0)$ and $e_2=(0,1)$ in $k times k$.  The diagonal map
    $k -> k times k$ is not surjective, but $e_1,e_2$ generate the unit ideal
    and both localized maps are isomorphic to $k -> k$, hence are surjective.
]

#metadata(none) <sup-lp-33>
#corollary(number: "LP-33", title: "Closed Immersions")[
  - *Affine description.* Use the affine quotient dictionary of
    #book-link(<sup-cs-1>)[CS-1]; the assertions here concern its locality
    and base-change consequences.

  - *Target locality and base change.* Closed immersions are affine local and Zariski
    local on the target and are stable under base change.

  - *Source locality.* They are not local on
    the source and not strongly affine local on arbitrary affine pairs.
]

#proof[
  #set enum(numbering: "1.")

  + *Target locality from the definition.* A closed immersion is a homeomorphism onto a closed subset together with a
    surjective morphism of structure sheaves.  Both conditions may be checked
    after restricting the target to an open cover: closed subsets and the
    induced homeomorphisms glue, while surjectivity of a sheaf morphism is
    equivalent to surjectivity on every stalk.  Thus closed immersions are
    target local.

  + *Affine criterion and base change.* By #book-link(<sup-cs-1>)[CS-1], a closed immersion over
    $V=ops.spec A$ has affine whole inverse image with a surjective coordinate
    map, and conversely. Apply #book-link(<sup-lp-13>)[LP-13] with the
    ring-surjectivity conditions of #book-link(<sup-lp-31>)[LP-31]. This gives
    affine locality and base-change stability.

  + *Failure of source locality.* The localization
    example above is an open-source restriction of a closed immersion which is
    not a closed immersion.  The diagonal $k -> k times k$ similarly gives a
    source cover whose restrictions are closed immersions although the whole
    morphism is not; hence source locality fails.
]

===== Flat

#metadata(none) <sup-lp-34>
#definition(number: "LP-34", title: "Flat Ring Map")[
  A ring map $A -> B$ is *flat* if $B$ is a flat $A$-module, that is, tensoring
  an exact sequence of $A$-modules with $B$ preserves exactness.
]

#metadata(none) <sup-lp-35>
#proposition(number: "LP-35", title: "Locality Profile: Flat")[
  Flatness satisfies BC, T, S, GS, and GT.
]

#proof[
  #set enum(numbering: "1.")

  + *BC, T, S, and PL.* Module flatness is stable under tensor-product base change and composition,
    and every localization is flat.  These facts give BC, T, S, and PL.

  + *Source gluing.* To prove GS, use the criterion that $B$ is flat over $A$ exactly when, for
    every injection $M' -> M$ of $A$-modules, the induced map
    $tensor(M', B, over: A) -> tensor(M, B, over: A)$ is injective.  After localizing at every
    $g_i$, this map is injective by hypothesis.  Its kernel localizes to zero
    at each $g_i$; because the $g_i$ generate the unit ideal, the kernel itself
    is zero.  Hence $B$ is flat over $A$.

  + *Target gluing and scheme locality.* Finally, GS and PL imply GT by the
    principal-target-extension argument above.  Strong Affine Locality then
    gives source and target locality for flat morphisms.
]

#metadata(none) <sup-lp-36>
#corollary(number: "LP-36", title: "Flat Morphisms")[
  Let $f:X->Y$ be a morphism of schemes.

  #set enum(numbering: "(i)", spacing: 0.8em)

  - *Affine and stalk criteria.* The following conditions are equivalent:

    + $f$ is flat.
    + For every affine pair $U=ops.spec B subset.eq X$ and
      $V=ops.spec A subset.eq Y$ with $f(U) subset.eq V$, the induced
      ring map $A->B$ is flat.
    + For every $x in X$, the local ring map
      $shf.o_(Y,f(x))->shf.o_(X,x)$ is flat.

  - *Locality and base change.* Flatness is strongly affine local,
    Zariski local on both source and target, and stable under base change.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the affine and stalk maps.* The affine-pair criterion follows from the preceding locality package.
    On an affine pair $ops.spec B -> ops.spec A$, the stalk map at the prime
    $q subset.eq B$, with inverse image $p subset.eq A$, is the localized ring
    map $A_p -> B_q$.

  + *Pass from an affine pair to stalks.* Flatness of $A -> B$ implies flatness of all these maps
    by localization.

  + *Recover flatness from stalks.* Conversely, if every $A_p -> B_q$ is flat, then for each
    prime $cal(Q)$ the localization $B_q$ is flat over $A$ by composition with the
    flat map $A -> A_p$; flatness of $B$ over $A$ follows because it may be
    checked after localization at all primes of $B$.  Thus the affine and stalk
    criteria agree.

  + *Base change.* BC for rings, followed by affine locality, gives BC for
    morphisms.
]

===== Faithfully flat

#metadata(none) <sup-lp-37>
#definition(number: "LP-37", title: "Faithfully Flat Ring Map")[
  A ring map $A -> B$ is *faithfully flat* if $B$ is flat over $A$ and the functor $tensor(-, B, over: A)$ detects exactness.  Equivalently, $A -> B$ is flat and
  $ops.spec B -> ops.spec A$ is surjective.
]

#metadata(none) <sup-lp-38>
#proposition(number: "LP-38", title: "Locality Profile: Faithfully Flat")[
  - Faithful flatness satisfies BC, T, and GT.

  - It satisfies neither S nor
    GS when empty distinguished covers are allowed.

  - GS does hold for
    nonempty finite distinguished covers.
]

#proof[
  #set enum(numbering: "1.")

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

  + *Failure of S and unrestricted GS.* The examples disprove S and unrestricted GS.
]

#metadata(none) <sup-lp-39>
#example(number: "LP-39", title: "Why Source Gluing Fails for the Empty Cover")[
  - *The empty-cover hypotheses.* Take $A=k$ and $B=0$, the zero ring.  The empty family generates the
    unit ideal in $B$ because $0=1$, and all its localized-map hypotheses
    hold vacuously.

  - *Failure of the conclusion.* But $k -> 0$ is not faithfully flat: the nonzero
    $k$-module $k$ tensors to zero.  Thus GS fails when the empty distinguished
    cover of the zero ring is admitted.

  - *The nonempty-cover convention.* If GS is instead formulated only for
    nonempty finite distinguished covers, faithful flatness does satisfy it;
    that is a different convention.
]

#metadata(none) <sup-lp-40>
#example(number: "LP-40", title: "Failure of S for faithful flatness")[
  The identity $k[t] -> k[t]$ is faithfully flat.  The source localization
  $k[t] -> k[t,t^(-1)]$ is flat but not faithfully flat: tensoring the nonzero
  module $k[t]\/(t)$ with $k[t,t^(-1)]$ gives zero.
]

#metadata(none) <sup-lp-41>
#corollary(number: "LP-41", title: "Faithfully Flat Morphisms")[
  - *Affine spectra.* A faithfully flat ring map gives an affine, flat, surjective morphism of
    spectra.

  - *General schemes.* For a general morphism, faithful flatness means flatness together
    with surjectivity.

  - *Locality and base change.* It is stable under base change and local on the target,
    but it is not local on the source; its surjectivity cannot be checked on
    every small affine pair.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify faithful flatness.* On affine spectra, the equivalence in the preceding proof identifies a
    faithfully flat ring map with a flat and surjective morphism.  This
    identification is compatible with restriction to affine targets, so for
    general schemes faithful flatness is equivalent to flatness together with
    surjectivity.

  + *Target locality and base change.* Both properties are local on the target and stable under
    base change, hence so is their conjunction.

  + *Failure of source locality.* The localization example
    shows that an open-source restriction can destroy surjectivity and rules
    out source locality.  Gluing a family of surjective restrictions and
    demanding that every restriction be surjective are different tests.
]

==== Geometric-property case studies

The next properties are not properties of one arbitrary ring map.  They are
best tested using RS, GSS, RT, and GTT directly.

===== Quasi-compact

#metadata(none) <sup-lp-42>
#definition(number: "LP-42", title: "Quasi-compact Morphism")[
  A morphism $f:X -> Y$ is *quasi-compact* if $f^(-1)(V)$ is quasi-compact for
  every quasi-compact open $V subset.eq Y$.  It is enough to test affine opens
  $V subset.eq Y$.
]

#metadata(none) <sup-lp-43>
#proposition(number: "LP-43", title: "Locality Profile: Quasi-compact")[
  Quasi-compactness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[
  #set enum(numbering: "1.")

  + *Target restriction.* Let $V=ops.spec A subset.eq Y$.  If $f^(-1)(V)$ is quasi-compact, then the
    inverse image of a distinguished open $D(a) subset.eq V$ is the
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

  + *Failure of source locality.* The examples prove the two source failures.
]

#metadata(none) <sup-lp-44>
#example(number: "LP-44", title: "Source failures for quasi-compactness")[
  - *Failure of RS.* Let $A=k[x_1,x_2,dots]$ and
    $U=union_(i>=1) D(x_i) subset.eq ops.spec A$.  The identity of $ops.spec A$ is
    quasi-compact, but its restriction $U -> ops.spec A$ is not, so RS fails.

  - *Failure of GSS.* Use the infinite disjoint union of points in
    #book-link(<sup-xp-disjoint-points>)[XP's disjoint-points example]. Each
    component maps quasi-compactly to $ops.spec k$, whereas the whole source
    is not quasi-compact. Thus GSS fails.
]

#metadata(none) <sup-lp-45>
#corollary(number: "LP-45", title: "Target Criterion for Quasi-compactness")[
  Quasi-compactness is affine local and Zariski local on the target, and it is
  stable under base change.  It is not local on the source.
]

===== Affine

#metadata(none) <sup-lp-46>
#definition(number: "LP-46", title: "Affine Morphism")[
  A morphism $f:X -> Y$ is *affine* if $f^(-1)(V)$ is affine for every affine
  open $V subset.eq Y$.
]

#metadata(none) <sup-lp-47>
#proposition(number: "LP-47", title: "Locality Profile: Affine")[
  Affineness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[
  #set enum(numbering: "1.")

  + *Apply the whole-inverse-image criterion.* In #book-link(<sup-lp-13>)[LP-13], take
    $cal(P)(A -> B)$ to hold for every ring map. Isomorphism invariance, T, GT,
    and BC are then automatic. The resulting property $cal(Q)$ is precisely
    affineness, so LP-13 gives RT, GTT, and base-change stability.

  + *Check the source failures.* The following examples disprove RS and GSS.
]

#metadata(none) <sup-lp-48>
#example(number: "LP-48", title: "Source failures for affineness")[
  - *Failure of RS.* The morphism $sch.a^2_k -> ops.spec k$ is affine, while the restriction
    $(sch.a^2_k minus {0}) -> ops.spec k$ is not affine; the nonaffineness
    calculation is in #book-link(<sup-mg-5>)[MG-5]. Hence RS fails.

  - *Failure of GSS.* The two standard affine lines cover $sch.p^1_k$, but
    $sch.p^1_k -> ops.spec k$ is not affine.  Hence GSS fails.
]

#metadata(none) <sup-lp-49>
#corollary(number: "LP-49", title: "Target Criterion for Affineness")[
  Affineness is affine local and Zariski local on the target and is stable
  under base change.  It is not local on the source.
]

===== Separated

#metadata(none) <sup-lp-50>
#definition(number: "LP-50", title: "Separated Morphism")[
  A morphism $f:X -> Y$ is *separated* if its diagonal
  $Delta_f:X -> fiber(X, X, base: Y)$ is a closed immersion.
]

#metadata(none) <sup-lp-51>
#proposition(number: "LP-51", title: "Locality Profile: Separated")[
  Separatedness satisfies RS, RT, and GTT and is stable under base change.  It
  does not satisfy GSS.
]

#proof[
  #set enum(numbering: "1.")

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
    still have to be checked.  This accounts for the doubled-origin
    counterexample to GSS.
]

#metadata(none) <sup-lp-52>
#example(number: "LP-52", title: "Failure of source gluing for separatedness")[
  Use the doubled-origin line of #book-link(<sup-xp-5>)[XP-5], where its
  nonclosed diagonal is computed. Its two standard affine charts are
  separated over $ops.spec k$, while the whole scheme is not. Thus GSS fails.
]

#metadata(none) <sup-lp-53>
#corollary(number: "LP-53", title: "Target Criterion for Separatedness")[
  Separatedness is affine local and Zariski local on the target and is stable
  under base change.  It is preserved by restriction to an open source, but
  it is not local on the source because source gluing fails.
]

===== Universally closed

#metadata(none) <sup-lp-54>
#definition(number: "LP-54", title: "Universally Closed Morphism")[
  A morphism $f:X -> Y$ is *universally closed* if every base change
  $f':fiber(X, Y', base: Y) -> Y'$ is a closed map on underlying topological
  spaces.
]

#metadata(none) <sup-lp-55>
#proposition(number: "LP-55", title: "Locality Profile: Universally Closed")[
  Universal closedness satisfies RT and GTT and is stable under base change.
  It satisfies neither RS nor GSS.
]

#proof[
  #set enum(numbering: "1.")

  + *Base change.* A further base change of a base change of $f$ is again a base change of
    $f$, so universal closedness is stable under base change.

  + *Target restriction and gluing.* Closedness of a continuous map is local on the target: for a closed
    $Z subset.eq X$, check $f(Z) inter V_i$ in each member of an open target
    cover.  Apply this after every base change, whose pulled-back target
    opens still cover.  This proves RT and GTT.

  + *Failure of source locality.* The examples give the source
    failures.
]

#metadata(none) <sup-lp-56>
#example(number: "LP-56", title: "Source failures for universal closedness")[
  - *Failure of RS.* The morphism $sch.p^1_k -> ops.spec k$ is universally closed, but its open
    restriction $sch.a^1_k -> ops.spec k$ is not; hence RS fails.

    For the latter assertion, base change to $sch.a^1_k$ and project
    $sch.a^2_k -> sch.a^1_k$.  The closed hyperbola $V(x y-1)$ has image
    $D(x)$, which is not closed.  Thus it is universal closedness, not
    closedness of the original map to a point, that fails.

  - *Failure of GSS.* Assume $k$ is algebraically closed and infinite.  Map the disjoint union
    $coprod(ops.spec k, a in k)$ to $sch.a^1_k$ by sending its $a$-component to
    the closed point $a$.  Every component map is a closed immersion, hence
    universally closed, but their union has image equal to the set of closed
    points, which is not closed.  Thus GSS fails.
]

#metadata(none) <sup-lp-57>
#corollary(number: "LP-57", title: "Target Criterion for Universal Closedness")[
  Universal closedness is affine local and Zariski local on the target and is
  stable under base change.  It is not local on the source.
]

==== Summary tables

#figure(
  table(
    columns: (2.2fr, 0.72fr, 0.72fr, 0.72fr, 0.72fr, 0.72fr),
    align: (left, center, center, center, center, center),
    inset: 4pt,
    table.header([*Ring property*], [*BC*], [*T*], [*S*], [*GS*], [*GT*]),
    [finite type], [yes], [yes], [yes], [yes], [yes],
    [finite presentation], [yes], [yes], [yes], [yes], [yes],
    [finite], [yes], [yes], [no], [yes], [yes],
    [integral], [yes], [yes], [no], [yes], [yes],
    [surjective], [yes], [yes], [no], [no], [yes],
    [flat], [yes], [yes], [yes], [yes], [yes],
    [faithfully flat], [yes], [yes], [no], [no], [yes],
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
    [quasi-compact], [no], [no], [yes], [yes], [yes],
    [affine], [no], [no], [yes], [yes], [yes],
    [separated], [yes], [no], [yes], [yes], [yes],
    [universally closed], [no], [no], [yes], [yes], [yes],
  ),
  caption: [Scheme-level locality profiles.],
)

#metadata(none) <sup-lp-58>
#remark(number: "LP-58", title: "A Procedure for Checking Locality")[
  When studying a new property, proceed in the following order.

  + Distinguish the all-affine-pairs route from the affine-whole-inverse-image
    route before choosing hypotheses.
  + Use T and S for affine refinements.  For a fixed affine target, S and GS
    give affine communication.
  + For a criterion imposed on every affine pair, verify T, S, GS, and GT.
    PL can help prove GT, but is not an additional hypothesis once GT is known.
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
