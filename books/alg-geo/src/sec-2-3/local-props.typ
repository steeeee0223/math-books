#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== A Locality Calculus for Morphisms

Many definitions in algebraic geometry begin with a property of a ring map
$A -> B$ and then pass to affine charts.  The passage rests on three standard
methods: induction over affine open covers, criteria involving the whole
inverse image of an affine open, and criteria involving all affine pairs.
The letters below abbreviate the restriction and gluing operations used in
these arguments.

==== Ring-local conditions

All rings are commutative with identity and all ring maps preserve identity;
the zero ring and empty schemes are allowed.  In the counterexamples, $k$ is
a field.  Fix a property $P(A -> B)$ invariant under isomorphisms of ring
maps.  Source and target in the letters S and T refer to the scheme map
$ops.spec B -> ops.spec A$, not to the ring map.

#definition(number: none, title: "The conditions BC, T, and S")[
  The following are preservation conditions.

  - *(BC), base-change stability.* For every $A$-algebra $A'$, one has
    $P(A -> B) Rightarrow P(A' -> tensor(B, A', over: A))$.
  - *(T), target localization.* For every $f in A$, one has
    $P(A -> B) Rightarrow P(A_f -> B_f)$.
  - *(S), source localization.* For every $g in B$, one has
    $P(A -> B) Rightarrow P(A -> B_g)$.
]

#definition(number: none, title: "The conditions GS and GT")[
  The following are gluing conditions.  All covers in these conditions are
  finite distinguished covers, including the empty cover of the empty
  spectrum.  Allowing arbitrary distinguished covers gives equivalent
  conditions: an ideal containing $1$ already contains a finite expression
  for $1$ in its generators.

  - *(GS), source gluing.* If $g_1, dots, g_n in B$ generate the unit ideal and
    $P(A -> B_(g_i))$ holds for every $i$, then $P(A -> B)$ holds.
  - *(GT), target gluing.* If $f_1, dots, f_n in A$ generate the unit ideal and
    $P(A_(f_i) -> B_(f_i))$ holds for every $i$, then $P(A -> B)$ holds.
]

#definition(number: none, title: "Principal-target Extension")[
  *(PL), principal-target extension,* is the following compatibility condition:
  if $a in A$ maps to a unit in an $A$-algebra $C$, then
  $
    P(A_a -> C) Rightarrow P(A -> C).
  $

  It follows, for example, when every principal localization $A -> A_a$ has
  $P$ and $P$ is stable under composition.
]

#remark(title: "PL is an optional way to prove GT")[
  Finite type, finite presentation, and flatness satisfy PL: the principal
  localization $A -> A_a$ has the same property, and that property is stable
  under composition.  If GS and PL hold, then GT follows.  Indeed, from
  $P(A_(a_i) -> B_(a_i))$, PL gives $P(A -> B_(a_i))$; the images of the
  $a_i$ generate the unit ideal of $B$, so GS gives $P(A -> B)$.
]

#proposition(title: "Base Change Contains Target Localization")[

  Every property satisfying BC satisfies T, since
  $B_f simeq tensor(B, A_f, over: A)$.

  Source localization is different: $B_g$ is obtained by localizing the
  codomain ring $B$, and need not be a base change from $A$.
]

==== From rings to affine charts

Let $f:X -> Y$ be a morphism.  An *affine pair for* $f$ means affine opens
$U=ops.spec B subset.eq X$ and $V=ops.spec A subset.eq Y$ such that
$U subset.eq f^(-1)(V)$.  The restriction $U -> V$ corresponds to a ring map
$A -> B$.

#proposition(title: "Affine Locality Principle")[
  Suppose $P$ satisfies T and S.  If an affine cover of $Y$, together with
  affine covers of its inverse images, consists of charts whose ring maps have
  $P$, then every principal affine refinement of those charts also has $P$.
  Thus the chartwise condition survives the common refinements used in scheme
  arguments.
]

#proof[
  Start with a chart $U=ops.spec B -> V=ops.spec A$ having $P$.  Restricting
  the target to $D(a) subset.eq V$ replaces its ring map by
  $A_a -> B_a$, which has $P$ by T.  A principal affine refinement of the
  source then has coordinate ring $(B_a)_g$ for some $g in B_a$, and
  $A_a -> (B_a)_g$ has $P$ by S.  These are precisely the ring maps attached
  to principal refinements of the original affine pair.
]

#proposition(title: "Affine Communication Lemma (Fixed Target)")[
  Let $f:X -> ops.spec A$ be a morphism.  Suppose $P$ satisfies S and GS.  If
  $X$ has an affine cover $U_i=ops.spec B_i$ such that every
  $A -> B_i$ has $P$, then $A -> Gamma(U, shf.o_X)$ has $P$ for every affine
  open $U subset.eq X$.
]

#proof[
  Put $U=ops.spec B$.  For $x in U inter U_i$, choose a neighborhood which
  is distinguished in both affine opens:
  $
    x in W = D_U(g) = D_(U_i)(h).
  $
  To construct such a neighborhood, first choose
  $x in D_U(a) subset.eq U inter U_i$, then
  $x in D_(U_i)(h) subset.eq D_U(a)$.  The restriction of $h$ to $D_U(a)$
  has the form $c/a^n$, so $D_(U_i)(h)=D_U(a c)$.

  By S applied in $U_i$, the map $A -> Gamma(W, shf.o_X)$ has $P$.
  Isomorphism invariance identifies this with $A -> B_g$.  These $W$ cover
  $U$; quasi-compactness selects finitely many, and their defining elements
  generate the unit ideal of $B$.  GS gives $P(A -> B)$.

  The simultaneous distinguished neighborhood is essential: mere inclusion
  $D_U(g) subset.eq U_i$ does not make $g$ a section on $U_i$.
]

#proposition(title: "Exactly what fixed-target communication requires")[
  For an isomorphism-invariant ring-map property, the fixed-target affine
  communication statement above, required for every $A$, $X$, and affine
  cover, is equivalent to S and GS together.
]

#proof[
  Sufficiency was proved above.  For S, take $X=ops.spec B$ with its
  one-member cover, and apply communication to $D(g) subset.eq X$.
  For GS, cover $ops.spec B$ by the given $D(g_i)$ and apply communication
  to the affine open $X$ itself.  This also handles the zero ring with its
  empty distinguished cover.  Thus neither S nor GS can simply be omitted
  from this universal communication statement.  T, GT, BC, and PL are not
  needed for the fixed-target proof.
]

#proposition(title: "Strong Affine Locality from Ring-Local Conditions")[
  Suppose $P$ satisfies T, S, GS, and GT.  If one system of affine charts for
  $f:X -> Y$ has $P$, then the ring map associated with every affine pair for
  $f$ has $P$.  In this situation the resulting morphism property is *strongly
  affine local*.  It is Zariski local on both source and target.
]

#proof[
  For an affine target $V=ops.spec A$, let $H(V)$ mean that every affine open
  $U=ops.spec B subset.eq f^(-1)(V)$ has $P(A -> B)$.

  First, S and GS give $H(V_i)$ on each member of the original target
  cover, by fixed-target communication.

  Second, $H(V)$ implies $H(D(a))$.  If $U=ops.spec B$ lies over $D(a)$,
  then $P(A -> B)$ holds and the image of $a$ is a unit in $B$.  T and
  $B_a simeq B$ give $P(A_a -> B)$.

  Third, suppose the $D(a_i)$ cover $V$ and $H(D(a_i))$ holds.  For any
  affine $U=ops.spec B subset.eq f^(-1)(V)$, the opens
  $U inter f^(-1)(D(a_i))=ops.spec B_(a_i)$ give
  $P(A_(a_i) -> B_(a_i))$.  GT gives $P(A -> B)$, hence $H(V)$.

  The second step permits restriction to a distinguished open of any affine
  target on which $H$ holds, and the third glues over a finite distinguished
  cover.  Every affine open is quasi-compact, so any affine cover of it has a
  finite refinement by distinguished opens.  Starting from the original
  affine target cover and applying these two operations therefore proves
  $H(V)$ for every affine open $V subset.eq Y$.  This is precisely the
  assertion about every affine pair.

  Restriction to an open source or target preserves the all-affine-pairs
  condition.  For source gluing, restrict to an affine target, refine the
  source cover by affine opens, and use fixed-target communication.  For
  target gluing, refine the target cover by affine opens and repeat the
  distinguished-open induction above.  Thus the condition is local on both
  source and target.
]

#remark(title: "A Characterization of Strong Affine Locality")[
  If a scheme-morphism property $Q$ is local on both source and target and
  $Q(ops.spec B -> ops.spec A)$ is equivalent to $P(A -> B)$, then T, S,
  GS, and GT are necessary: apply restriction and gluing to distinguished
  covers of the two spectra.  Conversely, the preceding proof constructs
  such a $Q$ from these four conditions: require $P$ for every affine pair.
  Its value on a morphism between affine spectra is then exactly $P$, by
  fixed-target communication and induction over distinguished target covers.

  This characterizes when $P$ extends in this way to a property local on both
  sides; it does not assert that the four conditions are logically
  independent.  A property local only on the target, such as finiteness, need
  not satisfy S or GS.  Base-change stability is a separate question, while
  PL is merely one sufficient device for proving GT.
]

#remark(title: "Whole inverse images versus affine pairs")[
  Some important properties, such as finite and integral, fail S.  They are
  therefore not properties of every affine pair.  Instead, they use a target
  criterion: for $V=ops.spec A subset.eq Y$, the whole inverse image must be
  affine, say $f^(-1)(V)=ops.spec B$, and the map $A -> B$ must have the stated
  ring property.
]

#example(title: "Locality on both sides does not imply BC")[
  Let $P(A -> B)$ mean that $B$ is reduced, and let $Q(f:X -> Y)$ mean
  that $X$ is reduced.  Reducedness is preserved by open restriction and
  can be checked on an open cover; consequently $Q$ is local on the source
  and on the target, and $P$ satisfies T, S, GS, and GT.
  But the base change of $k -> k$ along
  $k -> k[epsilon]\/ideal((epsilon^2))$ has nonreduced codomain.
  Thus BC is not necessary for locality, even on both sides.
]

#proposition(title: "The Whole-Inverse-Image Target Criterion")[
  Suppose $P$ respects isomorphisms and satisfies T and GT.  Define $Q(f)$
  by requiring, for every affine $V=ops.spec A$ in the target, that the
  entire inverse image be affine, $f^(-1)(V)=ops.spec B$, and that
  $P(A -> B)$ hold.  Then $Q$ is Zariski local on the target.  If P also
  satisfies BC, so does Q.
]

#proof[
  On an affine target, restriction to $D(a)$ replaces the whole inverse
  image $ops.spec B$ by $ops.spec B_a$; use T.

  For a distinguished target cover $D(a_i)$, suppose each whole inverse
  image $X_i$ is affine and has $P$.  The pullbacks of the $a_i$ are global
  sections of $X$, generate the unit ideal in $Gamma(X, shf.o_X)$, and
  have affine nonvanishing loci $X_i$.  The canonical morphism
  $X -> ops.spec Gamma(X, shf.o_X)$ restricts on each $X_i$ to the usual
  affine isomorphism.  These restrictions agree on overlaps, so they glue;
  hence $X$ is affine.  Writing $X=ops.spec B$, the restricted coordinate
  maps are $A_(a_i) -> B_(a_i)$, and GT gives $P(A -> B)$.  Since an affine
  target is quasi-compact, an arbitrary target cover admits a finite
  distinguished refinement, so this proves target locality.

  For BC, reduce both base schemes to affine opens using target locality.
  If the base change is $ops.spec A' -> ops.spec A$, the pullback of
  $ops.spec B -> ops.spec A$ is
  $ops.spec tensor(B, A', over: A) -> ops.spec A'$.  Its source is affine and
  its ring map has $P$ by BC.  The affine-local reductions just proved glue
  these affine calculations, so $Q$ is stable under arbitrary base change.
]

==== Locality directly on schemes

Ring-local conditions describe affine charts.  For a property $Q(f)$ of
scheme morphisms, locality on an arbitrary open cover is expressed directly at
scheme level.

#definition(number: none, title: "Source and Target Tests")[
  Let $f:X -> Y$ be a morphism.

  - *(RS), source restriction:* $Q(f)$ implies $Q(U -> Y)$ for every open
    $U subset.eq X$.
  - *(GSS), source gluing:* if $X=union_i U_i$ and every $U_i -> Y$ has $Q$,
    then $f$ has $Q$.
  - *(RT), target restriction:* $Q(f)$ implies
    $Q(f^(-1)(V) -> V)$ for every open $V subset.eq Y$.
  - *(GTT), target gluing:* if $Y=union_i V_i$ and every
    $f^(-1)(V_i) -> V_i$ has $Q$, then $f$ has $Q$.
]

#corollary(title: "Zariski Locality")[
  A property satisfying RS and GSS is Zariski local on the source.  A property
  satisfying RT and GTT is Zariski local on the target.

  These scheme-level tests are parallel to S, GS, T, and GT, but they are not
  the same statements: the former concern arbitrary open subschemes, whereas
  the latter concern ring maps between affine schemes.
]

#proof[
  Let $X=union_i U_i$.  If $Q(f)$ holds, RS gives $Q(U_i -> Y)$ for every
  $i$; conversely, if all these restrictions have $Q$, GSS gives $Q(f)$.
  Thus RS and GSS give exactly the two implications in locality on the source.

  Likewise, for $Y=union_i V_i$, RT gives the restricted properties
  $Q(f^(-1)(V_i) -> V_i)$ from $Q(f)$, while GTT gives the converse.
  Hence RT and GTT give locality on the target.
]
==== Ring-property case studies

===== Finite type

#definition(number: none, title: "Finite Type Ring Map")[
  A ring map $A -> B$ is *of finite type* if
  $B=A[b_1, dots, b_n]$ for finitely many elements of $B$.
]

#proposition(title: "Locality Profile: Finite Type")[
  Finite type satisfies BC, T, S, GS, and GT.
]

#proof[
  If $B$ is generated over $A$ by $b_1,dots,b_n$, then
  $tensor(B, A', over: A)$ is generated over $A'$ by the elements
  $b_j tensor 1$.  This proves BC and hence T.  A principal
  localization is generated by one inverse; together with composition
  stability this gives S and PL.

  For GS, choose coefficients $c_i$
  with $sum_i c_i g_i=1$ and let $C$ be the $A$-subalgebra generated by
  the $g_i$, the $c_i$, and numerators of finite generating sets for the
  $B_(g_i)$.  For $b in B$, clearing denominators gives
  $g_i^(n_i) b in C$.  The powers $g_i^(n_i)$ still generate the unit ideal
  in $C$, so $b in C$.  Hence $C=B$.  Finally, given a distinguished target
  cover, PL converts each $P(A_(a_i) -> B_(a_i))$ into
  $P(A -> B_(a_i))$, and GS then gives $P(A -> B)$.  Thus GT holds.
]

#corollary(title: "Locally Finite-type Morphisms")[
  The corresponding chartwise property is *locally of finite type*.  It is
  strongly affine local, Zariski local on both source and target, and stable
  under base change.  A morphism is of finite type precisely when it is locally
  of finite type and quasi-compact.
]

#proof[
  The preceding proposition and the Strong Affine Locality proposition show
  that one affine atlas with finite-type coordinate maps is equivalent to the
  same condition on every affine pair; they also give locality on both source
  and target.  On affine pairs, base change is the tensor-product construction,
  so BC gives stability under base change and locality glues the result.

  If $f$ is of finite type, the finitely many source charts in its defining
  affine atlas show that inverse images of affine opens are quasi-compact.
  Conversely, if $f$ is quasi-compact and locally of finite type, cover the
  inverse image of an affine target by finite-type affine charts and use
  quasi-compactness to retain finitely many of them.  This is precisely the
  finite atlas required in the definition of a finite-type morphism.
]

===== Finite presentation

#definition(number: none, title: "Finite Presentation Ring Map")[
  A ring map $A -> B$ is *of finite presentation* if
  $B simeq A[x_1, dots, x_n]\/ideal((r_1, dots, r_m))$ for finite lists of
  generators and relations.
]

#proposition(title: "Locality Profile: Finite Presentation")[
  Finite presentation satisfies BC, T, S, GS, and GT.
]

#proof[
  Tensoring a finite list of generators and relations with an $A$-algebra
  gives a finite presentation after base change, so BC and T hold.  The
  presentation
  $A_a simeq A[t]\/ideal((a t-1))$, together with composition stability,
  gives S and PL.

  For GS, first apply finite-type GS, then choose a surjection from a
  polynomial algebra in finitely many variables onto $B$.  Its kernel must be
  shown finitely generated.  Lifts of the $g_i$ need not generate the unit
  ideal in the polynomial algebra, so choose lifts of a relation
  $sum_i c_i g_i=1$ and impose the single relation
  $sum_i tilde(c)_i tilde(g)_i-1$.  In the resulting finitely presented
  intermediate algebra the lifted distinguished opens cover.  The localized
  kernels are finitely generated by the local finite presentations.  Clearing
  denominators in finite generating sets and using the unit-ideal relation
  then gives finitely many generators of the global kernel.  Thus GS holds.
  As in the finite-type case, GS and PL imply GT.  Strong Affine Locality and
  BC now give the assertions of the corollary.
]

#corollary(title: "Locally Finite-presentation Morphisms")[
  The corresponding chartwise property is *locally of finite presentation*.
  It is strongly affine local, Zariski local on both source and target, and
  stable under base change.
]

===== Finite

#definition(number: none, title: "Finite Ring Map")[
  A ring map $A -> B$ is *finite* if $B$ is a finitely generated $A$-module.
]

#proposition(title: "Locality Profile: Finite")[
  Finite satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[
  A finite set of $A$-module generators of $B$ tensors to a finite set of
  $A'$-module generators after any base change $A -> A'$, proving BC and
  hence T.  For GT, lift finite generating sets from the localizations
  $B_(a_i)$ and clear denominators.  For each $b in B$, a power
  of each covering element times $b$ lies in the span of these lifts;
  the unit-ideal condition then puts $b$ itself in that span.

  GS follows from integral GS proved below and finite-type GS, using
  the equivalence of module-finiteness with integrality plus finite type.
  The example proves failure of S.
]

#example(title: "Failure of S for finite maps")[
  The identity $k[t] -> k[t]$ is finite, but the source localization
  $k[t] -> k[t,t^(-1)]$ is not finite as a map of $k[t]$-modules.
]

#corollary(title: "Finite Morphisms")[
  A morphism $f:X -> Y$ is finite if, over every affine open
  $V=ops.spec A subset.eq Y$, the whole inverse image is
  $f^(-1)(V)=ops.spec B$ with $A -> B$ finite.  This criterion is affine local
  and Zariski local on the target.  Finite morphisms are stable under base
  change, but finiteness is not local on the source and is not strongly affine
  local on arbitrary affine pairs.
]

#proof[
  Apply the whole-inverse-image target criterion to ring finiteness, using T
  and GT from the preceding proposition.  This proves that the criterion may
  be checked on one affine cover of the target or on every affine target.
  The same proposition transports BC from rings to schemes.  The displayed
  localization $k[t] -> k[t,t^(-1)]$ is the coordinate map of an open-source
  restriction of the identity of $ops.spec k[t]$; since it is not finite,
  source restriction, and hence source locality, fails.
]

===== Integral

#definition(number: none, title: "Integral Ring Map")[
  A ring map $A -> B$ is *integral* if every $b in B$ satisfies a monic
  polynomial with coefficients in $A$.
]

#proposition(title: "Locality Profile: Integral")[
  Integral satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[
  A monic equation remains monic after extension of scalars, which proves BC
  and hence T.  For GT, clear denominators in local monic equations.  A power
  of each covering element times a given
  $b in B$ belongs to the integral closure of $A$ in $B$; gluing membership
  in this $A$-submodule shows that $b$ belongs to the integral closure.

  For GS, use the affine characterization that a morphism is integral if and
  only if it is affine and universally closed.  If finitely many $D(g_i)$ cover
  $ops.spec B$ and their maps to $ops.spec A$ are integral, these maps are
  universally closed.  After any base change, the image of a closed subset
  of the whole source is the finite union of its images from the $D(g_i)$;
  each is closed.  Hence the whole affine morphism is universally closed
  and therefore integral.  This argument uses a finite distinguished cover;
  it does not assert gluing over arbitrary open covers of the source.  The
  following example proves failure of S.
]

#example(title: "Failure of S for integral maps")[
  The identity $k[t] -> k[t]$ is integral.  The source localization
  $k[t] -> k[t,t^(-1)]$ is not integral because $t^(-1)$ is not integral over
  $k[t]$.
]

#corollary(title: "Integral Morphisms")[
  A morphism is integral exactly when inverse images of affine targets are
  affine and induce integral ring maps.  Integral morphisms are affine local
  and Zariski local on the target and are stable under base change.  They are
  not local on the source and not strongly affine local on arbitrary affine
  pairs.
]

#proof[
  Apply the whole-inverse-image target criterion with T and GT for integral
  ring maps.  It gives the stated every-affine-target criterion and target
  locality; ring BC gives stability under base change.  The open restriction
  in the example has coordinate map $k[t] -> k[t,t^(-1)]$, which is not
  integral, so source locality fails.
]

===== Surjective

#definition(number: none, title: "Surjective Ring Map")[
  A ring map $A -> B$ is *surjective* if every element of $B$ is the image of
  an element of $A$, equivalently $B simeq A\/I$ for some ideal $I subset.eq A$.
]

#proposition(title: "Locality Profile: Surjective")[
  Surjectivity satisfies BC, T, and GT, but it satisfies neither S nor GS.
]

#proof[
  Every tensor is a sum of pure tensors.  If $A -> B$ is surjective, lift the
  $B$-entry of each pure tensor to $A$; this proves that the base-changed map
  is surjective.  Thus BC, and hence T, holds.  For GT, regard the image of
  $A -> B$ as an $A$-submodule.  Local surjectivity and clearing
  denominators put a suitable covering-element power times each $b$ in
  this image; the unit-ideal condition gives $b$ itself.  The two examples
  below disprove S and GS.
]

#example(title: "Failures of S and GS for surjectivity")[
  The identity $k[t] -> k[t]$ is surjective, while
  $k[t] -> k[t,t^(-1)]$ is not; hence S fails.

  For GS, let $e_1=(1,0)$ and $e_2=(0,1)$ in $k times k$.  The diagonal map
  $k -> k times k$ is not surjective, but $e_1,e_2$ generate the unit ideal
  and both localized maps are isomorphic to $k -> k$, hence are surjective.
]

#corollary(title: "Closed Immersions")[
  Contravariantly, a surjective ring map $A -> B$ gives a closed immersion
  $ops.spec B -> ops.spec A$.  Closed immersions are affine local and Zariski
  local on the target and are stable under base change.  They are not local on
  the source and not strongly affine local on arbitrary affine pairs.
]

#proof[
  A closed immersion is a homeomorphism onto a closed subset together with a
  surjective morphism of structure sheaves.  Both conditions may be checked
  after restricting the target to an open cover: closed subsets and the
  induced homeomorphisms glue, while surjectivity of a sheaf morphism is
  equivalent to surjectivity on every stalk.  Thus closed immersions are
  target local.

  Over $V=ops.spec A$, this definition is equivalent to requiring
  $f^(-1)(V)=ops.spec B$ and a surjective coordinate map $A -> B$.
  The whole-inverse-image criterion and BC for surjections therefore give affine
  locality, target locality, and base-change stability.  The localization
  example above is an open-source restriction of a closed immersion which is
  not a closed immersion.  The diagonal $k -> k times k$ similarly gives a
  source cover whose restrictions are closed immersions although the whole
  morphism is not; hence source locality fails.
]

===== Flat

#definition(number: none, title: "Flat Ring Map")[
  A ring map $A -> B$ is *flat* if $B$ is a flat $A$-module, that is, tensoring
  an exact sequence of $A$-modules with $B$ preserves exactness.
]

#proposition(title: "Locality Profile: Flat")[
  Flatness satisfies BC, T, S, GS, and GT.
]

#proof[
  Module flatness is stable under tensor-product base change and composition,
  and every localization is flat.  These facts give BC, T, S, and PL.
  To prove GS, use the criterion that $B$ is flat over $A$ exactly when, for
  every injection $M' -> M$ of $A$-modules, the induced map
  $M' tensor_A B -> M tensor_A B$ is injective.  After localizing at every
  $g_i$, this map is injective by hypothesis.  Its kernel localizes to zero
  at each $g_i$; because the $g_i$ generate the unit ideal, the kernel itself
  is zero.  Hence $B$ is flat over $A$.  Finally GS and PL imply GT by the
  principal-target-extension argument above.  Strong Affine Locality then
  gives source and target locality for flat morphisms.
]

#corollary(title: "Flat Morphisms")[
  Flatness of a morphism may be checked on affine pairs, or equivalently on
  the local maps $shf.o_(Y,f(x)) -> shf.o_(X,x)$.  It is strongly affine local,
  Zariski local on both source and target, and stable under base change.
]

#proof[
  The affine-pair criterion follows from the preceding locality package.
  On an affine pair $ops.spec B -> ops.spec A$, the stalk map at the prime
  $q subset.eq B$, with inverse image $p subset.eq A$, is the localized ring
  map $A_p -> B_q$.  Flatness of $A -> B$ implies flatness of all these maps
  by localization.  Conversely, if every $A_p -> B_q$ is flat, then for each
  prime $q$ the localization $B_q$ is flat over $A$ by composition with the
  flat map $A -> A_p$; flatness of $B$ over $A$ follows because it may be
  checked after localization at all primes of $B$.  Thus the affine and stalk
  criteria agree.  BC for rings, followed by affine locality, gives BC for
  morphisms.
]

===== Faithfully flat

#definition(number: none, title: "Faithfully Flat Ring Map")[
  A ring map $A -> B$ is *faithfully flat* if $B$ is flat over $A$ and the
  functor $- tensor_A B$ detects exactness.  Equivalently, $A -> B$ is flat and
  $ops.spec B -> ops.spec A$ is surjective.
]

#proposition(title: "Locality Profile: Faithfully Flat")[
  Faithful flatness satisfies BC, T, and GT, but it satisfies neither S nor
  GS when empty distinguished covers are allowed.  GS does hold for
  nonempty finite distinguished covers.
]

#proof[
  Use the equivalence between faithful flatness of $A -> B$ and the
  conjunction of flatness with surjectivity of
  $ops.spec B -> ops.spec A$.  Both conditions survive base change, so BC
  and hence T hold.  Under GS hypotheses for a nonempty indexing family,
  flatness glues and any member's faithfully flat map already surjects onto
  $ops.spec A$.
  Thus the whole spectrum map is surjective.  Under GT hypotheses
  flatness again glues,
  and surjectivity is checked over the covering $D(a_i)$ of $ops.spec A$.
  If that target cover is empty, $A$ and hence $B$ are zero rings, and
  faithful flatness holds.  This proves nonempty-cover GS and unrestricted
  GT.  The examples disprove S and unrestricted GS.
]

#example(title: "Why Source Gluing Fails for the Empty Cover")[
  Take $A=k$ and $B=0$, the zero ring.  The empty family generates the
  unit ideal in $B$ because $0=1$, and all its localized-map hypotheses
  hold vacuously.  But $k -> 0$ is not faithfully flat: the nonzero
  $k$-module $k$ tensors to zero.  Thus GS fails when the empty distinguished
  cover of the zero ring is admitted.  If GS is instead formulated only for
  nonempty finite distinguished covers, faithful flatness does satisfy it;
  that is a different convention.
]

#example(title: "Failure of S for faithful flatness")[
  The identity $k[t] -> k[t]$ is faithfully flat.  The source localization
  $k[t] -> k[t,t^(-1)]$ is flat but not faithfully flat: tensoring the nonzero
  module $k[t]\/(t)$ with $k[t,t^(-1)]$ gives zero.
]

#corollary(title: "Faithfully Flat Morphisms")[
  A faithfully flat ring map gives an affine, flat, surjective morphism of
  spectra.  For a general morphism, faithful flatness means flatness together
  with surjectivity.  It is stable under base change and local on the target,
  but it is not local on the source; its surjectivity cannot be checked on
  every small affine pair.
]

#proof[
  On affine spectra, the equivalence in the preceding proof identifies a
  faithfully flat ring map with a flat and surjective morphism.  This
  identification is compatible with restriction to affine targets, so for
  general schemes faithful flatness is equivalent to flatness together with
  surjectivity.  Both properties are local on the target and stable under
  base change, hence so is their conjunction.  The localization example
  shows that an open-source restriction can destroy surjectivity and rules
  out source locality.  Gluing a family of surjective restrictions and
  demanding that every restriction be surjective are different tests.
]

==== Geometric-property case studies

The next properties are not properties of one arbitrary ring map.  They are
best tested using RS, GSS, RT, and GTT directly.

===== Quasi-compact

#definition(number: none, title: "Quasi-compact Morphism")[
  A morphism $f:X -> Y$ is *quasi-compact* if $f^(-1)(V)$ is quasi-compact for
  every quasi-compact open $V subset.eq Y$.  It is enough to test affine opens
  $V subset.eq Y$.
]

#proposition(title: "Locality Profile: Quasi-compact")[
  Quasi-compactness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[
  Let $V=ops.spec A subset.eq Y$.  If $f^(-1)(V)$ is quasi-compact, then the
  inverse image of a distinguished open $D(a) subset.eq V$ is the
  nonvanishing locus of the pulled-back section.  Choose finitely many affine
  charts covering $f^(-1)(V)$; on each chart that locus is distinguished and
  hence quasi-compact.  Their finite union is quasi-compact, proving target
  restriction.  Conversely, quasi-compact inverse images over a finite
  distinguished cover of $V$ have quasi-compact union, proving target gluing.
  Quasi-compactness of affine targets upgrades these distinguished tests to
  arbitrary target covers.

  For base change, work over affine bases and cover the quasi-compact source
  by finitely many affine opens.  Their pullbacks are affine and form a finite
  cover of the new source, which is therefore quasi-compact.  Target locality
  glues this calculation.  The examples prove the two source failures.
]

#example(title: "Source failures for quasi-compactness")[
  Let $A=k[x_1,x_2,dots]$ and
  $U=union_(i>=1) D(x_i) subset.eq ops.spec A$.  The identity of $ops.spec A$ is
  quasi-compact, but its restriction $U -> ops.spec A$ is not, so RS fails.

  An infinite disjoint union of points is covered by quasi-compact open
  components, but its map to one point is not quasi-compact.  Thus GSS fails.
]

#corollary(title: "Target Criterion for Quasi-compactness")[
  Quasi-compactness is affine local and Zariski local on the target, and it is
  stable under base change.  It is not local on the source.
]

===== Affine

#definition(number: none, title: "Affine Morphism")[
  A morphism $f:X -> Y$ is *affine* if $f^(-1)(V)$ is affine for every affine
  open $V subset.eq Y$.
]

#proposition(title: "Locality Profile: Affine")[
  Affineness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[
  Let $V=ops.spec A subset.eq Y$ and suppose $f^(-1)(V)=ops.spec B$.
  The inverse image of $D(a)$ is the distinguished affine
  $ops.spec B_a$, proving RT on distinguished opens.  Conversely, if the
  inverse images of a finite distinguished cover $D(a_i)$ are affine, the
  pullbacks of the $a_i$ are global sections of $f^(-1)(V)$ whose
  nonvanishing loci are precisely those affine inverse images.  The canonical
  map to the spectrum of global sections is an isomorphism on these loci;
  the local isomorphisms agree on overlaps and glue, so $f^(-1)(V)$ is affine.
  An affine target is quasi-compact, so distinguished refinements extend this
  to arbitrary target covers and prove GTT.

  After an affine base change $ops.spec A' -> ops.spec A$, the pullback is
  $ops.spec tensor(B, A', over: A)$ and is affine.  Target locality glues these
  affine computations, proving BC.  Neither argument asserts that a union of
  arbitrary affine source opens is affine; the examples show why.
]

#example(title: "Source failures for affineness")[
  The morphism $sch.a^2_k -> ops.spec k$ is affine, while the restriction
  $(sch.a^2_k minus {0}) -> ops.spec k$ is not affine; hence RS fails.

  The two standard affine lines cover $sch.p^1_k$, but
  $sch.p^1_k -> ops.spec k$ is not affine.  Hence GSS fails.
]

#corollary(title: "Target Criterion for Affineness")[
  Affineness is affine local and Zariski local on the target and is stable
  under base change.  It is not local on the source.
]

===== Separated

#definition(number: none, title: "Separated Morphism")[
  A morphism $f:X -> Y$ is *separated* if its diagonal
  $Delta_f:X -> fiber(X, X, base: Y)$ is a closed immersion.
]

#proposition(title: "Locality Profile: Separated")[
  Separatedness satisfies RS, RT, and GTT and is stable under base change.  It
  does not satisfy GSS.
]

#proof[
  The diagonal of a base change of $f$ is the base change of $Delta_f$.
  Since closed immersions are stable under base change, separatedness is also
  stable under base change.  For a target
  cover $Y=union_i V_i$, the opens
  $f^(-1)(V_i) times_(V_i) f^(-1)(V_i)$ cover $fiber(X, X, base: Y)$,
  so target locality for closed immersions gives RT and GTT.  Restricting
  the source to $U$ pulls the diagonal back to the open
  $fiber(U, U, base: Y)$, proving RS.  A source cover does not generally
  cover the fiber product by these self-products: the mixed products
  still have to be checked.  This accounts for the doubled-origin
  counterexample to GSS.
]

#example(title: "Failure of source gluing for separatedness")[
  The affine line with doubled origin is covered by two copies of
  $sch.a^1_k$, each separated over $ops.spec k$, but the doubled-origin line
  itself is not separated.  Thus GSS fails.
]

#corollary(title: "Target Criterion for Separatedness")[
  Separatedness is affine local and Zariski local on the target and is stable
  under base change.  It is preserved by restriction to an open source, but
  it is not local on the source because source gluing fails.
]

===== Universally closed

#definition(number: none, title: "Universally Closed Morphism")[
  A morphism $f:X -> Y$ is *universally closed* if every base change
  $f':fiber(X, Y', base: Y) -> Y'$ is a closed map on underlying topological
  spaces.
]

#proposition(title: "Locality Profile: Universally Closed")[
  Universal closedness satisfies RT and GTT and is stable under base change.
  It satisfies neither RS nor GSS.
]

#proof[
  A further base change of a base change of $f$ is again a base change of
  $f$, so universal closedness is stable under base change.
  Closedness of a continuous map is local on the target: for a closed
  $Z subset.eq X$, check $f(Z) inter V_i$ in each member of an open target
  cover.  Apply this after every base change, whose pulled-back target
  opens still cover.  This proves RT and GTT.  The examples give the source
  failures.
]

#example(title: "Source failures for universal closedness")[
  The morphism $sch.p^1_k -> ops.spec k$ is universally closed, but its open
  restriction $sch.a^1_k -> ops.spec k$ is not; hence RS fails.

  For the latter assertion, base change to $sch.a^1_k$ and project
  $sch.a^2_k -> sch.a^1_k$.  The closed hyperbola $V(x y-1)$ has image
  $D(x)$, which is not closed.  Thus it is universal closedness, not
  closedness of the original map to a point, that fails.

  Assume $k$ is algebraically closed and infinite.  Map the disjoint union
  $coprod(ops.spec k, a in k)$ to $sch.a^1_k$ by sending its $a$-component to
  the closed point $a$.  Every component map is a closed immersion, hence
  universally closed, but their union has image equal to the set of closed
  points, which is not closed.  Thus GSS fails.
]

#corollary(title: "Target Criterion for Universal Closedness")[
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

#remark(title: "A Procedure for Checking Locality")[
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
