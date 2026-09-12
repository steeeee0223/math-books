#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== A Locality Calculus for Morphisms

Many definitions in algebraic geometry begin with a property of a ring map
$A -> B$ and then pass to affine charts.  We follow mathlib's proofs of this
passage: affine-open induction, target-local affine properties, and properties
of all affine pairs.  The letters below name the operations used in those
proofs; they are not additional definitions from Hartshorne.

The source references in this section refer to mathlib commit
`e281a66114fe17935e6ea7917a01b714d0c1e493`.  The companion file
`local-props-mathlib.md` records the declarations and the distinction between
direct source proofs and deductions from them.  These are mathematical
expositions of the proofs, not a Lean verification of this text.

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

  This is mathlib's `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`.
  Its `Source` in the composition hypothesis means the ring-theoretic
  source $A$.  PL is not a field of `RingHom.PropertyIsLocal`; mathlib uses
  it to construct the GT field for finite type, finite presentation, and
  flatness.
]

#remark(title: "The mathlib dictionary")[
  With isomorphisms of localizations understood, the correspondence is:

  - T: `RingHom.LocalizationAwayPreserves`.
  - S: `RingHom.StableUnderCompositionWithLocalizationAwayTarget`.
  - GS: `RingHom.OfLocalizationSpanTarget`.
  - GT: `RingHom.OfLocalizationSpan`.
  - PL: `RingHom.StableUnderCompositionWithLocalizationAwaySource`.
  - BC: `RingHom.IsStableUnderBaseChange`.

  `RingHom.PropertyIsLocal` packages T, GS, GT, and S.  It does not require
  BC, PL, or stability under arbitrary composition.  Isomorphism invariance
  is built into the use of arbitrary models of localization in its T field.
]

#proposition(number: none, title: "Base Change Contains Target Localization")[

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

#proposition(number: none, title: "Affine Locality Principle")[
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

#proposition(number: none, title: "Affine Communication Lemma (Fixed Target)")[
  Let $f:X -> ops.spec A$ be a morphism.  Suppose $P$ satisfies S and GS.  If
  $X$ has an affine cover $U_i=ops.spec B_i$ such that every
  $A -> B_i$ has $P$, then $A -> Gamma(U, shf.o_X)$ has $P$ for every affine
  open $U subset.eq X$.
]

#proof[
  This is the affine-open induction in mathlib's `of_affine_open_cover`,
  as used by `HasRingHomProperty.of_source_openCover`.

  Put $U=ops.spec B$.  For $x in U inter U_i$, choose a neighborhood which
  is distinguished in both affine opens:
  $
    x in W = D_U(g) = D_(U_i)(h).
  $
  Such neighborhoods exist by `exists_basicOpen_le_affine_inter`.  To see
  the construction, first choose $x in D_U(a) subset.eq U inter U_i$, then
  $x in D_(U_i)(h) subset.eq D_U(a)$.  The restriction of $h$ to $D_U(a)$
  has the form $c/a^n$, so $D_(U_i)(h)=D_U(a c)$.

  By S applied in $U_i$, the map $A -> Gamma(W, shf.o_X)$ has $P$.
  Isomorphism invariance identifies this with $A -> B_g$.  These $W$ cover
  $U$; quasi-compactness selects finitely many, and their defining elements
  generate the unit ideal of $B$.  GS gives $P(A -> B)$.

  The simultaneous distinguished neighborhood is essential: mere inclusion
  $D_U(g) subset.eq U_i$ does not make $g$ a section on $U_i$.
]

#proposition(number: none, title: "Exactly what fixed-target communication requires")[
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

#proposition(number: none, title: "Strong Affine Locality via PropertyIsLocal")[
  Suppose $P$ satisfies T, S, GS, and GT.  If one system of affine charts for
  $f:X -> Y$ has $P$, then the ring map associated with every affine pair for
  $f$ has $P$.  In this situation the resulting morphism property is *strongly
  affine local*.  It is Zariski local on both source and target.
]

#proof[
  Following `sourceAffineLocally_isLocal`, for an affine target
  $V=ops.spec A$ let $H(V)$ mean that every affine open of $f^(-1)(V)$
  has a ring map from $A$ with $P$.

  First, S and GS give $H(V_i)$ on each member of the original target
  cover, by fixed-target communication.

  Second, $H(V)$ implies $H(D(a))$.  If $U=ops.spec B$ lies over $D(a)$,
  then $P(A -> B)$ holds and the image of $a$ is a unit in $B$.  T and
  $B_a simeq B$ give $P(A_a -> B)$.

  Third, suppose the $D(a_i)$ cover $V$ and $H(D(a_i))$ holds.  For any
  affine $U=ops.spec B subset.eq f^(-1)(V)$, the opens
  $U inter f^(-1)(D(a_i))=ops.spec B_(a_i)$ give
  $P(A_(a_i) -> B_(a_i))$.  GT gives $P(A -> B)$, hence $H(V)$.

  Apply affine-open induction on $Y$ to these last two steps.  This is
  `HasAffineProperty.of_iSup_eq_top`: $H$ holds on every affine target,
  which proves the assertion about every affine pair.

  Restriction to an open source or target preserves the all-affine-pairs
  condition.  For source gluing, restrict to an affine target, refine the
  source cover by affine opens, and use fixed-target communication.  For
  target gluing, refine the target cover by affine opens and use the
  target induction just proved.  These are the source and target locality
  instances supplied by `HasRingHomProperty`.
]

#remark(title: "Necessity has a specified meaning")[
  If a scheme-morphism property $Q$ is local on both source and target and
  $Q(ops.spec B -> ops.spec A)$ is equivalent to $P(A -> B)$, then T, S,
  GS, and GT are necessary: apply restriction and gluing to distinguished
  covers of the two spectra.  Conversely, the preceding proof constructs
  such a $Q$ from these four conditions, namely `affineLocally P`.
  In particular its value on an affine morphism between spectra is $P$,
  by fixed-target communication and target induction.

  Mathlib records the converse in
  `HasRingHomProperty.isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget`.
  This is a characterization of extension to a property local on both
  sides, not a claim that the four fields are logically independent.
  Properties local only on the target, such as finite morphisms, do not
  require S or GS.  BC is a separate stability question.  PL is an optional
  sufficient ingredient for constructing GT, not an additional requirement
  of this characterization.
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

#proposition(number: none, title: "The affineAnd target-local route")[
  Suppose $P$ respects isomorphisms and satisfies T and GT.  Define $Q(f)$
  by requiring, for every affine $V=ops.spec A$ in the target, that the
  entire inverse image be affine, $f^(-1)(V)=ops.spec B$, and that
  $P(A -> B)$ hold.  Then $Q$ is Zariski local on the target.  If P also
  satisfies BC, so does Q.
]

#proof[
  This is `affineAnd_isLocal`, followed by `HasAffineProperty`.
  On an affine target, restriction to $D(a)$ replaces the whole inverse
  image $ops.spec B$ by $ops.spec B_a$; use T.

  For a distinguished target cover $D(a_i)$, suppose each whole inverse
  image $X_i$ is affine and has $P$.  The pullbacks of the $a_i$ are global
  sections of $X$, generate the unit ideal in $Gamma(X, shf.o_X)$, and
  have affine nonvanishing loci $X_i$.  The affineness criterion
  `isAffine_of_isAffineOpen_basicOpen` gives that $X$ is affine.
  Its proof compares $X$ with $ops.spec Gamma(X, shf.o_X)$ on these
  distinguished opens and glues the isomorphisms.  Once $X$ is affine,
  GT applies to its global ring map.  Affine-open induction on the target
  then proves target locality for arbitrary open covers.

  For BC, reduce both base schemes to affine opens using target locality.
  The pullback of the affine source is the spectrum of the tensor product,
  where ring-theoretic BC applies.  This is
  `affineAnd_isStableUnderBaseChange` and
  `HasAffineProperty.isStableUnderBaseChange`.
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

#corollary(number: none, title: "Zariski Locality")[
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

#proposition(number: none, title: "Locality Profile: Finite Type")[
  Finite type satisfies BC, T, S, GS, and GT.
]

#proof[
  Follow `RingHom.finiteType_isLocal`.  Tensor products preserve a finite
  set of algebra generators, giving BC and hence T.  A principal
  localization is generated by one inverse; together with composition
  stability this gives S and PL.  The substantive gluing input is
  `Algebra.FiniteType.of_span_eq_top_target`, giving GS.  It constructs
  finitely many global generators as follows.  Choose coefficients $c_i$
  with $sum_i c_i g_i=1$ and let $C$ be the $A$-subalgebra generated by
  the $g_i$, the $c_i$, and numerators of finite generating sets for the
  $B_(g_i)$.  For $b in B$, clearing denominators gives
  $g_i^(n_i) b in C$.  The powers $g_i^(n_i)$ still generate the unit ideal
  in $C$, so $b in C$.  Hence $C=B$.  Finally GS and PL give GT by
  `OfLocalizationSpanTarget.ofLocalizationSpan`.
]

#corollary(number: none, title: "Locally Finite-type Morphisms")[
  The corresponding chartwise property is *locally of finite type*.  It is
  strongly affine local, Zariski local on both source and target, and stable
  under base change.  A morphism is of finite type precisely when it is locally
  of finite type and quasi-compact.
]

#proof[
  The `HasRingHomProperty` instance in `Morphisms/FiniteType.lean` applies
  the preceding four-field locality theorem to finite type.  BC is then
  transported separately by `HasRingHomProperty.isStableUnderBaseChange`.
  To compare with Hartshorne's cover definition, use the equivalence of one
  affine atlas and every affine pair.  Requiring finitely many source charts
  over each affine target is exactly quasi-compactness in addition to the
  local finite-type condition.
]

===== Finite presentation

#definition(number: none, title: "Finite Presentation Ring Map")[
  A ring map $A -> B$ is *of finite presentation* if
  $B simeq A[x_1, dots, x_n]\/ideal((r_1, dots, r_m))$ for finite lists of
  generators and relations.
]

#proposition(number: none, title: "Locality Profile: Finite Presentation")[
  Finite presentation satisfies BC, T, S, GS, and GT.
]

#proof[
  The construction is `RingHom.finitePresentation_isLocal`.  Finite
  presentations survive tensor products, giving BC and T.  The presentation
  $A_a simeq A[t]\/ideal((a t-1))$, together with composition stability,
  gives S and PL.  GS is the algebraic gluing theorem
  `Algebra.FinitePresentation.of_span_eq_top_target`: it first obtains
  finite type, then glues finite generation of the relation ideal after
  localization.  More precisely, start with a finite polynomial algebra
  surjecting onto $B$.  Lifts of the $g_i$ need not generate its unit ideal.
  Mathlib first imposes the single relation $sum_i tilde(g)_i tilde(c)_i=1$
  for lifts of a unit-ideal expression in $B$.  In this finitely presented
  intermediate algebra the lifted opens do cover.  Local finite
  presentation gives finitely generated localized kernels, and
  `RingHom.ker_fg_of_localizationSpan` glues their finite generation.
  GS and PL give GT.  The corresponding
  `HasRingHomProperty` instance supplies the following corollary.
]

#corollary(number: none, title: "Locally Finite-presentation Morphisms")[
  The corresponding chartwise property is *locally of finite presentation*.
  It is strongly affine local, Zariski local on both source and target, and
  stable under base change.
]

===== Finite

#definition(number: none, title: "Finite Ring Map")[
  A ring map $A -> B$ is *finite* if $B$ is a finitely generated $A$-module.
]

#proposition(number: none, title: "Locality Profile: Finite")[
  Finite satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[
  `RingHom.finite_isStableUnderBaseChange` transports finite module
  generators through tensor products.  T follows.  For GT,
  `RingHom.finite_ofLocalizationSpan` lifts finite generating sets from
  the localizations and clears denominators.  For each $b in B$, a power
  of each covering element times $b$ lies in the span of these lifts;
  the unit-ideal condition then puts $b$ itself in that span.

  GS follows from integral GS proved below and finite-type GS, using
  the equivalence of module-finiteness with integrality plus finite type.
  This is a deduction from those results, not a GS field used by mathlib's
  finite-morphism locality construction.  The example proves failure of S.
]

#example(title: "Failure of S for finite maps")[
  The identity $k[t] -> k[t]$ is finite, but the source localization
  $k[t] -> k[t,t^(-1)]$ is not finite as a map of $k[t]$-modules.
]

#corollary(number: none, title: "Finite Morphisms")[
  A morphism $f:X -> Y$ is finite if, over every affine open
  $V=ops.spec A subset.eq Y$, the whole inverse image is
  $f^(-1)(V)=ops.spec B$ with $A -> B$ finite.  This criterion is affine local
  and Zariski local on the target.  Finite morphisms are stable under base
  change, but finiteness is not local on the source and is not strongly affine
  local on arbitrary affine pairs.
]

#proof[
  The `HasAffineProperty` instance in `Morphisms/Finite.lean` uses
  `affineAnd` with ring finiteness,
  feeding it T and GT.  It therefore proves equivalence of Hartshorne's
  existence-of-an-affine-cover definition with the every-affine-target
  criterion.  The affineAnd route also transports BC.  The displayed
  failure of S is a failure of restriction to an open source, so source
  locality fails even though ring GS holds.
]

===== Integral

#definition(number: none, title: "Integral Ring Map")[
  A ring map $A -> B$ is *integral* if every $b in B$ satisfies a monic
  polynomial with coefficients in $A$.
]

#proposition(number: none, title: "Locality Profile: Integral")[
  Integral satisfies BC, T, GS, and GT, but it does not satisfy S.
]

#proof[
  Use `RingHom.isIntegral_isStableUnderBaseChange` for BC and hence T.
  For GT, `RingHom.isIntegral_ofLocalizationSpan` clears denominators in
  local monic equations.  A power of each covering element times a given
  $b in B$ belongs to the integral closure of $A$ in $B$; gluing membership
  in this $A$-submodule shows that $b$ belongs to the integral closure.

  For GS we use a consequence of mathlib's geometric characterization
  `IsIntegralHom.iff_universallyClosed_and_isAffineHom`.  This
  characterization uses T and GT, not GS.  If finitely many $D(g_i)$ cover
  $ops.spec B$ and their maps to $ops.spec A$ are integral, these maps are
  universally closed.  After any base change, the image of a closed subset
  of the whole source is the finite union of its images from the $D(g_i)$;
  each is closed.  Hence the whole affine morphism is universally closed
  and therefore integral.  This derives ring GS without claiming that
  integral morphisms are local on arbitrary open source covers.  The
  following example proves failure of S.
]

#example(title: "Failure of S for integral maps")[
  The identity $k[t] -> k[t]$ is integral.  The source localization
  $k[t] -> k[t,t^(-1)]$ is not integral because $t^(-1)$ is not integral over
  $k[t]$.
]

#corollary(number: none, title: "Integral Morphisms")[
  A morphism is integral exactly when inverse images of affine targets are
  affine and induce integral ring maps.  Integral morphisms are affine local
  and Zariski local on the target and are stable under base change.  They are
  not local on the source and not strongly affine local on arbitrary affine
  pairs.
]

#proof[
  `IsIntegralHom.hasAffineProperty` uses the affineAnd route with T and GT;
  its base-change instance uses ring BC.  The open restriction in the
  example is not integral, which rules out source locality.
]

===== Surjective

#definition(number: none, title: "Surjective Ring Map")[
  A ring map $A -> B$ is *surjective* if every element of $B$ is the image of
  an element of $A$, equivalently $B simeq A\/I$ for some ideal $I subset.eq A$.
]

#proposition(number: none, title: "Locality Profile: Surjective")[
  Surjectivity satisfies BC, T, and GT, but it satisfies neither S nor GS.
]

#proof[
  `RingHom.surjective_isStableUnderBaseChange` proves BC by expressing
  tensors as sums of pure tensors and lifting their $B$-entries to $A$.
  Thus T follows.  For GT, `RingHom.surjective_ofLocalizationSpan` treats
  the image of $A -> B$ as an $A$-submodule: local surjectivity and clearing
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

#corollary(number: none, title: "Closed Immersions")[
  Contravariantly, a surjective ring map $A -> B$ gives a closed immersion
  $ops.spec B -> ops.spec A$.  Closed immersions are affine local and Zariski
  local on the target and are stable under base change.  They are not local on
  the source and not strongly affine local on arbitrary affine pairs.
]

#proof[
  Mathlib defines `IsClosedImmersion` by a closed embedding of underlying
  spaces and surjectivity on stalks.  This matches Hartshorne's closed-image
  homeomorphism and surjective sheaf map: sheaf surjectivity is tested on
  stalks, not on sections of every open set.  Its target-locality instance
  comes first, from target locality of these two conditions.

  `IsClosedImmersion.hasAffineProperty` then identifies the affine-target
  criterion as affine source plus a surjective global ring map.  BC is
  transported from ring surjectivity using that criterion.  The failure of
  S above rules out source locality; the diagonal $k -> k times k$ also
  gives a source-gluing failure for the corresponding two-point morphism.
]

===== Flat

#definition(number: none, title: "Flat Ring Map")[
  A ring map $A -> B$ is *flat* if $B$ is a flat $A$-module, that is, tensoring
  an exact sequence of $A$-modules with $B$ preserves exactness.
]

#proposition(number: none, title: "Locality Profile: Flat")[
  Flatness satisfies BC, T, S, GS, and GT.
]

#proof[
  Follow `RingHom.Flat.propertyIsLocal`.  Module flatness is stable under
  tensor-product base change and composition, and localizations are flat.
  These give BC, T, S, and PL.  The gluing input for GS is
  `Module.flat_of_isLocalized_span`: localizing a tensor-product
  injectivity test at a unit-ideal cover detects whether its kernel is
  zero.  GS and PL give GT.  The `HasRingHomProperty` instance in
  `Morphisms/Flat.lean` then supplies source and target locality.
]

#corollary(number: none, title: "Flat Morphisms")[
  Flatness of a morphism may be checked on affine pairs, or equivalently on
  the local maps $shf.o_(Y,f(x)) -> shf.o_(X,x)$.  It is strongly affine local,
  Zariski local on both source and target, and stable under base change.
]

#proof[
  The affine-pair criterion follows from the preceding locality package.
  For the comparison with Hartshorne's stalk definition, mathlib uses
  `RingHom.Flat.localRingHom` in one direction and
  `RingHom.Flat.ofLocalizationPrime` in the other.  A stalk map on an
  affine pair is the corresponding localization at a prime and its inverse
  image.  The resulting comparison is `Flat.iff_flat_stalkMap`; it uses
  an additional local algebra theorem, not merely a change of notation.
  Ring BC transports to scheme BC separately.
]

===== Faithfully flat

#definition(number: none, title: "Faithfully Flat Ring Map")[
  A ring map $A -> B$ is *faithfully flat* if $B$ is flat over $A$ and the
  functor $- tensor_A B$ detects exactness.  Equivalently, $A -> B$ is flat and
  $ops.spec B -> ops.spec A$ is surjective.
]

#proposition(number: none, title: "Locality Profile: Faithfully Flat")[
  Faithful flatness satisfies BC, T, and GT, but it satisfies neither S nor
  GS when empty distinguished covers are allowed.  GS does hold for
  nonempty finite distinguished covers.
]

#proof[
  Use `RingHom.FaithfullyFlat.isStableUnderBaseChange` for BC and T, and
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` for gluing.
  Under GS hypotheses for a nonempty indexing family, flatness glues and
  any member's faithfully flat map already surjects onto $ops.spec A$.
  Thus the whole spectrum map is surjective.  Under GT hypotheses
  flatness again glues,
  and surjectivity is checked over the covering $D(a_i)$ of $ops.spec A$.
  If that target cover is empty, $A$ and hence $B$ are zero rings, and
  faithful flatness holds.  These arguments deduce nonempty-cover GS and
  unrestricted GT from the equivalence; they are not a `PropertyIsLocal`
  instance.  The examples disprove S and unrestricted GS.
]

#example(title: "The empty-cover obstruction to GS")[
  Take $A=k$ and $B=0$, the zero ring.  The empty family generates the
  unit ideal in $B$ because $0=1$, and all its localized-map hypotheses
  hold vacuously.  But $k -> 0$ is not faithfully flat: the nonzero
  $k$-module $k$ tensors to zero.  Thus GS as defined in
  `RingHom.OfLocalizationSpanTarget` fails.  If one instead requires
  $n>=1$ in the definition of GS, the faithfully-flat GS entry becomes
  yes; that is a different convention.
]

#example(title: "Failure of S for faithful flatness")[
  The identity $k[t] -> k[t]$ is faithfully flat.  The source localization
  $k[t] -> k[t,t^(-1)]$ is flat but not faithfully flat: tensoring the nonzero
  module $k[t]\/(t)$ with $k[t,t^(-1)]$ gives zero.
]

#corollary(number: none, title: "Faithfully Flat Morphisms")[
  A faithfully flat ring map gives an affine, flat, surjective morphism of
  spectra.  For a general morphism, faithful flatness means flatness together
  with surjectivity.  It is stable under base change and local on the target,
  but it is not local on the source; its surjectivity cannot be checked on
  every small affine pair.
]

#proof[
  Mathlib's `flat_and_surjective_iff_faithfullyFlat_of_isAffine` supplies
  the affine comparison.  For general schemes use the conjunction of
  flatness and surjectivity, both of which are target local and stable
  under base change.  The example shows that restriction to an open source
  can destroy surjectivity.  Gluing a family of surjective restrictions
  and demanding that every restriction be surjective are different tests.
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

#proposition(number: none, title: "Locality Profile: Quasi-compact")[
  Quasi-compactness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[
  Mathlib uses `HasAffineProperty` with the affine-target property
  that the whole source is quasi-compact.  A basic open of a global section
  in a quasi-compact scheme is quasi-compact: take finitely many affine
  charts and restrict the section on each.  This gives distinguished
  target restriction.  A finite union of quasi-compact inverse images is
  quasi-compact, giving distinguished target gluing.  Affine-open
  induction upgrades these to RT and GTT.  For BC, over affine bases cover
  the quasi-compact source by finitely many affine opens; their pullbacks
  are affine and still form a finite cover.  The examples prove the two
  source failures.
]

#example(title: "Source failures for quasi-compactness")[
  Let $A=k[x_1,x_2,dots]$ and
  $U=union_(i>=1) D(x_i) subset.eq ops.spec A$.  The identity of $ops.spec A$ is
  quasi-compact, but its restriction $U -> ops.spec A$ is not, so RS fails.

  An infinite disjoint union of points is covered by quasi-compact open
  components, but its map to one point is not quasi-compact.  Thus GSS fails.
]

#corollary(number: none, title: "Target Criterion for Quasi-compactness")[
  Quasi-compactness is affine local and Zariski local on the target, and it is
  stable under base change.  It is not local on the source.
]

===== Affine

#definition(number: none, title: "Affine Morphism")[
  A morphism $f:X -> Y$ is *affine* if $f^(-1)(V)$ is affine for every affine
  open $V subset.eq Y$.
]

#proposition(number: none, title: "Locality Profile: Affine")[
  Affineness satisfies RT and GTT and is stable under base change.  It
  satisfies neither RS nor GSS.
]

#proof[
  The `HasAffineProperty` instance for `IsAffineHom` takes affineness of
  the entire source as its affine-target property.  Distinguished target
  restriction gives a distinguished open in an affine scheme.  Gluing
  uses `isAffine_of_isAffineOpen_basicOpen`, as in the affineAnd proof,
  followed by affine-open induction.  BC reduces to the affine tensor
  product description of pullbacks.  Neither argument asserts affineness
  of a union of arbitrary affine source opens; the examples show why.
]

#example(title: "Source failures for affineness")[
  The morphism $sch.a^2_k -> ops.spec k$ is affine, while the restriction
  $(sch.a^2_k minus {0}) -> ops.spec k$ is not affine; hence RS fails.

  The two standard affine lines cover $sch.p^1_k$, but
  $sch.p^1_k -> ops.spec k$ is not affine.  Hence GSS fails.
]

#corollary(number: none, title: "Target Criterion for Affineness")[
  Affineness is affine local and Zariski local on the target and is stable
  under base change.  It is not local on the source.
]

===== Separated

#definition(number: none, title: "Separated Morphism")[
  A morphism $f:X -> Y$ is *separated* if its diagonal
  $Delta_f:X -> fiber(X, X, base: Y)$ is a closed immersion.
]

#proposition(number: none, title: "Locality Profile: Separated")[
  Separatedness satisfies RS, RT, and GTT and is stable under base change.  It
  does not satisfy GSS.
]

#proof[
  `isSeparated_eq_diagonal_isClosedImmersion` expresses separatedness as
  the diagonal construction applied to closed immersions.  Diagonals
  commute with base change; use BC for closed immersions.  For a target
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

#corollary(number: none, title: "Target Criterion for Separatedness")[
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

#proposition(number: none, title: "Locality Profile: Universally Closed")[
  Universal closedness satisfies RT and GTT and is stable under base change.
  It satisfies neither RS nor GSS.
]

#proof[
  `universallyClosed_eq` writes the property as universalization of
  closedness of the underlying map.  BC follows by composing base changes.
  Closedness of a continuous map is local on the target: for a closed
  $Z subset.eq X$, check $f(Z) inter V_i$ in each member of an open target
  cover.  Apply this after every base change, whose pulled-back target
  opens still cover.  This is the proof of
  `universallyClosed_isZariskiLocalAtTarget` using
  `universally_isZariskiLocalAtTarget`.  The examples give the source
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

#corollary(number: none, title: "Target Criterion for Universal Closedness")[
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

#remark(title: "Locality Checklist")[
  When studying a new property, proceed in the following order.

  + Distinguish the all-affine-pairs route from the affine-whole-inverse-image
    route before choosing hypotheses.
  + Use T and S for affine refinements.  For a fixed affine target, S and GS
    give affine communication.
  + For all affine pairs use T, S, GS, and GT, as in `PropertyIsLocal`.
    PL can help prove GT, but is not an additional required field.
  + For an affine whole inverse image with a ring property, use T and GT
    in `affineAnd`, then target-local `HasAffineProperty`.
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
