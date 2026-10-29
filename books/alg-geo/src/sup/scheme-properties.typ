#import "@preview/fletcher:0.5.8" as fletcher: *
#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

#supplement-numbering("XP")

== XP — Topology and intrinsic properties of schemes <sup-xp>

The definitions of connected, irreducible, reduced, integral, and
(locally) Noetherian schemes, and their initial criteria, remain in
#book-link(<text-ii-3>)[II.3, Propositions 3.1–3.2 and surrounding definitions].

=== Generic points and specialization <sup-xp-generic-points>

A topological space is _sober_ if every nonempty irreducible closed subset
has a unique generic point. A _Zariski space_ is a Noetherian sober space,
as in Ex. II.3.17.

#proposition(key: "sup-xp-1", title: "Existence and uniqueness")[
  + Every scheme is sober, without a Noetherian hypothesis. On $ops.spec A$,
    the generic point of $V(idl.p)$ is $idl.p$ for each prime $idl.p$.
    (Ex. II.2.9)
  + For any topological space $Y$, let $t(Y)$ be the set of its nonempty
    irreducible closed subsets, with opens
    $t(U)={C in t(Y) | C inter U != emptyset}$ for opens $U subset Y$.
    Then $t(Y)$ is sober, and $U mapsto t(U)$ is an isomorphism of lattices
    of open subsets. In particular, $Y$ is Noetherian if and only if
    $t(Y)$ is Noetherian.
  + The canonical map $Y to t(Y)$, $y mapsto overline({y})$, is a
    homeomorphism if and only if $Y$ is sober.
]

#proof[

  + *Find a prime on an affine chart.* Let $C$ be the closed irreducible subset and choose an affine open
    $U=ops.spec A$ meeting it. The nonempty open $C inter U$ of $C$ is
    dense and irreducible. Write it as $V(I)$ in $U$. Irreducibility says
    that $sqrt(I)$ is prime: if $a b in sqrt(I)$, the containment
    $V(I) subset V(a) union V(b)$ forces one of the two containments.

  + *Construct the generic point.* Put $idl.p=sqrt(I)$. The closure of $idl.p$ in $U$ is $V(idl.p)$,
    so its closure in $X$ contains $C inter U$ and is contained in $C$;
    density gives equality with $C$.

  + *Prove uniqueness.* If two points have closure $C$, every open meeting $C$ contains both:
    an open containing a specialization contains its generizations. Choose
    an affine neighborhood of one. In this affine chart, equal closures
    mean equal prime ideals, so the two points coincide.

  + *Describe the opens and closed subsets of $t(Y)$.* Irreducibility gives
    $t(U inter V)=t(U) inter t(V)$, and $t$ preserves arbitrary unions of
    opens. The inverse image of $t(U)$ under the canonical map is $U$,
    so this correspondence is injective as well as surjective. It
    preserves ascending chains, proving the Noetherian assertion.
    Every closed subset of $t(Y)$ therefore has the form
    $F^(t)={C in t(Y) | C subset F}$ for a closed subset $F subset Y$.
    Such a subset is nonempty and irreducible exactly when $F$ is:
    use the same correspondence on unions of two closed subsets.
    In this case its unique generic point is the point $F$ of $t(Y)$,
    since the closure of a point $C$ is $C^(t)$.

  + *Identify the homeomorphism criterion.* The canonical map is continuous
    and induces the preceding isomorphism on opens. It is bijective
    exactly when every nonempty irreducible closed subset of $Y$ is the
    closure of a unique point. A bijection inducing this isomorphism on
    opens is a homeomorphism.
]

#definition(key: "sup-xp-2", title: "Specialization and components")[
  A point $y$ is a specialization of $x$ if $y in overline({x})$; $x$ is
  then a generization of $y$.
  A subset is _stable under generization_ if it contains every generization
  of each of its points; stability under specialization is defined similarly.
]

#proposition(key: "sup-xp-3", title: "Specialization and closed points")[
  + For points $x,y in ops.spec A$, $y in overline({x})$ if and only if
    $idl.p_(x) subset idl.p_(y)$.

  + Every sober space is $cal(T)_(0)$: distinct points have distinct
    closures. Specialization defines a partial order by $y<=x$ when
    $y in overline({x})$. Its minimal points are the closed points,
    and its maximal points are the generic points of irreducible components.
    The minimal nonempty closed subsets are single closed points.

  + Closed points of an affine scheme are the maximal
    ideals.

  + Its irreducible components correspond to minimal primes, with those
    primes as their generic points.

  + In every topological space, closed subsets are stable under
    specialization and open subsets are stable under generization.
]

#proof[

  + *Compute specialization on an affine chart.* A closed set $V(I)$ contains $idl.p$ precisely when $I subset idl.p$;
    intersecting these sets gives $overline({idl.p})=V(idl.p)$.
    This proves the specialization criterion.

  + *Order points by their closures.* In a sober space, equal closures
    give equal points by uniqueness of generic points. Thus specialization
    is antisymmetric. Its minimal points have singleton closure, and its
    maximal points have closure maximal among irreducible closed subsets.
    A minimal nonempty closed subset contains the closure of each of its
    points; minimality and the $cal(T)_(0)$ property make it a singleton.

  + *Identify closed points.* The closure is a singleton exactly for a maximal prime.

  + *Identify irreducible components.* By XP-1, every irreducible closed set is $V(idl.p)$, and maximality of
    that closed set is exactly minimality of $idl.p$ among prime ideals.

  + *Check stability.* A closed subset containing $x$ contains
    $overline({x})$. Taking complements proves the assertion for opens.
]

#lemma(key: "sup-xp-4", title: "Subspaces and generic points")[
  Let $Y$ be a sober space, and give its subsets their subspace topologies.
  + If $T subset Y$ is stable under generization, then $T$ is sober.
    Its irreducible components are exactly the nonempty intersections
    $C inter T$ for components $C$ of $Y$.
  + Every nonempty open of an irreducible sober space contains its generic
    point and is irreducible with the same generic point.
  + The dimension of a sober space is the supremum of the lengths of its
    strict specialization chains. No Noetherian or finiteness hypothesis
    on the set of components is required.
]

#proof[

  + *Restrict generic points to $T$.* For a nonempty irreducible closed
    subset $D subset T$, let $C=overline(D)$ in $Y$. This is irreducible,
    so has a generic point $eta$. Each point of $D$ is a specialization
    of $eta$; hence $eta in T$ by stability. The subspace closure formula
    gives $overline({eta}) inter T=C inter T=D$. Uniqueness is inherited
    from the $cal(T)_(0)$ property of $Y$.

  + *Restrict components.* If a component $C$ meets $T$, its generic point
    lies in $T$, so $C inter T$ is irreducible and dense in $C$.
    An irreducible closed subset of $T$ containing it has irreducible
    closure in $Y$ containing $C$, hence equal to $C$.
    Conversely, close a component of $T$ in $Y$ and include it in a
    component $C$ of $Y$; maximality in $T$ gives equality with $C inter T$.
    Existence of a containing component follows from the maximality
    principle: the closure of the union of a chain of irreducible subsets
    is irreducible.

  + *Restrict to a nonempty open.* Opens are stable under generization by
    XP-3. A nonempty open of an irreducible sober space contains its
    generic point, whose closure in that open is the whole open.

  + *Compare chains.* The correspondence
    $y mapsto overline({y})$ identifies points with nonempty irreducible
    closed subsets. Strict specialization corresponds to strict reverse
    inclusion of these closures, preserving chain lengths.
]

#proposition(key: "sup-xp-5", title: "Function fields")[
  + For an integral scheme $X$ with generic point $eta$, there are canonical
    identifications $K(X)=shf.o_(X,eta)=kappa(eta)$ and
    $ops.frac(A) simeq K(X)$ for every nonempty affine open $ops.spec A$.

  + Restriction to the generic stalk embeds $Gamma(U, shf.o_X)$ into $K(X)$
    for every nonempty open $U$.

  + These are the function-field identifications
    of II.3.6; a generic local ring on a nonintegral scheme need not be a field.
]

#proof[

  + *Identify the generic local ring.* On a nonempty affine open $ops.spec A$, integrality makes $A$ a domain
    and identifies $eta$ with $(0)$. Proposition 5.1's stalk formula for the
    structure sheaf gives $shf.o_(X,eta)=A_((0))=ops.frac(A)$; its maximal
    ideal is zero, so it equals its residue field. These identifications
    use the same germ map and consequently agree on smaller affine opens.
    They give the claimed canonical identifications with $K(X)$.

  + *Embed sections into the function field.* For $s in Gamma(U, shf.o_X)$ with zero generic germ, restrict to every
    affine open $V=ops.spec B subset U$. The map $B->ops.frac(B)$ is
    injective, so $s|_V=0$. These affines cover $U$, and SL-1 gives $s=0$.
]

#proposition(key: "sup-xp-6", title: "Dominance")[
  + For integral schemes $X,Y$, a morphism $f:X->Y$ is dominant if and only
    if $f(eta_X)=eta_Y$; its local map gives an inclusion $K(Y)->K(X)$.

  + For a ring map $phi:A->B$ inducing $f:ops.spec B->ops.spec A$,
    $f$ is dominant if and only if $ops.ker(phi) subset sqrt((0))$.
    Here $sqrt((0))$ is the nilradical of $A$.

  + If $A$ is reduced, then $f$ is dominant if and only if $phi$ is injective.

  + The quotient $A->A_(red)$ is dominant
    on spectra but is not injective when $A$ has a nonzero nilpotent.

  (Ex. II.3.7)
]

#proof[

  + *Test dominance at generic points.* Continuity gives $f(X) subset overline({f(eta_X)})$; since the
    right side is closed and contains a point of $f(X)$, the two closures
    coincide. XP-1 now proves the dominance criterion. The local map
    at the generic points is a map of fields and is therefore injective.

  + *Compute the closure of an affine image.* For a ring map $u:A->B$, the primes containing every contraction from
    $ops.spec B$ form $V(u^(-1)(sqrt((0))))=V(ops.ker(u))$:
    $u(a)$ is nilpotent if and only if some power of $a$ belongs to the kernel.
    This is the closure of the image, by the formula for closed sets in a
    spectrum. It is the whole spectrum if and only if the kernel lies in
    the intersection of all primes, the nilradical. Reducedness then makes
    this equivalent to a zero kernel. Applying this to the nilradical
    quotient gives the last example.
]

#remark(key: "sup-xp-7", title: "Noetherian and closed-point phenomena")[
  + A Noetherian scheme has a Noetherian underlying space and unique generic
    points for nonempty irreducible closed subsets; in the terminology of
    II.3.17 it is a Zariski space.

  + A scheme locally of finite type over a field
    has closed points dense in every closed subset.

  + For a scheme of finite
    type over a field, closed points have residue fields finite over that field.
    Over an algebraically closed field, these residue fields equal the base.

  + Neither Noetherianity nor density of closed points is needed for XP-1.
]

#proof[

  + *Prove Noetherianity of the underlying space.* A finite cover by spectra of Noetherian rings gives a finite cover by
    Noetherian spaces: ascending chains of opens stabilize on each member,
    hence simultaneously. Generic points are supplied by XP-1.

  + *Apply the Nullstellensatz.* For the closed-point assertion, use the algebraic form of the
    Nullstellensatz: a finitely generated algebra over a field is Jacobson,
    and its maximal-ideal residue fields are finite over that field.
    These are algebraic inputs left to the reader (Check!).

  + *Find a point with finite residue field.* Given a
    nonempty relatively open part of a closed subset, choose an affine
    finite-type chart and then a principal open inside that part. A maximal
    ideal of its quotient coordinate ring gives a point with finite residue
    field.

  + *Prove global closedness and density.* This point is closed in the entire scheme: in any finite-type
    affine neighborhood of a specialization its prime has quotient embedded
    in that finite field, hence that quotient is a finite-dimensional domain
    over the base field and is a field. The specialization must therefore
    equal the point. This proves the density assertion even when only local
    finite type is assumed.

  + *Identify residue fields over an algebraically closed base.* Over an algebraically closed field a finite
    field extension is the field itself.
]

#proposition(key: "sup-xp-8", title: "Clopen sets and idempotents")[
  + Global idempotents $e in Gamma(X, shf.o_X)$ correspond to clopen subsets
    by $e mapsto X_e$, with $e$ equal to $1$ on $X_e$ and $0$ on its
    complement.

  + On $ops.spec A$, a nontrivial decomposition is equivalent to
    $A simeq A_1 times A_2$ with both factors nonzero, or to orthogonal
    nonzero idempotents $e_1+e_2=1$. The factors are $A e_1,A e_2$ with
    identities $e_1,e_2$.

  (II.2.19)
]

#proof[

  + *Construct a clopen set from an idempotent.* In a local ring, $e(1-e)=0$ implies $e=0$ or $e=1$, since one of
    $e,1-e$ is a unit (Check!). For a global idempotent, the loci of these two germ
    equalities are open, disjoint, and exhaustive. They therefore form a
    clopen decomposition, and SL-1 identifies the restrictions with $1,0$.

  + *Glue an idempotent from a clopen decomposition.* Conversely, those two constant sections glue uniquely on a clopen
    decomposition, and their glued section is idempotent. These operations
    are inverse.

  + *Identify the affine product decomposition.* In an affine ring, the maps $a mapsto (a e,a(1-e))$ and
    $(b,c) mapsto b+c$ are inverse ring homomorphisms between $A$
    and $A e times A(1-e)$, with the indicated factor identities.
    Neither factor vanishes precisely for a nontrivial decomposition.
]

#proposition(key: "sup-xp-9", title: "Reduction")[
  + A scheme $X$ is reduced if and only if every local ring $shf.o_(X,x)$
    is reduced; equivalently, every ring $shf.o_X (U)$ has no nonzero nilpotents.
  + Let $shf.n$ be the sheaf of locally nilpotent sections of $shf.o_X$.
    Then $X_(red)=(X,shf.o_X\/shf.n)$ is a reduced scheme, and the quotient
    map defines a closed immersion $i:X_(red)->X$ that is a homeomorphism
    on underlying spaces. Its structure sheaf is the sheafification of
    $U mapsto shf.o_X (U)_(red)$.
  + Every morphism from a reduced scheme $T$ to $X$ factors uniquely
    through $i:X_(red)->X$.

  A common nilpotence exponent on an arbitrary open is not required.
  Reduced induced structures on other closed subsets are treated in CS-4.
  (Ex. II.2.3)
]

#proof[
  + *Compare reduced sections and reduced stalks.*

    + *Pass from stalks to sections.* Suppose first that every $shf.o_(X,x)$ is reduced.  If
      $s in shf.o_X (U)$ is nilpotent, then every germ $s_x$ is nilpotent and
      hence zero.  A section whose germs are all zero is zero, so
      $shf.o_X (U)$ is reduced.

    + *Pass from sections to stalks.* Conversely, assume every $shf.o_X (U)$ is reduced.  Let a germ
      $a in shf.o_(X,x)$ be nilpotent.  Represent it by
      $s in shf.o_X (U)$.  The equality $a^n=0$ means that after shrinking to
      some neighborhood $V$ of $x$, one has $(s|_V)^n=0$.  Reducedness of
      $shf.o_X (V)$ gives $s|_V=0$, hence $a=0$.  Thus every local ring is
      reduced.

  + *Construct the reduction.*

    + *Form the nilradical quotient sheaf.* Let $shf.n$ be the sheafification of the ideal presheaf
      $U mapsto sqrt((0)) subset shf.o_X(U)$.  Its inclusion into
      $shf.o_X$ is injective by SC-1.  Thus $shf.n (U)$ consists
      of locally nilpotent sections; a uniform nilpotence exponent on an
      arbitrary open $U$ is not required.  Define
      $
        X_(red)=(X,shf.o_X\/shf.n).
      $
      Equivalently, this quotient sheaf is the sheafification of
      $U mapsto shf.o_X (U)_(red)$.

    + *Identify its affine charts.* On an affine open
      $V=ops.spec A$, its restriction is the structure sheaf of
      $ops.spec(A\/sqrt((0)))$.  To see this, on every $D(a) subset V$
      a locally nilpotent section is nilpotent because $D(a)$ is
      quasi-compact: choose a finite cover with nilpotence exponents and take
      their maximum.  The nilradical of $A_a$ is $sqrt((0))A_a$, and
      $A_a\/sqrt((0))A_a simeq (A\/sqrt((0)))_(bar(a))$. These nilradical
      and quotient-localization identities are algebraic checks (Check!). Localization
      commutes with these quotient maps, so these identifications respect all
      restrictions on the distinguished basis.  They identify the quotient
      sheaf with the indicated affine structure sheaf.  Hence these affine reductions
      glue and make $X_(red)$ a scheme.  The quotient maps define a closed immersion
      $i:X_(red)->X$.

    + *Compare the underlying spaces.* Every prime ideal of $A$ contains $sqrt((0))$, so contraction gives a
      homeomorphism
      $ops.spec(A\/sqrt((0))) simeq ops.spec A$.  These local homeomorphisms
      agree, and therefore $i$ is a homeomorphism on underlying spaces.

    + *Verify reducedness.* Finally, $A\/sqrt((0))$ is reduced on every affine chart, so part (a)
      shows that $X_(red)$ is reduced.

  + *Prove the reduced-source universal property.*

    #align(center)[#diagram(
      cell-size: 20mm,
      $X edge("r", tilde(f), ->, stroke: #(dash: "dashed")) edge("dr", f, ->) & Y_(red) edge("d", i, ->) \ & Y$,
    )]

    + *Factor the structure-sheaf map.* Let $f:X->Y$ with $X$ reduced.  Nilpotent local sections of $shf.o_Y$
      pull back to nilpotent sections of $shf.o_X$, hence to zero.  Thus
      $f^sharp$ kills the nilradical ideal sheaf of $Y$ and factors through
      $shf.o_Y\/shf.n_Y$.  This gives a morphism
      $tilde(f):X->Y_(red)$ with $i compose tilde(f)=f$.

    + *Check locality on stalks.* At $x in X$,
      the induced map is the factor of the local homomorphism
      $shf.o_(Y,f(x))->shf.o_(X,x)$ through its nilradical quotient.  It is
      local because the maximal ideal of that quotient is the image of the
      original maximal ideal.  Thus this is a morphism of locally ringed
      spaces.

    + *Prove uniqueness.* The underlying map is forced by the homeomorphism $i$, and
      the sheaf map is forced by the epimorphism to the quotient, proving
      uniqueness.

]

#lemma(key: "sup-xp-10", title: "Quasi-compactness and Noetherian induction")[
  + Every affine scheme is quasi-compact.

  + A topological space is Noetherian
    if and only if every open is quasi-compact.

  + A locally Noetherian scheme is
    Noetherian if and only if it is quasi-compact.

  + On a Noetherian space,
    Noetherian induction proves a property for all closed subsets if, for each
    closed subset, its validity on every proper closed subset implies its
    validity there. This includes the empty subset as the initial case
    (II.2.13 and II.3.16).
]

#proof[

  + *Prove affine quasi-compactness.* Refine an open cover of $ops.spec A$ by distinguished opens $D(a_i)$.
    Their covering condition says that the ideal generated by all $a_i$ is
    the unit ideal (Check! a proper ideal lies in a maximal ideal).
    An expression for $1$ uses finitely many generators,
    giving a finite subcover.

  + *Characterize Noetherian spaces.* In a Noetherian space, the finite unions from
    any open cover of an open subset have a maximal member, which must be
    that subset. Conversely, if every open is quasi-compact, the union of
    an ascending chain of opens is covered by finitely many members and
    the chain stabilizes.

  + *Characterize Noetherian schemes.* A quasi-compact locally Noetherian scheme has a
    finite cover by Noetherian affine charts; the converse follows from
    that finite cover and affine quasi-compactness.

  + *Apply Noetherian induction.* If induction failed, the descending chain condition on closed subsets
    would give a minimal closed counterexample. All its proper closed
    subsets satisfy the property, so the induction hypothesis rules out
    this counterexample, including the possibility that it is empty.
]

#definition(key: "sup-xp-11", title: "Quasi-separatedness")[
  Let $Delta_X:X->fiber(X, X, base: ops.spec ZZ)$ be the diagonal.
  A scheme $X$ is quasi-separated if $Delta_X$ is quasi-compact.
  The following conditions are equivalent:

  #set enum(spacing: 0.8em)

  + $X$ is quasi-separated.
  + $U inter V$ is quasi-compact for every pair of affine open subsets
    $U,V subset X$.
  + The intersection of two quasi-compact open subsets of $X$ is
    quasi-compact.

  Every separated scheme is quasi-separated. The converse fails:
  the doubled affine line has affine overlap and is not separated.
]

#proof[

  + *Compute the inverse images of the diagonal.* Cover $fiber(X, X, base: ops.spec ZZ)$ by products $U times V$ of affine
    opens. These products are affine by MG-1, and the inverse image under
    the diagonal is $U inter V$. The target criterion for quasi-compactness
    in LP gives the equivalence.

  + *Pass to quasi-compact opens.* Each quasi-compact open has a finite
    affine open cover. Distributing an intersection over these covers
    expresses it as a finite union of affine intersections. The converse
    follows because affine opens are quasi-compact by XP-10.

  + *Deduce quasi-separatedness from separatedness.* A closed immersion is quasi-compact, so
    separatedness implies the condition.

  + *Check the doubled-line example.* For the doubled line, its two
    standard charts and their overlap $ops.spec k[t,t^(-1)]$ are
    quasi-compact. On the product of the two charts, the diagonal has the
    punctured diagonal as image; its closure contains the pair of origins.
    It is therefore not a closed immersion.
]

=== Constructible sets and quasi-compact subspaces <sup-xp-constructible>

A space is _spectral_ if it is sober and quasi-compact, and its
quasi-compact open subsets form a basis closed under finite intersections.
Every quasi-compact, quasi-separated scheme is spectral by XP-1, XP-10,
and XP-11. Every Zariski space is spectral, since every open of a
Noetherian space is quasi-compact.

#proposition(key: "sup-xp-12", title: "Constructible sets")[
  Let $Y$ be a spectral space. A subset is _constructible_ if it belongs
  to the Boolean algebra generated by quasi-compact opens. The
  _constructible topology_ is generated by these opens and their complements.
  + Constructible subsets are exactly the finite disjoint unions of sets
    $U minus V$, where $U,V subset Y$ are quasi-compact and open.
    In a Noetherian space these are precisely the finite disjoint unions
    of locally closed subsets, as in Ex. II.3.18.
  + The constructible topology is compact and Hausdorff. Its clopen
    subsets are exactly the constructible subsets. In particular, a
    family of constructible subsets with the finite-intersection
    property has nonempty intersection.
  + A subset closed in the constructible topology is closed in $Y$ if
    and only if it is stable under specialization. Consequently, a
    constructible subset is closed if and only if it is stable under
    specialization, and is open if and only if it is stable under
    generization. A constructible open is quasi-compact.
  + If $Y$ is irreducible with generic point $eta$, a constructible
    subset $E$ is dense if and only if $eta in E$. In this case $E$
    contains a nonempty open subset.
  + A continuous map between spectral spaces preserves constructible
    subsets under inverse image if inverse images of quasi-compact
    opens are quasi-compact. For maps between Noetherian spaces this
    extra condition is automatic.
]

#proof[
  + *Put Boolean expressions in disjoint form.* Partition $Y$ according
    to membership in the finitely many quasi-compact opens appearing
    in an expression. Each part is $U minus V$: intersect the positive
    conditions and take the union of the negative ones. Empty intersections
    mean $Y$, which is quasi-compact. These parts are disjoint and locally
    closed. If $Y$ is Noetherian, every locally closed set has this form.

  + *Prove compactness of the constructible topology.* Extend a family
    of constructible sets with the finite-intersection property to an
    ultrafilter $cal(F)$ on their Boolean algebra. Put
    $
      C=Y minus union_(U in.not cal(F)) U,
    $
    where $U$ runs through quasi-compact opens. Quasi-compactness of $Y$
    makes $C$ nonempty: otherwise a finite union of opens outside the
    ultrafilter would equal $Y$. For a quasi-compact open $U$,
    $
      C inter U != emptyset quad arrow.l.r.double quad U in cal(F).
    $
    Indeed, one direction follows from the definition of $C$; for the
    other, covering $U$ by the excluded opens would give a finite such
    cover, contradicting $U in cal(F)$. The basis and the filter property
    now make $C$ irreducible: two basis opens meeting $C$ have intersection
    in $cal(F)$, hence meet $C$ simultaneously. Sobriety gives a generic
    point $eta$ of $C$. It belongs to a quasi-compact open $U$ exactly
    when $U in cal(F)$, and therefore has the same membership rule for
    every Boolean expression. It lies in the original family.
    This finite-intersection criterion proves compactness. Distinct
    points are separated by a quasi-compact open and its complement,
    so the topology is Hausdorff. Its basic opens are constructible
    and clopen; compactness makes every clopen a finite union of these.

  + *Recover closed subsets from specialization.* Let $E$ be closed in
    the constructible topology and stable under specialization. For
    $x in.not E$ and $y in E$, one has $x in.not overline({y})$. Choose
    a quasi-compact open $U_(y)$ containing $x$ and avoiding $y$.
    The complements of the $U_(y)$ cover $E$ in the constructible topology.
    Compactness gives finitely many, whose corresponding intersection
    is an open neighborhood of $x$ disjoint from $E$. Thus $E$ is closed
    in $Y$. Conversely, an ordinary closed subset is an intersection of
    complements of quasi-compact opens, and is stable under specialization
    by XP-3. Apply this criterion to a constructible set and its complement.
    A constructible set is compact in the finer topology and hence
    quasi-compact in the original topology.

  + *Test density at the generic point.* If a constructible set is dense,
    its finite locally closed decomposition has a part with closure $Y$,
    because $Y$ is irreducible. That part is a nonempty open of $Y$,
    so contains $eta$ by XP-4. Conversely, a subset containing $eta$
    is dense. The same decomposition then supplies a nonempty open.

  + *Take inverse images.* Inverse image commutes with Boolean operations.
    The condition on quasi-compact opens therefore suffices. XP-10 makes
    it automatic when the source is Noetherian.
]

#proposition(key: "sup-xp-13", title: "Quasi-compact subspaces")[
  Let $Y$ be a spectral space, and give all subsets their subspace topologies.
  + A subset $T subset Y$ is quasi-compact and stable under generization
    if and only if it is an intersection of quasi-compact opens of $Y$.
    Such a subspace is spectral. Its quasi-compact opens are precisely
    the sets $T inter V$ with $V subset Y$ quasi-compact and open.
  + For a quasi-compact subset $E subset Y$, put
    $
      W={y in Y | exists e in E, e in overline({y})}.
    $
    Then $W$ is quasi-compact and stable under generization, and equals
    the intersection of the quasi-compact open neighborhoods of $E$.
  + If $T$ is as in (a), $U subset T$ is quasi-compact and open,
    $Z=T minus U$, and $W$ is the set of generizations of $Z$ in $T$,
    then $W$ and $W minus Z=W inter U$ are quasi-compact and stable
    under generization in $Y$.
  + Let $T=inter_(i in I) V_(i)$, where the $V_(i)$ are a nonempty
    family of quasi-compact opens such that for any $i,j$ there is
    $k$ with $V_(k) subset V_(i) inter V_(j)$. For constructible subsets
    $A,B subset Y$, if $T inter A subset B$, then
    $V_(i) inter A subset B$ for some $i$. This applies in particular
    to finite containment and covering relations between quasi-compact opens.
]

#proof[
  + *Express a stable subset as an intersection.* Suppose $T$ is
    quasi-compact and stable under generization. For $x in.not T$,
    $overline({x})$ is disjoint from $T$. Refine its open complement by
    the quasi-compact open basis and take a finite subcover of $T$.
    Its union is a quasi-compact open containing $T$ and avoiding $x$.
    Thus $T$ is the intersection of these neighborhoods.
    Conversely, such an intersection is closed in the compact
    constructible topology by XP-12, hence quasi-compact in the original
    topology, and is stable under generization by XP-3.

  + *Identify the topology on $T$.* For a quasi-compact open $V subset Y$,
    $T inter V$ is closed in the constructible topology, hence
    quasi-compact. These sets form a basis. Every quasi-compact open of
    $T$ is a finite union of them, hence is $T inter V$ for their union
    $V$. Finite intersections retain this form, and XP-4 gives sobriety.
    Thus $T$ is spectral. This also shows that its constructible topology
    is the subspace topology induced by the constructible topology of $Y$.

  + *Take generizations of $E$.* Every open containing $E$ contains $W$.
    An open cover of $W$ therefore has a finite subcover as soon as
    it covers $E$, so $W$ is quasi-compact. It is stable under
    generization by transitivity. The separating-neighborhood argument
    in (a) gives the claimed intersection formula.

  + *Remove the closed complement of an open.* In the spectral space
    $T$, the subset $Z$ is closed and quasi-compact. Part (b) applies
    to its generizations $W$. Both $W$ and $U$ are closed in the
    constructible topology of $T$, so $W inter U$ is quasi-compact.
    It is stable under generization in $T$, hence in $Y$ because $T$
    is stable there. The same applies to $W$.

  + *Descend finite relations.* The closed subsets
    $V_(i) inter (A minus B)$ of the compact constructible space have
    empty intersection. Finitely many already have empty intersection
    by XP-12. The condition on the family supplies a single $V_(i)$
    contained in all those finitely many members, proving the assertion.
]

#corollary(key: "sup-xp-14", title: "Zero-dimensional spaces")[
  Let $Y$ be a spectral space of dimension zero. Every quasi-compact
  open is clopen, and every open covering has a finite refinement by
  pairwise disjoint clopen subsets.
]

#proof[
  By XP-4, dimension zero excludes strict specializations. Hence every
  subset is stable under specialization, and XP-12 makes every
  quasi-compact open closed. Refine a given cover by the quasi-compact
  open basis and take a finite subcover $U_(1),dots.c,U_(r)$.
  The sets $U_(i) minus union_(j<i) U_(j)$ are clopen, pairwise disjoint,
  and cover $Y$; each lies in a member of the original cover.
]

=== Local algebra and intrinsic properties

#proposition(key: "sup-xp-15", title: "Normality")[
  + A scheme $X$ is normal if and only if $shf.o_(X,x)$ is an integrally
    closed domain for every $x in X$.

  + For any open cover $X=union_i U_i$, $X$ is normal if and only if
    $U_i$ is normal for every $i$.

  + For a ring $A$, $ops.spec A$ is normal if and only if $A_idl.p$ is
    an integrally closed domain for every prime ideal $idl.p subset A$.
    If $A$ is a domain, this is also equivalent to $A$ being integrally
    closed in $ops.frac(A)$.

  + Normality does not imply connectedness or irreducibility.

  + If $X$ is nonempty, connected, normal, and Noetherian, then $X$ is integral.
]

#proof[

  + *Check normality on an open cover.* Restricting a scheme to an open preserves its local rings, which proves
    both open restriction and the cover criterion.

  + *Apply the affine localization criterion.* On $ops.spec A$, the
    stalks are $A_idl.p$. For a domain, the algebraic criterion is that
    integral closedness is preserved by localization and that
    $A=inter.big_idl.p A_idl.p$ inside $ops.frac(A)$. Indeed, an element
    integral over $A$ lies in every integrally closed $A_idl.p$, hence in
    $A$. For the intersection formula, if a fraction $z$ is not in $A$,
    the proper ideal ${a:a z in A}$ is contained in a maximal ideal,
    and $z$ is not in that localization.

  + *Prove the connected Noetherian conclusion.* In the Noetherian case, there are finitely many irreducible components.
    No two can meet: in an affine neighborhood of an intersection point,
    their distinct minimal primes remain distinct minimal primes in the
    local ring at that point, contradicting its being a domain. Thus the
    components are disjoint and, being finitely many closed subsets, open.
    Connectedness and nonemptiness force a single component. Normal local
    rings are reduced, so the stalk criterion makes $X$ reduced as well;
    reducedness and irreducibility give integrality.
]

#corollary(key: "sup-xp-16", title: "Finite type and Noetherianity")[
  A finite-type scheme over a Noetherian scheme is Noetherian.
  Local finite type supplies Noetherian affine charts by the Hilbert basis
  theorem; quasi-compactness supplies a finite affine cover. The distinction
  between these two hypotheses is part of the finite-type definition and
  #book-link(<sup-lp>)[its locality criteria].
]

#proof[

  + *Obtain Noetherian affine charts.* Choose a finite Noetherian affine cover $V_i=ops.spec A_i$ of the
    target. LP's local finite-type criterion gives an affine cover of
    $f^(-1)(V_i)$ with rings finitely generated over $A_i$; each is
    Noetherian by the Hilbert basis theorem and passage to quotients.

  + *Choose a finite cover.* Quasi-compactness of $f$ makes each inverse image quasi-compact, so
    finitely many such charts suffice for each $i$. They give a finite
    Noetherian affine cover of the source, as required by XP-10.
]

=== Locality of intrinsic properties <sup-xp-locality>

#table(
  columns: (1fr, 1fr, 1fr, 1.5fr),
  inset: 5pt,
  fill: (_, y) => if calc.odd(y) { rgb("EAF2F5") },
  stroke: none,
  table.header([Property], [Open restriction], [Open-cover test], [Stalk / affine test]),
  [Reduced], [$checkmark$], [$checkmark$], [Reduced stalks / reduced rings],
  [Normal], [$checkmark$], [$checkmark$], [Normal local rings / XP-15],
  [Locally Noetherian], [$checkmark$], [$checkmark$], [Noetherian affine rings; Noetherian stalks alone do not suffice],
  [Quasi-compact], [Not in general], [Finite cover by quasi-compact opens], [No stalk test],
  [Irreducible],
  [Nonempty opens],
  [Irreducible nonempty cover members with pairwise nonempty intersections],
  [No stalk test],

  [Connected], [Not in general], [Connected nonempty cover members with connected intersection graph], [No stalk test],
  [Integral],
  [Nonempty opens],
  [Reduced plus the irreducibility condition above],
  [Domains on every nonempty affine open],
)

#metadata(none) <sup-xp-examples>
#example(key: "sup-xp-17", title: "Calculations and counterexamples")[
  In $ops.spec(k[x,y]\/(x y))$, the generic primes are $(x)$ and $(y)$,
  with closures the two axes. Only the component $V(y)$ meets $D(x)$;
  only $V(x)$ meets $D(y)$. Deleting the origin gives a disconnected open
  in a connected scheme.
]

#proof[
  A prime containing $x y$ contains $x$ or $y$, giving precisely the two minimal primes. On $D(x)$ the relation forces $y=0$, and on $D(y)$ it forces $x=0$. The two axes are connected and meet at the origin, so their union is connected; deleting that point leaves two disjoint nonempty opens.
]

#example(key: "sup-xp-18", title: "Calculations and counterexamples")[
  $ops.spec(k[epsilon]\/(epsilon^2))$ has one point, both closed and
  generic, but its local ring is not a field.
]

#proof[
  Every prime contains $epsilon$, and the quotient by $(epsilon)$ is $k$. Thus there is just one prime. The element $epsilon$ is nonzero with square zero in the local ring, so this ring is not a field.
]

#example(key: "sup-xp-19", title: "Calculations and counterexamples")[
  The closed points of $sch.a^1_k$ for algebraically closed $k$ are dense
  and omit its generic point. In contrast, a nonfield DVR has one closed
  point and one generic point, and its closed points are not dense.
]

#proof[
  A nonzero polynomial in one variable has only finitely many roots, whereas an algebraically closed field is infinite. Thus no proper closed subset contains all $k$-points. In a nonfield DVR the only nonzero prime is its maximal ideal, whose singleton is closed and proper.
]

#example(key: "sup-xp-20", title: "Calculations and counterexamples")[
  For $k[s]->k[t]$, $s mapsto t^2$, the generic map is $k(s)->k(t)$
  with the same substitution. See #supplement-link(<sup-mg-3>)[MG-3] for the fibers.
]

#proof[
  The substitution is injective on polynomials, since distinct powers of $s$ become distinct even powers of $t$. It extends uniquely to fractions, giving the claimed generic field inclusion by XP-5.
]

#metadata(none) <sup-xp-disjoint-points>
#example(key: "sup-xp-21", title: "Calculations and counterexamples")[
  An infinite disjoint union of copies of $ops.spec k$ is locally
  Noetherian but not quasi-compact. Two copies already have an integral
  affine cover without being connected or irreducible.
]

#proof[
  The components themselves form an open cover with no finite subcover. Each component is a Noetherian affine open. Two components form a disjoint clopen decomposition, which prevents connectedness and irreducibility.
]

#example(key: "sup-xp-22", title: "Calculations and counterexamples")[
  The square-zero ring $k plus.o V$, with $V$ infinite-dimensional and
  $V^2=0$, is not Noetherian, though its spectrum has one point.
]

#proof[
  Every prime contains the square-zero ideal $V$ and the quotient is $k$, giving one prime. A generating set for $V$ as an ideal must span it over $k$, since $V$ acts on itself by zero. Thus $V$ is not finitely generated.
]

#example(key: "sup-xp-23", title: "Calculations and counterexamples")[
  For $A=product_(n>=0) bb(F)_2$, every local ring is a field but $A$ is
  not Noetherian. Noetherian stalks do not imply local Noetherianity.
]

#proof[

  + *Compute the local rings.* Every element of $A$ is idempotent. In any local ring of $A$, every element is therefore $0$ or $1$, so that ring is a field.

  + *Exhibit failure of Noetherianity.* The ideals of sequences supported in the first $n$ coordinates form a strictly ascending chain.

  + *Exclude local Noetherianity.* If the scheme were locally Noetherian, its affine quasi-compactness would give a finite Noetherian affine cover and force $A$ Noetherian, a contradiction.
]

#example(key: "sup-xp-24", title: "Calculations and counterexamples")[
  $ops.spec(k times k)$ is normal and is not integral.
]

#proof[
  Its two local rings are $k$, hence are integrally closed domains, whereas the spectrum has two disjoint nonempty components and the ring has nonzero zero divisors.
]
