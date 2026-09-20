#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== MG — Morphisms, diagonals and graphs <sup-mg>

Use the fiber product of #book-link(<text-ii-3>)[II.3, D10 and Theorem 3.3],
the diagonal and separatedness criteria of
#book-link(<text-ii-4>)[II.4, Proposition 4.1 and Corollary 4.2], and
#book-link(<sup-lp>)[the locality calculus].

#metadata(none) <sup-mg-1>
#proposition(number: "MG-1", title: "Affine fiber products")[
  For $A$-algebras $B,C$, the fiber product of their spectra is canonically
  $ops.spec tensor(B, C, over: A)$; the projections correspond to
  $b mapsto tensor(b, 1)$ and $c mapsto tensor(1, c)$.
]

#proof[

  + *Apply the affine-target correspondence.* Put $D=tensor(B, C, over: A)$. For any scheme $T$, maps from $T$ to
    $ops.spec D$ correspond to ring maps $D->Gamma(T, shf.o_T)$ by II.2's
    affine-target adjunction.

  + *Apply the tensor-product universal property.* The tensor-product universal property identifies
    these with pairs of maps from $B,C$ agreeing on $A$, hence with pairs
    $T->ops.spec B$, $T->ops.spec C$ agreeing over $ops.spec A$.
    Check the tensor-product universal property for commutative algebras (Check!).

  + *Identify the projections and conclude.* This correspondence is natural in $T$ and sends the two specified
    algebra inclusions to the projections. It proves the fiber-product
    universal property, including uniqueness.
]

#metadata(none) <sup-mg-2>
#example(number: "MG-2", title: "Points of a fiber product")[
  + For example, $tensor(k(s), k(t), over: k)$ is the localization of $k[s,t]$
    by all nonzero polynomials in $s$ and all nonzero polynomials in $t$.

  + Its primes are exactly the primes of $k[s,t]$ disjoint from this
    multiplicative set. Both $(0)$ and $(s-t)$ occur.

  + Thus points of a fiber
    product are not the ordinary product of the point sets, even over $k$.
]

#proof[

  + *Compute the localization and its primes.* First localize $k[s,t]$ by the nonzero elements of $k[s]$, and then by
    those of $k[t]$. Successive localization and tensor-product universal
    properties give the displayed tensor ring. The localization prime
    correspondence identifies its primes with the primes avoiding both sets.

  + *Exhibit two distinct primes.* The zero prime avoids them since $k[s,t]$ is a domain. The prime $(s-t)$
    also avoids them, since substitution $s=t$ is injective on each of the
    two one-variable polynomial rings.

  + *Compare the projected points.* Both primes project to the unique
    points of the two field spectra, although they are distinct.
]

#metadata(none) <sup-mg-3>
#proposition(number: "MG-3", title: "Fibers")[
  + For $f:X->Y$ and $y in Y$, use the fiber definition in
    #book-link(<text-ii-3>)[II.3, D11]. On affine charts $A->B$, its ring is
    $tensor(B, kappa(y), over: A)$.

  + Projection identifies its underlying space
    with $f^(-1)({y})$ with the subspace topology; the scheme structure also
    records residue fields and nilpotents.
]

#proof[

  + *Compute the affine fiber charts.* Choose $V=ops.spec A$ containing $y$, with prime $idl.p$, and cover
    $f^(-1)(V)$ by affines $W=ops.spec B$. Base change of these open
    immersions covers the fiber. MG-1 identifies each chart with
    $ops.spec(tensor(B, kappa(idl.p), over: A))$. Its ring is
    $S^(-1)B\/idl.p S^(-1)B$, where $S$ is the image of $A minus idl.p$.

  + *Identify their underlying subspaces.* Quotient and localization prime correspondences identify its primes with
    those $idl.q$ of $B$ whose contractions equal $idl.p$. Basic opens
    correspond under projection to the intersections of $D(b)$ with this
    subset, so the bijection is a homeomorphism onto the subspace.

  + *Glue the chart identifications.* All maps
    used are the base-changed projection; they agree on overlaps and prove
    the global assertion.
]

#metadata(none) <sup-mg-4>
#example(number: "MG-4", title: "Fibers of a quadratic map")[
  For algebraically closed $k$ of characteristic different from $2$ and
  $s mapsto t^2$,

  + The fiber at $s=a!=0$ is two reduced $k$-points.

  + The fiber at $0$ is $ops.spec(k[t]\/(t^2))$.

  + The generic fiber is
    $ops.spec(k(s)[t]\/(t^2-s))=ops.spec k(t)$, with its specified $k(s)$-map.
]

#proof[

  + *Compute the closed-fiber ring.* Tensoring over $k[s]$ with $k[s]\/(s-a)$ gives $k[t]\/(t^2-a)$.

  + *Treat the nonzero closed fibers.* For $a!=0$, choose a square root $b$; the two factors $t-b,t+b$ are
    relatively prime because $2b!=0$, and the Chinese remainder theorem
    gives $k times k$.

  + *Treat the fiber over zero.* At zero, the surviving class of $t$ is nonzero and
    has square zero.

  + *Treat the generic fiber.* At the generic point, invert every nonzero polynomial
    in $s=t^2$. Every nonzero $q(t)$ becomes invertible: the nonzero product
    $q(t)q(-t)$ lies in $k[t^2]$. The resulting ring is therefore $k(t)$.
]

#metadata(none) <sup-mg-5>
#corollary(number: "MG-5", title: "Graphs")[
  + For an $S$-morphism $h:X->Y$, its graph
    $Gamma_h:X->fiber(X, Y, base: S)$ is the base change of the diagonal of
    $Y/S$ along the map $(h compose p_1,p_2)$.

  + Consequently, it is a closed immersion if $Y/S$ is separated.
    This factorization uses the given morphism, not just its point map.
]

#proof[

  + *Describe the pullback of the diagonal.* Write $P=fiber(X, Y, base: S)$ and map it to $fiber(Y, Y, base: S)$ by
    $(h p_1,p_2)$. A map $T->P$ together with a lift to the diagonal is
    exactly a pair $(a:T->X,b:T->Y)$ with $h a=b$; the lift is forced.

  + *Identify the graph.* Such data are naturally the single map $a$. Thus the pullback of the
    diagonal is $X$, and its map to $P$ is $(ops.id_X,h)$, the graph.

  + *Apply separatedness.* Separatedness makes the diagonal a closed immersion, and LP's
    base-change stability of closed immersions proves the conclusion.
]

#metadata(none) <sup-mg-6>
#lemma(number: "MG-6", title: "Uniqueness on a dense open")[
  If $X$ is reduced and $Y/S$ is separated, two $S$-morphisms $X->Y$
  which agree as morphisms on a dense open of $X$ are equal.
]

#proof[

  + *Construct the closed equalizer.* Let the morphisms be $a,b$ and pull the closed diagonal of $Y/S$ back
    along $(a,b):X->fiber(Y, Y, base: S)$. This gives a closed subscheme
    $E->X$, the equalizer. The given dense open factors through $E$, so the
    underlying closed subset of $E$ is all of $X$.

  + *Use reducedness to kill its ideal.* On an affine chart
    $ops.spec A$ of $X$, write $E$ as $ops.spec(A/I)$. The equality
    $V(I)=ops.spec A$ gives $I subset.eq sqrt((0))=0$, because $X$ is
    reduced.

  + *Conclude globally.* Thus $E->X$ is an isomorphism on an affine cover and hence
    globally by XL.

  Its defining equality gives $a=b$.
]

#metadata(none) <sup-mg-7>
#example(number: "MG-7", title: "Hypotheses for uniqueness on a dense open")[
  + The doubled origin shows that separatedness of the target matters.

  + For failure without reducedness, take
    $X=ops.spec(k[t,epsilon]\/(epsilon^2,t epsilon))$ and the two maps to
    $sch.a^1_k$ given by the sections $0$ and $epsilon$. They agree on the
    dense open $D(t)$ and differ globally.

  + On the one-point dual-number scheme,
    these same two sections give distinct maps with identical underlying point
    maps, so setwise equality is weaker still.
]

#proof[

  + *Remove separatedness of the target.* The two inclusions of an affine line into the doubled line agree on
    the punctured line and send the origin to different points.

  + *Remove reducedness of the source.* For the
    second example, every prime contains $epsilon$, so the underlying space
    is an affine line and $D(t)$ is dense. Inverting $t$ kills $epsilon$.
    The class of $epsilon$ is nevertheless nonzero before localization, as
    is seen by setting $t=0$ and mapping to $k[epsilon]\/(epsilon^2)$.
    The affine-target correspondence therefore gives distinct morphisms.

  + *Compare point maps with scheme morphisms.* On the dual-number spectrum, there is only one point, and both maps send
    it to the origin; they still differ on the coordinate function.
]

#metadata(none) <sup-mg-8>
#corollary(number: "MG-8", title: "Affine intersections")[
  + If $X$ is separated over an affine scheme $S$, the intersection of any
    two affine opens of $X$ is affine.

  + Without separatedness, this may fail:
    glue two affine planes over $k$ along the punctured plane. Their overlap
    is $sch.a^2_k$ minus the origin, which is not affine.

  + The overlap in the doubled affine line is $sch.a^1_k$ minus the origin,
    which is affine, so that example does not demonstrate this failure.
]

#proof[

  + *Use the closed diagonal.* For affine opens $U,V subset.eq X$, the pullback of the diagonal
    $X->fiber(X, X, base: S)$ to $fiber(U, V, base: S)$ is $U inter V$.
    The product is affine by MG-1, since $S$ is affine. Its closed
    subscheme $U inter V$ is affine by the affine closed-immersion criterion.

  + *Exhibit a nonaffine overlap.* In the punctured plane, cover by $D(x),D(y)$. The sheaf equalizer
    computes global functions as
    $k[x,y]_x inter k[x,y]_y=k[x,y]$ inside $k(x,y)$: unique factorization
    removes both possible denominators. If this open were affine, its
    inclusion into the plane would, on global rings, be the identity and
    thus an isomorphism, although it omits the origin. Gluing two planes
    along this open produces the asserted example.

  + *Compare the doubled line.* For the doubled line,
    the overlap is the distinguished affine open $D(t)$.
]

#metadata(none) <sup-mg-9>
#proposition(number: "MG-9", title: "Calculus of morphism properties")[
  Let $P$ contain all closed immersions and be stable under composition
  and base change.

  + Products over a common base of two $P$-morphisms have
    $P$.

  + If $X ->^f Y ->^g Z$, $g compose f$ has $P$, and $g$ is
    separated, then $f$ has $P$ by its graph factorization.

  + If $f$ has $P$,
    then $f_(red):X_(red)->Y_(red)$ has $P$, using the closed immersion of
    $X_(red)$ into $fiber(X, Y_(red), base: Y)$.

  + For separated and proper morphisms, compare
    #book-link(<text-ii-4>)[II.4, Corollaries 4.6 and 4.8].

  + For finite type (II.3.13), closed immersions and quasi-compact open
    immersions are finite type; compositions, base changes, and products
    preserve finite type.

  + The additional cancellation statement is:
    if $f$ is quasi-compact and $g compose f$ is finite type, then $f$ is
    finite type, without assuming $g$ separated. Use the affine
    finite-generation criterion of #book-link(<sup-lp>)[the locality calculus].
    The Noetherian conclusion is #book-link(<sup-xp-13>)[XP-13].
]

#proof[

  + *Form products by base change.* The product map factors as two successive base changes of the given
    maps, so composition proves the first assertion.

  + *Apply the graph factorization.* The graph factorization through
    $fiber(X, Y, base: Z)$, followed by projection to $Y$, has two arrows: the first arrow
    is a closed immersion when $Y->Z$ is separated, and the second is the
    base change of $X->Z$. Thus $f$ has $P$.

  + *Pass to reductions.* For reduction, put $W=fiber(X, Y_(red), base: Y)$. The map
    $X_(red)->W$ is a closed immersion: over a compatible pair of affine
    charts $A->B$ it is the surjection
    $B\/sqrt((0)_A)B -> B\/sqrt((0)_B)$, since nilpotents map to
    nilpotents. These chartwise maps are canonical quotient maps and glue.
    Compose this closed immersion with the base change $W->Y_(red)$ of
    $f$ to obtain $f_(red)$.

  + *Check finite-type stability.* For finite type, use LP's affine ring criteria for composition and
    base change. A quotient is generated by $1$ as a module, and a
    principal localization $A_a$ is generated as an algebra by $1/a$;
    a quasi-compact open immersion is covered by finitely many such
    principal opens over each affine target.

  + *Prove finite-type cancellation.* For the additional cancellation,
    choose $V=ops.spec B subset.eq Y$ mapping into $W=ops.spec A subset.eq Z$,
    and an affine $U=ops.spec C subset.eq f^(-1)(V)$. The local finite-type
    criterion for $g f$ makes $C$ a finite-type $A$-algebra. The same
    generators generate it over $B$, since the $A$-map factors through $B$.
    Such $U,V$ cover the source and target in question, so $f$ is locally
    finite type. Its assumed quasi-compactness completes the definition.
]

#metadata(none) <sup-mg-10>
#proposition(number: "MG-10", title: "Field-valued points")[
  + For a field $K$, morphisms $ops.spec K->X$ correspond to pairs
    $(x,kappa(x)->K)$, where the field map is an inclusion.

  + A morphism $f:X->Y$ induces $kappa(f(x))->kappa(x)$, so a $k$-morphism
    preserves $k$-rational points.

  + The closed-point hypotheses and classical
    variety interpretation are in #book-link(<sup-xp-7>)[XP-7] and
    #book-link(<sup-vs>)[VS].
]

#proof[

  + *Recover the residue-field inclusion.* A map from the one-point scheme has image $x$ and gives a local map
    $shf.o_(X,x)->K$. Its kernel is the maximal ideal, so it factors uniquely
    through an inclusion $kappa(x)->K$.

  + *Construct a morphism from the pair.* Conversely, choose an affine
    neighborhood $ops.spec A$ of $x$, with prime $idl.p$. Compose
    $A->A_idl.p->kappa(idl.p)->K$ and take spectra. Its image is $x$;
    restriction to any smaller affine neighborhood gives the same map,
    because its ring map is the same composite of germs. XL's uniqueness
    glues these descriptions and makes the construction independent of the
    chart. They are inverse.

  + *Check functoriality and rational points.* Applying the same local-map factorization to
    $f$ gives the residue-field map. If $kappa(x)=k$ and $f$ is over $k$,
    the inclusions $k->kappa(f(x))->k$ compose to the identity, so
    $kappa(f(x))=k$ as a $k$-field.
]

#metadata(none) <sup-mg-11>
#proposition(number: "MG-11", title: "Finite morphisms")[
  + Finite morphisms have finite fibers, are closed, and are proper.
    Their composition, base-change, and affine criteria are in
    #book-link(<sup-lp>)[the locality calculus]; properness uses the definition in
    #book-link(<text-ii-4>)[II.4].

  + A quasi-finite morphism means a finite-type
    morphism with finite fibers in this discussion.

  + The map
    $coprod(X_i, i=1, top: 2)->sch.a^1_k$ where $X_1=sch.a^1_k$ and $X_2=sch.a^1_k minus {0}$, given by
    identity and inclusion is surjective and quasi-finite but not finite.
    Thus finite fibers, even with surjectivity, do not imply finiteness.
]

#proof[

  + *Prove finiteness of fibers.* Over $V=ops.spec A$ write the inverse image as $ops.spec B$ with $B$
    finite over $A$, using LP. MG-3 makes a fiber the spectrum of a
    finite-dimensional algebra over $kappa(y)$. Such an algebra is Artinian
    and has only finitely many prime ideals (Check!).

  + *Prove closedness.* A finite algebra is integral;
    lying over applied also to $B/J$ shows that the image of $V(J)$ is
    $V(u^(-1)(J))$. Integrality of finite algebras and lying over are
    the algebraic facts left to the reader here (Check!). Thus the affine restriction is closed. Target locality
    of closedness proves that $f$ is closed.

  + *Prove properness.* Every base change is again
    finite by LP, so $f$ is universally closed. It is finite type and is
    separated, since its affine diagonal corresponds to the surjective
    multiplication $tensor(B, B, over: A)->B$. Hence it is proper.

  + *Verify the quasi-finite counterexample.* The last displayed map is finite type, surjective, and has one or two
    points in each fiber. Its second component is a closed subset of the
    disjoint union whose image is the nonclosed punctured line. The map is
    not closed and therefore cannot be finite.
]

#metadata(none) <sup-mg-12>
#proposition(number: "MG-12", title: "Quasi-compact scheme-theoretic images")[
  + For a quasi-compact $f:X->Y$, the ideal
    $shf.i=ops.ker(shf.o_Y->f_*shf.o_X)$ is quasi-coherent.

  + The closed
    subscheme it defines is the smallest closed subscheme of $Y$ through
    which $f$ factors, and its formation commutes with open restriction on $Y$.

  + Its underlying closed subset is $overline(f(X))$.

  + These assertions concern
    the kernel even when pushforward itself is not known to be quasi-coherent.

  + For the quasi-compact hypothesis, see
    #link("https://stacks.math.columbia.edu/tag/01R5")[Stacks, Lemma 29.6.3].
    The arbitrary-morphism version is not included here. The closed-subscheme
    criteria of II.3.11(a)–(c) are indexed in #book-link(<sup-cs>)[CS].
]

#proof[

  + *Identify the kernel on affine charts.* Restrict to $V=ops.spec A subset.eq Y$ and choose a finite affine cover
    $W_i=ops.spec B_i$ of $f^(-1)(V)$. Put
    $I=ops.ker(A->product_i B_i)$. A function pulls back to zero exactly
    when it does so on this cover. Over $D(a)$ the cover becomes
    $ops.spec (B_i)_a$; exact localization and its commutation with finite
    products give kernel $I_a$. Thus the actual kernel sheaf on $V$ is
    $tildeOf(I)$. These descriptions prove quasi-coherence and agree under
    open restriction because they describe the same kernel.

  + *Prove factorization and minimality.* The quotient sheaf defines a closed subscheme through which $f$ factors.
    Any other factorization kills its defining ideal, which must lie in
    this kernel; the direction of inclusion of closed subschemes is reversed.
    This proves minimality.

  + *Compute the underlying closed subset.* Finally, the closure of the finite union of the
    images of $W_i$ is the union of their closures, namely
    $union_i V(ops.ker(A->B_i))=V(I)$ by XP-6's closure formula.
    This proves the underlying-space assertion on a cover and hence globally.
]

#metadata(none) <sup-mg-13>
#corollary(number: "MG-13", title: "Images of proper subschemes")[
  Let $X,Y$ be separated finite-type schemes over a Noetherian scheme $S$,
  let $f:X->Y$ be an $S$-morphism, and let $Z$ be a closed subscheme of
  $X$ proper over $S$. The scheme-theoretic image of $Z->Y$ is proper
  over $S$. This is the image statement associated to II.4.4; its image is
  the one of MG-12, and the graph is the closed immersion of MG-5.
]

#proof[

  + *Prove the map from the proper subscheme is proper.* Put $q:Z->Y$. Its graph is closed by MG-5, and projection
    $fiber(Z, Y, base: S)->Y$ is proper by base change from $Z->S$.
    Thus $q$ is proper.

  + *Construct a proper surjection onto the image.* Let $W$ be its scheme-theoretic image, which exists
    by MG-12 since a proper map is quasi-compact. Its underlying subset is
    the image of $q$, since that image is closed. The factor $Z->W$ is
    surjective. It is also proper: it identifies with the base change of
    $q$ along the closed immersion $W->Y$, using that this immersion is
    a monomorphism.

  + *Base change the image.* The scheme $W$ is finite type and separated over $S$, being closed in
    $Y$. To prove universal closedness, make any base change $S'->S$.
    Surjectivity of $Z->W$ survives this base change: each fiber remains
    nonempty after a field extension, as tensoring a nonzero algebra with
    a field extension is faithfully flat (Check!).

  + *Descend closedness and conclude.* For a closed subset $C$ of
    $W_(S')$, its inverse image in $Z_(S')$ is closed and has closed image
    in $S'$ by properness of $Z/S$. Surjectivity identifies this image with
    the image of $C$. Thus $W->S$ is universally closed and is proper.
]
