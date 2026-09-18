#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

== XL — Scheme locality and gluing <sup-xl>

Use the affine structure sheaf and functoriality of spectrum in
#book-link(<text-ii-2>)[II.2, Propositions 2.2–2.3], and the sheaf tools in
#book-link(<sup-sl>)[SL]. The simultaneous distinguished-neighborhood,
affine-communication, and whole-inverse-image criteria are collected in
#book-link(<sup-lp>)[A Locality Calculus for Morphisms].

Read XL-1–XL-7 after II.2 and before LP-1–LP-15. In XL-6, the form of
II.2.16 using a finite affine cover with quasi-compact overlaps is enough
for this first reading; no diagonal criterion is needed. Return to XL-8
with the affine pushforward formula of II.5.2.

#metadata(none) <sup-proof-2-1>
#metadata(none) <sup-proof-2-2>
#metadata(none) <sup-xl-1>
#proposition(number: "XL-1", title: "Open subschemes")[
  For $X=ops.spec A$ and $f in A$, localization induces an isomorphism
  $(D(f),shf.o_X|_(D(f))) simeq ops.spec A_f$.
  For every open subset $U$ of a scheme $X$, the restricted locally ringed
  space $(U,shf.o_X|_U)$ is a scheme, called the *open subscheme* on $U$.
  Its stalks are the corresponding local rings of $X$.

  This proves #book-link(<exercise-2-1>)[Exercise II.2.1] and
  #book-link(<exercise-2-2>)[Exercise II.2.2].
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the underlying spaces.* The map $A->A_f$ induces
    $pi:ops.spec A_f->ops.spec A$.  Extension and contraction give inverse
    bijections
    $
      {q in ops.spec A_f} arrow.l.r {p in ops.spec A : f in.not p},
    $
    because the prime ideals of a localization are exactly the primes disjoint
    from the localized multiplicative set ${1,f,f^2,dots}$ (Check!).  Thus $pi$ is a
    homeomorphism from $ops.spec A_f$ onto $D(f)$: the inverse image of
    $D(g)$ is $D(g/1)$, and these distinguished opens form bases on both sides.

  + *Identify the structure sheaves.* This homeomorphism also identifies the structure sheaves.  The opens
    $D(f g)=D(f) inter D(g)$, for $g in A$, form a basis
    of $D(f)$; their inverse images are $D(g/1)$, and on these opens the two rings
    of sections are
    $
      shf.o_(ops.spec A)(D(f g))=A_(f g)
      quad "and" quad
      shf.o_(ops.spec A_f)(D(g/1))=(A_f)_(g/1).
    $
    The canonical localization map identifies these rings, compatibly with
    restriction; these localization identities are algebraic checks (Check!).  A morphism of sheaves which is an isomorphism on a basis is
    an isomorphism, so $pi$ yields the required isomorphism of schemes.
  + *Choose a distinguished neighborhood.* Let $x in U$.  Choose an affine neighborhood
    $V=ops.spec A subset.eq X$ of $x$.  The intersection $U inter V$ is open in
    $ops.spec A$, and principal opens form a basis of its topology, so there is
    some $f in A$ with
    $
      x in D(f) subset.eq U inter V.
    $

  + *Obtain an affine neighborhood in the open.* By the distinguished-open isomorphism just proved, with its restricted structure sheaf, this neighborhood is
    $ops.spec A_f$.  Hence every point of $(U,shf.o_X|_U)$ has an affine open
    neighborhood, which is the definition of a scheme.

  + *Compare restrictions and stalks.* The sheaf
    restriction is transitive, so on $D(f)$ the structure sheaf restricted
    from $U$ is exactly the one restricted from $V$.

  In particular, its stalks are the same local rings as those of $X$.
]

#metadata(none) <sup-proof-2-4>
#metadata(none) <sup-xl-2>
#proposition(number: "XL-2", title: "Morphisms into an affine scheme")[
  - For any scheme $X$ and ring $A$, taking global sections gives the natural
    bijection $ ops.hom(X, ops.spec A, over: cat.sch) simeq
    ops.hom(A, Gamma(X, shf.o_X), over: cat.ring) $.
    This proves #book-link(<exercise-2-4>)[Exercise II.2.4].

  - In particular, $ops.spec ZZ$ is terminal.
    Its points are $(0)$ and $(p)$ for positive primes $p$; $(0)$ is generic
    and the $(p)$ are closed.

  - The spectrum of the zero ring is empty and is
    initial among schemes, including when the target is empty.
]

#proof[
  #set enum(numbering: "1.")

  + *Take global sections.* A scheme morphism $f:X->ops.spec A$ induces on global sections a ring map
    $
      A simeq Gamma(ops.spec A, shf.o) ->^(f^sharp)
      Gamma(X, shf.o_X).
    $
    This defines the map from left to right.

  + *Construct and glue affine morphisms.* Conversely, let $phi:A->Gamma(X, shf.o_X)$.  For each affine open
    $U=ops.spec B subset.eq X$, restriction gives a ring map
    $A->Gamma(U, shf.o_U) simeq B$, hence a scheme morphism
    $U->ops.spec A$.  Cover each overlap $U inter U'$ by affine opens
    $W=ops.spec C$.  Both restricted morphisms $W->ops.spec A$ correspond
    to the same ring map $A->Gamma(X, shf.o_X)->C$.  The affine
    correspondence therefore makes them equal on $W$, and hence on the
    overlap.  The gluing lemma for scheme morphisms now glues them
    to a morphism $X->ops.spec A$.

  + *Check inverse constructions and naturality.* On an affine open, the two constructions are inverse by the contravariant
    equivalence between rings and affine schemes.  Since affine opens cover
    $X$, they are inverse globally.  Every step commutes with precomposition in
    $X$ and with ring maps in $A$, so the bijection is natural.

  + *Identify the terminal and initial schemes.* There is a unique unital
    ring map $ZZ->Gamma(X, shf.o_X)$, so the bijection makes $ops.spec ZZ$
    terminal. Its primes and their inclusions are the elementary arithmetic
    description of $ops.spec ZZ$ (Check!). The zero ring has no prime
    ideals, and the empty locally ringed space has exactly one morphism to
    every scheme, including itself (Check!). Thus its spectrum is initial.
]

#metadata(none) <sup-xl-3>
#lemma(number: "XL-3", title: "Gluing scheme morphisms")[
  - For an open cover $X=union_i U_i$, morphisms $U_i->Y$ agreeing on the
    open subschemes $U_i inter U_j$ glue to a unique scheme morphism $X->Y$.

  - The gluing data consist of continuous maps and compatible maps of structure
    sheaves. The latter glue by #book-link(<sup-sl-3>)[SL-3], and their induced
    stalk maps are local homomorphisms.

  - Equality of scheme morphisms may thus
    be tested on an open cover of the source.
]

#proof[
  #set enum(numbering: "1.")

  + *Glue the point maps.* The local point maps agree on overlaps, so define a unique map $f:X->Y$.
    For an open $V subset.eq Y$, its inverse image intersects $U_i$ in
    $f_i^(-1)(V)$, which is open; thus $f$ is continuous.

  + *Glue the structure-sheaf maps.* A section
    $s in shf.o_Y (V)$ pulls back by $f_i^sharp$ to compatible sections on
    $f^(-1)(V) inter U_i$. Their gluing defines $f^sharp_V\(s)$.
    Uniqueness of gluing makes these maps ring homomorphisms and makes
    them commute with restriction.

  + *Check locality on stalks.* At $x in U_i$, the induced stalk map is
    exactly the stalk map of $f_i$, hence is local. Therefore $(f,f^sharp)$
    is a morphism of locally ringed spaces and thus a scheme morphism.

  + *Prove uniqueness.* Its point map and all its section maps were uniquely forced, proving
    uniqueness. In particular, no affineness assumption on the overlaps is needed.
]

#metadata(none) <sup-proof-2-12>
#metadata(none) <sup-xl-4>
#proposition(number: "XL-4", title: "Gluing schemes")[
  Let $X_i$ be schemes, let $U_(i j)$ be open subschemes of $X_i$ with
  $U_(i i)=X_i$, and let $phi_(i j):U_(i j)->U_(j i)$ be isomorphisms.
  Assume $phi_(i i)=ops.id$, $phi_(j i)=phi_(i j)^(-1)$, and
  $phi_(i j)(U_(i j) inter U_(i k))=U_(j i) inter U_(j k)$, with
  $phi_(j k) compose phi_(i j)=phi_(i k)$ on that overlap.

  There is a scheme $X$ with open immersions $q_i:X_i->X$ whose images
  cover $X$, whose pairwise overlaps are exactly the prescribed $U_(i j)$,
  and whose transition maps are $phi_(i j)$. It is unique up to the unique
  isomorphism preserving the $q_i$. Compatible morphisms from the $X_i$
  glue uniquely to a morphism from $X$.
  Empty overlaps between distinct components give the disjoint union.

  This proves #book-link(<exercise-2-12>)[Exercise II.2.12].
]

#proof[
  #set enum(numbering: "1.")

  + *Glue the underlying spaces.* Form the disjoint union of the underlying spaces and impose the equivalence
    relation generated by
    $
      x equiv phi_(i j)(x)
      quad (x in U_(i j)).
    $
    The inverse and cocycle conditions say exactly that this is already an
    equivalence relation on the indicated points.  Let $X$ be the quotient.
    Give it the topology in which $W subset.eq X$ is open precisely when its
    inverse image in every $X_i$ is open.  Because each $U_(i j)$ is open and
    every $phi_(i j)$ is a homeomorphism, the maps
    $q_i:X_i->X$ are open embeddings.  More explicitly, the inverse image
    in $X_j$ of the image of an open $W_i subset.eq X_i$ is
    $phi_(i j)(W_i inter U_(i j))$, which is open; the cocycle condition
    ensures that no further identifications occur within a single $X_i$.
    The equivalence-relation and quotient-topology checks in this step
    are purely topological (Check!). Their images cover $X$, and
    $q_i(X_i) inter q_j(X_j)$ is the common image of $U_(i j)$ and $U_(j i)$.

  + *Glue the structure sheaves.* Apply SL-4 to the transported ring
    sheaves on the open subsets $q_i(X_i)$. The specified structure-sheaf
    isomorphisms satisfy the same cocycle condition, so the glued sheaf
    restricts to $shf.o_(X_i)$ on each chart. In particular, its stalks
    are the original local rings and the chart maps are locally ringed
    isomorphisms onto their images.

  + *Verify the scheme and uniqueness properties.* Since the images $q_i(X_i)$ are open and each is a scheme, every point of
    $(X,shf.o_X)$ has an affine neighborhood.  Thus it is a scheme.  By XL-3, compatible
    morphisms out of the $X_i$ glue uniquely.  Consequently, any two schemes
    obtained from the data are uniquely isomorphic in a way compatible with
    all $q_i$.

  + *Recover disjoint unions.* For the disjoint union, take $U_(i j)=emptyset$ when $i != j$ and
    $U_(i i)=X_i$.  There are then no cross-component compatibility conditions,
    so the construction is the ordinary topological disjoint union with
    componentwise structure sheaf.
]

#metadata(none) <sup-proof-2-17>
#metadata(none) <sup-xl-5>
#lemma(number: "XL-5", title: "Target-cover criterion for isomorphisms")[
  - For a fixed $f:X->Y$ and an open cover $V_i$ of $Y$, if every restricted
    map $f^(-1)(V_i)->V_i$ is an isomorphism, then $f$ is an isomorphism;
    this proves #book-link(<exercise-2-17>)[Exercise II.2.17(a)].
    The local maps must be restrictions
    of the given morphism, so that their inverses agree on overlaps.
    The affineness criterion in part (b) is XL-7.

  - Two copies of a nonempty scheme mapping identically onto one copy show why
    being an isomorphism locally on the source is not enough.
]

#proof[
  + *Glue the local inverse morphisms.*

    - *Construct the inverse by gluing.* Let ${U_i}$ be an open cover of $Y$ such that each base change
      $f_i:f^(-1)(U_i)->U_i$ is an isomorphism.  Write
      $g_i:U_i->X$ for the composite of $f_i^(-1)$ with the inclusion
      $f^(-1)(U_i)->X$.  On $U_i inter U_j$, both $g_i$ and $g_j$ are inverse to
      the same restriction of $f$, so they agree.  The gluing lemma for
      morphisms gives $g:Y->X$.

    - *Check the two inverse identities.* On every $U_i$, one has $(f compose g)|_(U_i)=ops.id$, hence
      $f compose g=ops.id_Y$.  On every $f^(-1)(U_i)$, one similarly has
      $(g compose f)|_(f^(-1)(U_i))=ops.id$, and these opens cover $X$; hence
      $g compose f=ops.id_X$.  Thus $f$ is an isomorphism.


  The disjoint union of two copies of a nonempty scheme has distinct points
  with the same image, so its map to one copy is not an isomorphism,
  although each source component maps isomorphically.
]

#metadata(none) <sup-proof-2-16>
#metadata(none) <sup-xl-6>
#proposition(number: "XL-6", title: "Global principal opens")[
  For $f in A=Gamma(X, shf.o_X)$, write $X_f$ for the locus where $f_x$
  is a unit.

  + On every affine chart $U=ops.spec B$, one has $X_f inter U=D(f|_U)$.
    In particular, $X_f$ is open.
  + If $X$ is quasi-compact and $a|_(X_f)=0$, then $f^n a=0$ for some $n$.
  + If $X$ has a finite affine cover with quasi-compact pairwise overlaps,
    every $b in Gamma(X_f, shf.o_X)$ satisfies $f^n b=a|_(X_f)$ for some
    $n$ and some $a in A$.
  + Under this last hypothesis, restriction induces the isomorphism
    $A_f simeq Gamma(X_f, shf.o_X)$, with $a/f^n mapsto a|_(X_f)/f^n$.

  The finite-cover hypothesis is equivalent to $X$ being quasi-compact
  and quasi-separated; see XP-11. A function on just one chart does not
  define a global $X_f$. For the module and invertible-sheaf versions, see
  #book-link(<text-ii-5>)[II.5, Lemma 5.14 and Remark 5.14.1].
  This proves #book-link(<exercise-2-16>)[Exercise II.2.16].
]

#proof[
  Write $A=Gamma(X, shf.o_X)$.

  + Let $U=ops.spec B subset.eq X$ and write $f_U in B$ for the restriction of
    $f$.  A point $p in U$ belongs to $X_f$ exactly when the germ of $f_U$ in
    $B_p$ is a unit.  The local-ring unit criterion gives $f_U in.not p$ (Check!), hence exactly
    when $p in D(f_U)$.  Therefore
    $X_f inter U=D(f_U)$.  The right side is open for every affine $U$, so
    $X_f$ is open.

  + *Clear a vanishing section by one power.*

    - *Find powers on a finite affine cover.* Choose a finite affine cover $X=union_(i=1)^r U_i$, possible because $X$
      is quasi-compact.  Put $A_i=Gamma(U_i, shf.o_X)$ and let $f_i,a_i$ be the
      restrictions of $f,a$.  On the affine scheme $U_i$, the hypothesis says
      that $a_i/1=0$ in $(A_i)_(f_i)$.  Hence
      $f_i^(n_i)a_i=0$ for some $n_i$ by the algebraic localization zero
      criterion (Check!).

    - *Choose a common exponent.* Taking
      $n=max_i n_i$ gives $(f^n a)|_(U_i)=0$ for every $i$.  A section which
      vanishes on an open cover is zero, so $f^n a=0$ on $X$.

  + *Extend a section after multiplication by a power.*

    - *Clear denominators on the affine charts.* Let $X=union_(i=1)^r U_i$ be the given affine cover and set
      $U_(i j)=U_i inter U_j$.  On
      $(U_i)_f=D(f_i)$, XL-1 identifies $b$ with an element of
      $(A_i)_(f_i)$.  After choosing a common exponent $n$, write
      $
        f_i^n b=a_i|_((U_i)_f)
        quad "for some" quad a_i in A_i.
      $

    - *Clear differences on the overlaps.* On $U_(i j)$, the difference $a_i-a_j$ vanishes after restriction to
      $(U_(i j))_f$.  Each $U_(i j)$ is quasi-compact, so part (b), applied on
      that open subscheme, gives an exponent $m_(i j)$ such that
      $f^(m_(i j))(a_i-a_j)=0$ on $U_(i j)$.

    - *Choose a common power and glue.* There are only finitely many
      pairs.  Choose one $m$ dominating all $m_(i j)$ and replace every $a_i$
      by $f^m a_i$.  The new $a_i$ agree on all overlaps and therefore glue to
      $a in A$.  On $X_f$, they satisfy
      $f^(n+m)b=a|_(X_f)$.

  + *Identify the localized ring of global sections.*

    - *Construct the restriction homomorphism.* Restriction gives a ring homomorphism
      $
        theta:A_f->Gamma(X_f, shf.o).
      $
      This map exists because $f|_(X_f)$ is a unit: its stalkwise inverses
      are represented by local inverses, which agree and glue.

    - *Prove surjectivity.* Part (c) says
      it is surjective.

    - *Prove injectivity.* If $theta(a/f^r)=0$, then
      $a|_(X_f)=0$; by part (b), $f^n a=0$ for some $n$, which is exactly the
      criterion for $a/f^r=0$ in $A_f$.  Thus $theta$ is also injective and is
      the required isomorphism.

]

#metadata(none) <sup-xl-7>
#proposition(number: "XL-7", title: "Recognizing affine schemes")[
  A scheme $X$ is affine if and only if there are finitely many
  $f_i in A=Gamma(X, shf.o_X)$ generating the unit ideal such that every
  $X_(f_i)$ is affine. Under these conditions, the canonical morphism
  $X->ops.spec A$ corresponding to $ops.id_A$ is an isomorphism.

  This proves #book-link(<exercise-2-17>)[Exercise II.2.17(b)].
]

#proof[
  + *Apply the unit-ideal criterion.*

    - *Treat the affine case.* If $X$ is affine, take the single section $f_1=1$.  It generates the unit
      ideal, $X_(f_1)=X$, and this open is affine.

    - *Obtain the two principal-open covers.* Conversely, suppose $f_1,dots,f_r$ generate the unit ideal of $A$.
      Then the opens
      $X_(f_i)$ cover $X$: at every point some $(f_i)_x$ must be a unit, since a
      linear combination of the $f_i$ is $1$.  The principal opens
      $D(f_i)$ likewise cover $ops.spec A$.

    - *Construct the canonical morphism.* Consider the canonical morphism
      $
        psi:X->ops.spec A
      $
      corresponding under XL-2 to $ops.id_A$.  Its inverse image of
      $D(f_i)$ is $X_(f_i)$.  The latter is affine by hypothesis.

    - *Compute sections on its inverse-image charts.* Moreover,
      its pairwise intersections are principal opens in an affine scheme, hence
      affine and in particular quasi-compact.  XL-6(d) therefore gives
      $
        Gamma(X_(f_i), shf.o_X) simeq A_(f_i).
      $

    - *Apply the target-cover criterion.* Under this isomorphism, the restriction of $psi$ over $D(f_i)$ is the
      affine-scheme morphism induced by the identity of $A_(f_i)$, so it is an
      isomorphism.  XL-5, applied to the cover ${D(f_i)}$ of
      $ops.spec A$, now shows that $psi$ is an isomorphism.  Hence $X$ is
      affine.

]

#metadata(none) <sup-xl-8>
#remark(number: "XL-8", title: "Affine ring maps and principal-open index")[
  For $phi:A->B$ and $f:ops.spec B->ops.spec A$, the map $phi$ is
  injective exactly when $shf.o_(ops.spec A)->f_*shf.o_(ops.spec B)$ is injective. The canonical identification uses the affine pushforward formula of #book-link(<text-ii-5>)[II.5, Proposition 5.2]. Surjectivity and closed immersions are indexed in #book-link(<sup-cs-1>)[CS-1]; dominance is distinguished from injectivity in #book-link(<sup-xp-6>)[XP-6].

  For II.2.A and II.2.18(a), the following is a lookup index:

  - Empty $D(f)$, units, and the empty spectrum: the spectrum and localization formulas of #book-link(<text-ii-2>)[II.2, Lemma 2.1 and Proposition 2.2].
  - Radical ideals and closed subsets: II.2, Lemma 2.1; see also #book-link(<sup-cs-4>)[CS-4] for their reduced structures.
  - Quasi-compact distinguished opens: #book-link(<sup-xl-1>)[XL-1] and #book-link(<sup-xp-10>)[XP-10].
  - Closed points and maximal ideals: #book-link(<sup-xp-3>)[XP-3].

  For II.3.1–II.3.4, use #book-link(<sup-lp>)[the locality calculus]. Intersections of affine charts need not be affine; #book-link(<sup-mg-8>)[MG-8] gives a separatedness hypothesis and an example where it fails.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the sheaf map.* Put $X=ops.spec A$. Under the affine pushforward formula, the sheaf map in question is $tildeOf(A)->tildeOf(B)$ induced by the $A$-linear map
    $phi$.

  + *Localize an injective ring map.* If $phi$ is injective, its localization $A_f->B_f$ is injective for every $f in A$ by AL-3. These are the maps on the distinguished basis of $X$; sections on any open are detected on that basis, so the sheaf map is injective.

  + *Recover the ring map on global sections.* Conversely, an injective sheaf map is injective on every open, in particular on $X$, where it is precisely $phi:A->B$.

  + *Read the remaining index entries.* The remaining entries refer to the indicated spectrum, localization, and locality results and introduce no further criterion.
]
