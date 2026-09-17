#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

=== XL — Scheme locality and gluing <sup-xl>

Use the affine structure sheaf and functoriality of spectrum in
#book-link(<text-ii-2>)[II.2, Propositions 2.2–2.3], and the sheaf tools in
#book-link(<sup-sl>)[SL]. The simultaneous distinguished-neighborhood,
affine-communication, and whole-inverse-image criteria are collected in
#book-link(<sup-lp>)[A Locality Calculus for Morphisms].

Read XL-1–7 after II.2 and before LP-1–15. In XL-6, the form of
II.2.16 using a finite affine cover with quasi-compact overlaps is enough
for this first reading; no diagonal criterion is needed. Return to XL-8
with the affine pushforward formula of II.5.2.

#metadata(none) <sup-xl-1>
#definition(number: "XL-1", title: "Open subschemes")[
  The identification of a distinguished open with a spectrum, and the scheme
  structure on any open subset, are established in
  #book-link(<sup-proof-2-1>)[II.2.1] and #book-link(<sup-proof-2-2>)[II.2.2 below].
  The identification is induced by localization and respects the restricted
  structure sheaf; it is not only a homeomorphism of point sets.
]

#metadata(none) <sup-xl-2>
#proposition(number: "XL-2", title: "Morphisms into an affine scheme")[
  - For any scheme $X$ and ring $A$, taking global sections gives the natural
    bijection $ ops.hom(X, ops.spec A, over: cat.sch) simeq
    ops.hom(A, Gamma(X, shf.o_X), over: cat.ring) $ proved in
    #book-link(<sup-proof-2-4>)[II.2.4].

  - In particular, $ops.spec ZZ$ is terminal.
    Its points are $(0)$ and $(p)$ for positive primes $p$; $(0)$ is generic
    and the $(p)$ are closed.

  - The spectrum of the zero ring is empty and is
    initial among schemes, including when the target is empty.
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

#metadata(none) <sup-xl-4>
#proposition(number: "XL-4", title: "Gluing schemes")[
  - The scheme-gluing construction with specified overlap isomorphisms and
    cocycle compatibility is proved in #book-link(<sup-proof-2-12>)[II.2.12].
    It glues both the underlying spaces and the structure sheaves. The specified
    charts identify stalks with their original local rings and supply affine
    neighborhoods.

  - The disjoint union is the case of empty overlaps between
    distinct components.

  - Uniqueness always preserves the specified charts.
]

#metadata(none) <sup-xl-5>
#lemma(number: "XL-5", title: "Target-cover criterion for isomorphisms")[
  - For a fixed $f:X->Y$ and an open cover $V_i$ of $Y$, if every restricted
    map $f^(-1)(V_i)->V_i$ is an isomorphism, then $f$ is an isomorphism;
    see #book-link(<sup-proof-2-17>)[II.2.17(a)]. The local maps must be restrictions
    of the given morphism, so that their inverses agree on overlaps.

  - Two copies of a nonempty scheme mapping identically onto one copy show why
    being an isomorphism locally on the source is not enough.
]

#metadata(none) <sup-xl-6>
#definition(number: "XL-6", title: "Global principal opens")[
  - For $f in Gamma(X, shf.o_X)$, let $X_f$ be the locus where its germ is a
    unit. On any affine chart, this is the distinguished open of the restricted
    function.

  - If $X$ is quasi-compact and a global section $a$ vanishes on
    $X_f$, then $f^n a=0$ for some $n$.

  - If $X$ is quasi-compact and quasi-separated, restriction induces
    $Gamma(X, shf.o_X)_f simeq Gamma(X_f, shf.o_X)$, sending $a/f^n$ to the
    restriction of $a$ divided by $f^n$. The proof, including the role of
    quasi-compact overlaps, is in #book-link(<sup-proof-2-16>)[II.2.16].

  - A function defined on only one chart does not define a global $X_f$.

  - For the module and invertible-sheaf version, see
    #book-link(<text-ii-5>)[II.5, Lemma 5.14 and Remark 5.14.1].
]

#metadata(none) <sup-xl-7>
#proposition(number: "XL-7", title: "Recognizing affine schemes")[
  The unit-ideal criterion for global principal affine opens is proved in
  #book-link(<sup-proof-2-17>)[II.2.17(b)]. For a morphism over an affine target,
  apply #book-link(<sup-lp>)[the whole-inverse-image criterion]: affineness is
  checked on the entire inverse images of target opens, not on an arbitrary
  collection of affine source charts.
]

#metadata(none) <sup-xl-8>
#remark(number: "XL-8", title: "Affine ring maps and principal-open index")[
  For $phi:A->B$ and $f:ops.spec B->ops.spec A$, the map $phi$ is
  injective exactly when $shf.o_(ops.spec A)->f_*shf.o_(ops.spec B)$ is
  injective. The canonical identification uses the affine pushforward formula
  of #book-link(<text-ii-5>)[II.5, Proposition 5.2]. Surjectivity and closed
  immersions are indexed in #book-link(<sup-cs-1>)[CS-1]; dominance is distinguished
  from injectivity in #book-link(<sup-xp-1e>)[XP-1e].

  For II.2.A and II.2.18(a), the following is a lookup index:

  - Empty $D(f)$, units, and the empty spectrum: the spectrum and localization
  formulas of #book-link(<text-ii-2>)[II.2, Lemma 2.1 and Proposition 2.2].
  - Radical ideals and closed subsets: II.2, Lemma 2.1; see also
  #book-link(<sup-cs-3>)[CS-3] for their reduced structures.
  - Quasi-compact distinguished opens: #book-link(<sup-xl-1>)[XL-1] and
  #book-link(<sup-xp-4>)[XP-4].
  - Closed points and maximal ideals: #book-link(<sup-xp-1b>)[XP-1b].

  For II.3.1–II.3.4, use #book-link(<sup-lp>)[the locality calculus]. Intersections
  of affine charts need not be affine; #book-link(<sup-mg-5>)[MG-5] gives a
  separatedness hypothesis and an example where it fails.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the sheaf map.* Put $X=ops.spec A$. Under the affine pushforward formula, the sheaf map
    in question is $tildeOf(A)->tildeOf(B)$ induced by the $A$-linear map
    $phi$.

  + *Localize an injective ring map.* If $phi$ is injective, its localization $A_f->B_f$ is injective
    for every $f in A$ by AL-2. These are the maps on the distinguished basis
    of $X$; sections on any open are detected on that basis, so the sheaf map
    is injective.

  + *Recover the ring map on global sections.* Conversely, an injective sheaf map is injective on every open,
    in particular on $X$, where it is precisely $phi:A->B$.

  + *Read the remaining index entries.* The remaining entries refer to the indicated spectrum, localization, and
    locality results and introduce no further criterion.
]

#block(sticky: true)[#strong[Application: II.2.1]] <sup-proof-2-1>

#exercise(title: "Exercise 2.1")[
  For $X=ops.spec A$ and $f in A$, show
  $(D(f),shf.o_X|_(D(f))) simeq ops.spec A_f$.
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
    from the localized multiplicative set ${1,f,f^2,dots}$.  Thus $pi$ is a
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
    restriction.  A morphism of sheaves which is an isomorphism on a basis is
    an isomorphism, so $pi$ yields the required isomorphism of schemes.
]

#block(sticky: true)[#strong[Application: II.2.2]] <sup-proof-2-2>

#exercise(title: "Exercise 2.2")[
  If $U subset.eq X$ is open in a scheme, show $(U,shf.o_X|_U)$ is a scheme.
  It is the *open subscheme* induced on $U$.
]

#proof[
  #set enum(numbering: "1.")

  + *Choose a distinguished neighborhood.* Let $x in U$.  Choose an affine neighborhood
    $V=ops.spec A subset.eq X$ of $x$.  The intersection $U inter V$ is open in
    $ops.spec A$, and principal opens form a basis of its topology, so there is
    some $f in A$ with
    $
      x in D(f) subset.eq U inter V.
    $

  + *Obtain an affine neighborhood in the open.* By Exercise 2.1, with its restricted structure sheaf, this neighborhood is
    $ops.spec A_f$.  Hence every point of $(U,shf.o_X|_U)$ has an affine open
    neighborhood, which is the definition of a scheme.

  + *Compare restrictions and stalks.* The sheaf
    restriction is transitive, so on $D(f)$ the structure sheaf restricted
    from $U$ is exactly the one restricted from $V$.

  In particular, its stalks are the same local rings as those of $X$.
]

#block(sticky: true)[#strong[Application: II.2.4]] <sup-proof-2-4>

#exercise(title: "Exercise 2.4")[
  Show that taking global sections gives a natural bijection
  $ops.hom(X, ops.spec A, over: cat.sch) simeq
  ops.hom(A, Gamma(X, shf.o_X), over: cat.ring)$.
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
]

#block(sticky: true)[#strong[Application: II.2.12]] <sup-proof-2-12>

#exercise(title: "Exercise 2.12 (Glueing Lemma)")[
  Let schemes $X_i$ have open subschemes $U_(i j)$ and isomorphisms
  $phi_(i j):U_(i j)->U_(j i)$ with $phi_(j i)=phi_(i j)^(-1)$ and the
  usual cocycle compatibility on triple overlaps. Show that the $X_i$ glue
  to a scheme $X$ in which each $X_i$ is open and the prescribed overlaps
  are identified. Include the special case of the disjoint union.
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
    Their images cover $X$, and
    $q_i(X_i) inter q_j(X_j)$ is the common image of $U_(i j)$ and $U_(j i)$.

  + *Glue the structure sheaves.* Define the structure sheaf by compatible families:
    $
      shf.o_X (W)=
      { (s_i)_i : s_i in shf.o_(X_i) (q_i^(-1)(W)),
        phi_(i j)^sharp(s_j)=s_i " on every overlap" }.
    $
    Restrictions are componentwise.  The sheaf axioms follow by applying the
    sheaf axiom separately on every $X_i$; compatibility of the glued sections
    follows from compatibility before gluing.  Projection to the $i$-th
    component identifies
    $shf.o_X|_(q_i(X_i))$ with $shf.o_(X_i)$, and under these identifications the
    transition map is the prescribed $phi_(i j)$.

  + *Verify the scheme and uniqueness properties.* Since the images $q_i(X_i)$ are open and each is a scheme, every point of
    $(X,shf.o_X)$ has an affine neighborhood.  Thus it is a scheme.  The same
    compatible-family description shows the universal property: compatible
    morphisms out of the $X_i$ glue uniquely.  Consequently, any two schemes
    obtained from the data are uniquely isomorphic in a way compatible with
    all $q_i$.

  + *Recover disjoint unions.* For the disjoint union, take $U_(i j)=emptyset$ when $i != j$ and
    $U_(i i)=X_i$.  There are then no cross-component compatibility conditions,
    so the construction is the ordinary topological disjoint union with
    componentwise structure sheaf.
]

#block(sticky: true)[#strong[Application: II.2.16]] <sup-proof-2-16>

#exercise(title: "Exercise 2.16")[
  For $f in Gamma(X, shf.o_X)$, let $X_f$ be the points where $f_x$ is a unit.

  + On $ops.spec B subset.eq X$, show $X_f inter ops.spec B=D(f|_(ops.spec B))$; hence
    $X_f$ is open.
  + If $X$ is quasi-compact and $a|_(X_f)=0$, show $f^n a=0$ for some $n$.
  + If $X$ has a finite affine cover with quasi-compact pairwise
    intersections, show each $b in Gamma(X_f, shf.o)$ satisfies
    $f^n b=a|_(X_f)$ for some $n$ and $a in Gamma(X, shf.o_X)$.
  + Under this hypothesis, conclude $Gamma(X_f, shf.o) simeq Gamma(X, shf.o_X)_f$.
]

#proof[
  Write $A=Gamma(X, shf.o_X)$.

  + Let $U=ops.spec B subset.eq X$ and write $f_U in B$ for the restriction of
    $f$.  A point $p in U$ belongs to $X_f$ exactly when the germ of $f_U$ in
    $B_p$ is a unit.  This happens exactly when $f_U in.not p$, hence exactly
    when $p in D(f_U)$.  Therefore
    $X_f inter U=D(f_U)$.  The right side is open for every affine $U$, so
    $X_f$ is open.

  + *Clear a vanishing section by one power.*

    - *Find powers on a finite affine cover.* Choose a finite affine cover $X=union_(i=1)^r U_i$, possible because $X$
      is quasi-compact.  Put $A_i=Gamma(U_i, shf.o_X)$ and let $f_i,a_i$ be the
      restrictions of $f,a$.  On the affine scheme $U_i$, the hypothesis says
      that $a_i/1=0$ in $(A_i)_(f_i)$.  Hence
      $f_i^(n_i)a_i=0$ for some $n_i$.

    - *Choose a common exponent.* Taking
      $n=max_i n_i$ gives $(f^n a)|_(U_i)=0$ for every $i$.  A section which
      vanishes on an open cover is zero, so $f^n a=0$ on $X$.

  + *Extend a section after multiplication by a power.*

    - *Clear denominators on the affine charts.* Let $X=union_(i=1)^r U_i$ be the given affine cover and set
      $U_(i j)=U_i inter U_j$.  On
      $(U_i)_f=D(f_i)$, Exercise 2.1 identifies $b$ with an element of
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

#block(sticky: true)[#strong[Application: II.2.17]] <sup-proof-2-17>

#exercise(title: "Exercise 2.17 (A Criterion for Affineness)")[
  + If $f:X->Y$ is locally an isomorphism over an open cover of $Y$, show
    $f$ is an isomorphism.
  + Show $X$ is affine iff finitely many $f_i in A=Gamma(X, shf.o_X)$ generate
    the unit ideal and every $X_(f_i)$ is affine.
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
      corresponding under Exercise 2.4 to $ops.id_A$.  Its inverse image of
      $D(f_i)$ is $X_(f_i)$.  The latter is affine by hypothesis.

    - *Compute sections on its inverse-image charts.* Moreover,
      its pairwise intersections are principal opens in an affine scheme, hence
      affine and in particular quasi-compact.  Exercise 2.16(d) therefore gives
      $
        Gamma(X_(f_i), shf.o_X) simeq A_(f_i).
      $

    - *Apply part (a).* Under this isomorphism, the restriction of $psi$ over $D(f_i)$ is the
      affine-scheme morphism induced by the identity of $A_(f_i)$, so it is an
      isomorphism.  Part (a), applied to the cover ${D(f_i)}$ of
      $ops.spec A$, now shows that $psi$ is an isomorphism.  Hence $X$ is
      affine.

]
