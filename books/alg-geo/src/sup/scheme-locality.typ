#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

#supplement-numbering("XL")

== XL — Scheme locality and gluing <sup-xl>

#set enum(numbering: "a.i.", spacing: 0.7em)

#proposition(key: "sup-xl-1", title: "Open subschemes")[
  Let $X$ be a scheme.

  + For $U subset X$ open, $(U,shf.o_X|_U)$ is a scheme and
    $shf.o_(U,x)=shf.o_(X,x)$ for $x in U$.
  + If $X=ops.spec A$ and $f in A$, localization induces
    $(D(f),shf.o_X|_(D(f))) simeq ops.spec A_f$.
  (Ex. II.2.1–2)
]

#proof[

  + The map $A->A_f$ induces
    $pi:ops.spec A_f->ops.spec A$.  Extension and contraction give inverse
    bijections
    $
      {q in ops.spec A_f} simeq {p in ops.spec A : f in.not p},
    $
    because the prime ideals of a localization are exactly the primes disjoint
    from the localized multiplicative set ${1,f,f^2,dots}$ (Check!).  Thus $pi$ is a
    homeomorphism from $ops.spec A_f$ onto $D(f)$: the inverse image of
    $D(g)$ is $D(g/1)$, and these distinguished opens form bases on both sides.

  + This homeomorphism also identifies the structure sheaves.  The opens
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
  + Let $x in U$.  Choose an affine neighborhood
    $V=ops.spec A subset X$ of $x$.  The intersection $U inter V$ is open in
    $ops.spec A$, and principal opens form a basis of its topology, so there is
    some $f in A$ with
    $
      x in D(f) subset U inter V.
    $

  + By the distinguished-open isomorphism just proved, with its restricted structure sheaf, this neighborhood is
    $ops.spec A_f$.  Hence every point of $(U,shf.o_X|_U)$ has an affine open
    neighborhood, which is the definition of a scheme.

  + The sheaf
    restriction is transitive, so on $D(f)$ the structure sheaf restricted
    from $U$ is exactly the one restricted from $V$.

  In particular, its stalks are the same local rings as those of $X$.
]

#proposition(key: "sup-xl-2", title: "Global principal opens")[
  Let $(X,shf.o_X)$ be a locally ringed space, $A=Gamma(X, shf.o_X)$, and $f in A$.

  + Define the _unit locus_ of $f$ by
    $X_f=\{x in X:f_x in shf.o_(X,x)^times\}$.

    + $X_f$ is open, and $f|_(X_f)$ is a unit of $Gamma(X_f, shf.o_X)$.
    + If $X$ is a scheme and $U=ops.spec B subset X$, then $X_f inter U=D(f|_U)$.

  + If $X$ is a quasi-compact scheme and $a in A$, then
    $a|_(X_f)=0$ if and only if $f^n a=0$ for some $n in NN$.

  + Suppose $X$ is a scheme with a finite affine cover
    whose pairwise intersections are quasi-compact.

    + For $b in Gamma(X_f, shf.o_X)$, there exist $n>=0$ and $a in A$ with
      $f^n b=a|_(X_f)$.
    + Restriction induces an isomorphism
      $
          A_f & to Gamma(X_f, shf.o_X), \
        a/f^n & mapsto a|_(X_f)/(f|_(X_f))^n.
      $
  (Ex. II.2.16)
]

#proof[

  Write $A=Gamma(X, shf.o_X)$.

  + If $f_x$ is a unit, represent its inverse
    near $x$. By SL-1, shrink until its product with $f$ is $1$. Thus
    $X_f$ is open. The inverses on these neighborhoods agree by uniqueness
    and glue to an inverse of $f|_(X_f)$.

  + Let $U=ops.spec B subset X$ and write $f_U in B$ for the restriction of
    $f$.  A point $p in U$ belongs to $X_f$ if and only if the germ of $f_U$ in
    $B_p$ is a unit. By the local-ring unit criterion, the germ is a unit if
    and only if $f_U in.not p$ (Check!), which means $p in D(f_U)$. Therefore
    $X_f inter U=D(f_U)$.  The right side is open for every affine $U$, so
    $X_f$ is open.

  + If $X=emptyset$, the vanishing and localization assertions hold in the
    zero ring. Otherwise choose a nonempty finite affine cover.

    + Choose a finite affine cover $X=union_(i=1)^r U_i$, possible because $X$
      is quasi-compact.  Put $A_i=Gamma(U_i, shf.o_X)$ and let $f_i,a_i$ be the
      restrictions of $f,a$.  On the affine scheme $U_i$, the hypothesis says
      that $a_i/1=0$ in $(A_i)_(f_i)$.  Hence
      $f_i^(n_i)a_i=0$ for some $n_i$ by the algebraic localization zero
      criterion (Check!).

    + Taking
      $n=max_i n_i$ gives $(f^n a)|_(U_i)=0$ for every $i$.  A section which
      vanishes on an open cover is zero, so $f^n a=0$ on $X$ by SL-1.
      Conversely, since $f|_(X_f)$ is a unit, $f^n a=0$ implies $a|_(X_f)=0$.

  + To obtain a global numerator for $b in Gamma(X_f, shf.o_X)$, proceed as follows.

    + Let $X=union_(i=1)^r U_i$ be the given affine cover and set
      $U_(i j)=U_i inter U_j$.  On
      $(U_i)_f=D(f_i)$, XL-1 identifies $b$ with an element of
      $(A_i)_(f_i)$.  After choosing a common exponent $n$, write
      $
        f_i^n b=a_i|_((U_i)_f)
        quad "for some" quad a_i in A_i.
      $

    + On $U_(i j)$, the difference $a_i-a_j$ vanishes after restriction to
      $(U_(i j))_f$.  Each $U_(i j)$ is quasi-compact, so the vanishing assertion, applied on
      that open subscheme, gives an exponent $m_(i j)$ such that
      $f^(m_(i j))(a_i-a_j)=0$ on $U_(i j)$.

    + There are only finitely many
      pairs.  Choose one $m$ dominating all $m_(i j)$ and replace every $a_i$
      by $f^m a_i$.  The new $a_i$ agree on all overlaps and therefore glue to
      $a in A$.  On $X_f$, they satisfy
      $f^(n+m)b=a|_(X_f)$.

  + To identify the localization with the ring of sections, use the following map.

    + Restriction gives a ring homomorphism
      $
        theta:A_f->Gamma(X_f, shf.o).
      $
      This map exists because $f|_(X_f)$ is a unit: its stalkwise inverses
      are represented by local inverses, which agree and glue.

    + The global-numerator assertion says
      it is surjective.

    + If $theta(a/f^r)=0$, then
      $a|_(X_f)=0$; by the vanishing assertion, $f^n a=0$ for some $n$, which is exactly the
      criterion for $a/f^r=0$ in $A_f$.  Thus $theta$ is also injective and is
      the required isomorphism.
]

The finite-cover hypothesis is equivalent to quasi-compactness and
quasi-separatedness; see #supplement-link(<sup-xp-11>)[XP-11]. For the module
and invertible-sheaf versions, see #book-link(<text-ii-5>)[II.5, Lemma 5.14
  and Remark 5.14.1].

#proposition(key: "sup-xl-3", title: "Morphisms into an affine scheme")[
  For every locally ringed space $X$ and ring $A$, there is a natural bijection
  $
    ops.hom(X, ops.spec A, over: cat.lrs) & to
                                            ops.hom(A, Gamma(X, shf.o_X), over: cat.ring), \
                                        h & mapsto Gamma(h^sharp).
  $
  For $phi:A to Gamma(X, shf.o_X)$, its corresponding morphism satisfies
  $h^(-1)(D(a))=X_(phi(a))$ for all $a in A$.
  (Ex. II.2.4)
]

#proof[

  + Put $B=Gamma(X, shf.o_X)$.
    For $x in X$, let $rho_x:B->shf.o_(X,x)$ be the germ map and let
    $idl.m_x$ be the maximal ideal of this local ring. Define
    $
      eta_(X)(x)=rho_x^(-1)(idl.m_x) in ops.spec B.
    $
    This is a prime ideal because it is the inverse image of a prime ideal.
    For $b in B$, its principal open has inverse image
    $
      eta_X^(-1)(D(b))=X_b:={x in X | b_x in shf.o_(X,x)^times}.
    $
    XL-2 makes $X_b$ open, so $eta_X$ is continuous because the $D(b)$ form a basis.

  + On $X_b$, the local inverses of $b$
    agree by uniqueness and glue, so $b|_(X_b)$ is a unit. Localization
    therefore gives a unique ring map
    $
      B_b simeq shf.o_(ops.spec B)(D(b))->shf.o_(X)(X_b),
      quad c/b^n mapsto c|_(X_b)(b|_(X_b))^(-n).
    $
    These maps commute with restrictions between principal opens: on both
    sides they extend the restriction of $B$, and uniqueness of localization
    forces equality. By #supplement-link(<sup-sl-2>)[SL-2], they extend
    uniquely to a sheaf map $shf.o_(ops.spec B)->(eta_X)_*shf.o_X$.
    At $x$, put $idl.p=eta_X(x)$. The stalk map is the localization
    $B_idl.p->shf.o_(X,x)$ of $rho_x$. Its inverse image of $idl.m_x$ is
    $idl.p B_idl.p$, since a fraction $c/d$ with $d in.not idl.p$ maps into
    $idl.m_x$ exactly when $c in idl.p$. It is therefore local.
    We have constructed a morphism of locally ringed spaces $eta_X$;
    under $Gamma(ops.spec B, shf.o) simeq B$, its global-sections map is $ops.id_B$.

  + A morphism
    $h:X->ops.spec A$ induces a ring map
    $alpha(h):A->Gamma(X, shf.o_X)=B$. Conversely, for $phi:A->B$, set
    $
      beta(phi)=ops.spec (phi) compose eta_X:X->ops.spec A.
    $
    Functoriality of $ops.spec$ and the preceding identity on global
    sections give $alpha(beta(phi))=phi$.

  + Suppose
    $alpha(h)=phi$. At $x$, the composite
    $A->A_(h(x))->shf.o_(X,x)$ is $rho_x compose phi$.
    Locality of the second map implies
    $
      h(x)=(rho_x compose phi)^(-1)(idl.m_x).
    $
    This is also the point map of $beta(phi)$. For $a in A$, both
    morphisms therefore have inverse image $X_(phi(a))$ over $D(a)$.
    Their section maps $A_a->shf.o_(X)(X_(phi(a)))$ both extend the
    restriction of $phi$, so uniqueness of localization makes them equal.
    Principal opens form a basis, hence their sheaf maps agree by SL-2.
    Thus $h=beta(phi)$, proving $beta(alpha(h))=h$.

  + For a morphism of locally ringed spaces
    $u:X'->X$, let $u^sharp:B->Gamma(X', shf.o_(X'))$ be its map on
    global sections. The uniqueness just proved gives
    $eta_X compose u=ops.spec (u^sharp) compose eta_(X')$.
    Moreover, precomposing $h$ with $u$ sends $alpha(h)$ to
    $u^sharp compose alpha(h)$, while composing $h$ with
    $ops.spec (v)$ for a ring map $v:A'->A$ sends it to $alpha(h) compose v$.
    The bijection is therefore natural in both variables, which is the
    stated adjunction. Scheme morphisms are precisely morphisms of their
    underlying locally ringed spaces, so the scheme case follows.
]

#proposition(key: "sup-xl-4", title: "Initial and terminal schemes")[
  + $ops.spec ZZ$ is terminal in $cat.sch$. Its points are $(0)$ and $(p)$
    for positive primes $p$; $(0)$ is generic and the $(p)$ are closed.
  + $ops.spec 0=emptyset$ is initial in $cat.sch$.
]

#proof[
  + There is a unique unital ring map $ZZ->Gamma(X, shf.o_X)$, so the bijection makes $ops.spec ZZ$ terminal. Its primes and their inclusions are the elementary arithmetic description of $ops.spec ZZ$ (Check!). The zero ring has no prime ideals, and the empty locally ringed space has exactly one morphism to every scheme, including itself (Check!). Thus its spectrum is initial.
]

#lemma(key: "sup-xl-5", title: "Gluing scheme morphisms")[
  Let $X=union_i U_i$ be an open cover and let $f_i:U_i to Y$ be scheme morphisms
  satisfying $f_i|_(U_i inter U_j)=f_j|_(U_i inter U_j)$.
  There is a unique $f:X to Y$ with $f|_(U_i)=f_i$ for every $i$.
  In particular, for $f,g:X to Y$,
  $
    f=g & arrow.l.r.double f|_(U_i)=g|_(U_i) " for every " i.
  $
]

#proof[

  + The local point maps agree on overlaps, so define a unique map $f:X->Y$.
    For an open $V subset Y$, its inverse image intersects $U_i$ in
    $f_i^(-1)(V)$, which is open; thus $f$ is continuous.

  + A section
    $s in shf.o_Y (V)$ pulls back by $f_i^sharp$ to compatible sections on
    $f^(-1)(V) inter U_i$. Their gluing defines $f^sharp_V\(s)$.
    Uniqueness of gluing makes these maps ring homomorphisms and makes
    them commute with restriction.

  + At $x in U_i$, the induced stalk map is
    exactly the stalk map of $f_i$, hence is local. Therefore $(f,f^sharp)$
    is a morphism of locally ringed spaces and thus a scheme morphism.

  + Its point map and all its section maps were uniquely forced, proving
    uniqueness. In particular, no affineness assumption on the overlaps is needed.
]

#proposition(key: "sup-xl-6", title: "Gluing schemes")[
  Let $X_i$ be schemes, $U_(i j) subset X_i$ open subschemes, and
  $phi_(i j):U_(i j) to U_(j i)$ isomorphisms. Assume
  $
    U_(i i)=X_i, quad phi_(i i)=ops.id, quad phi_(j i)=phi_(i j)^(-1), \
    phi_(i j)(U_(i j) inter U_(i k))=U_(j i) inter U_(j k), \
    phi_(j k) compose phi_(i j)=phi_(i k) " on " U_(i j) inter U_(i k).
  $

  + There is a _glued scheme_ $X$ with open immersions $q_i:X_i to X$
    satisfying
    $
      X=union_i q_i(X_i), quad q_i|_(U_(i j))=q_j compose phi_(i j), \
      q_i^(-1)(q_j(X_j))=U_(i j).
    $

    + $(X,(q_i)_i)$ is unique up to a unique isomorphism respecting all $q_i$.
    + For every scheme $Y$, restriction identifies $ops.hom(X, Y)$ with
      families $f_i:X_i to Y$ satisfying $f_i|_(U_(i j))=f_j compose phi_(i j)$.
  + If $U_(i j)=emptyset$ for $i!=j$, then $X=coprod(X_i, i)$ in $cat.sch$.
  (Ex. II.2.12)
]

#proof[

  + Form the disjoint union of the underlying spaces and impose the equivalence
    relation generated by
    $
      x equiv phi_(i j)(x)
      quad (x in U_(i j)).
    $
    The inverse and cocycle conditions say exactly that this is already an
    equivalence relation on the indicated points.  Let $X$ be the quotient.
    Give it the topology in which $W subset X$ is open precisely when its
    inverse image in every $X_i$ is open.  Because each $U_(i j)$ is open and
    every $phi_(i j)$ is a homeomorphism, the maps
    $q_i:X_i->X$ are open embeddings.  More explicitly, the inverse image
    in $X_j$ of the image of an open $W_i subset X_i$ is
    $phi_(i j)(W_i inter U_(i j))$, which is open; the cocycle condition
    ensures that no further identifications occur within a single $X_i$.
    The equivalence-relation and quotient-topology checks in this step
    are purely topological (Check!). Their images cover $X$, and
    $q_i(X_i) inter q_j(X_j)$ is the common image of $U_(i j)$ and $U_(j i)$.

  + Apply SL-4 to the transported ring
    sheaves on the open subsets $q_i(X_i)$. The specified structure-sheaf
    isomorphisms satisfy the same cocycle condition, so the glued sheaf
    restricts to $shf.o_(X_i)$ on each chart. In particular, its stalks
    are the original local rings and the chart maps are locally ringed
    isomorphisms onto their images.

  + Since the images $q_i(X_i)$ are open and each is a scheme, every point of
    $(X,shf.o_X)$ has an affine neighborhood.  Thus it is a scheme.  By XL-5, compatible
    morphisms out of the $X_i$ glue uniquely.  Consequently, any two schemes
    obtained from the data are uniquely isomorphic in a way compatible with
    all $q_i$.

  + For the disjoint union, take $U_(i j)=emptyset$ when $i != j$ and
    $U_(i i)=X_i$.  There are then no cross-component compatibility conditions,
    so the construction is the ordinary topological disjoint union with
    componentwise structure sheaf.
]

The following criterion assembles inverses over an open cover of the target.
It is the final step in the affineness criterion below. An open cover of the
source alone does not suffice: $coprod(Y, i in {1,2}) to Y$ (the two identity maps)
is locally an isomorphism on the source for nonempty $Y$, but is not injective.

#lemma(key: "sup-xl-7", title: "Target-cover criterion for isomorphisms")[
  Let $f:X to Y$ be a scheme morphism, $Y=union_i V_i$ an open cover, and
  $f_i:f^(-1)(V_i) to V_i$ the restrictions of $f$. Then
  $
    f " is an isomorphism" & arrow.l.r.double f_i " is an isomorphism for every " i.
  $
  (Ex. II.2.17(a))
]

#proof[
  The forward implication follows by restriction. For the converse:

  + Write $f_i:f^(-1)(V_i) to V_i$ for the
    restrictions and $g_i:V_i to X$ for $f_i^(-1)$ followed by inclusion.
    On $V_i inter V_j$, the two maps are inverses to the same restriction
    of $f$, so they agree. XL-5 gives a morphism $g:Y to X$.

  + On every $V_i$,
    $(f compose g)|_(V_i)=ops.id$. On every $f^(-1)(V_i)$,
    $(g compose f)|_(f^(-1)(V_i))=ops.id$. These are covers of $Y$ and $X$,
    respectively, so the equality criterion of XL-5 gives
    $f compose g=ops.id_Y$ and $g compose f=ops.id_X$.
]

#proposition(key: "sup-xl-8", title: "Recognizing affine schemes")[
  Let $X$ be a scheme and $A=Gamma(X, shf.o_X)$. Then $X$ is affine if and
  only if there are $f_1,dots,f_r in A$ with $(f_1,dots,f_r)=A$ such that
  $X_(f_i)$ is affine for every $i$.
  Under these conditions the canonical morphism $X to ops.spec A$
  corresponding to $ops.id_A$ is an isomorphism.
  (Ex. II.2.17(b))
]

#proof[
  + If $X$ is affine, take the single section $f_1=1$.  It generates the unit
    ideal, $X_(f_1)=X$, and this open is affine.

  + Conversely, suppose $f_1,dots,f_r$ generate the unit ideal of $A$.
    Then the opens
    $X_(f_i)$ cover $X$: at every point some $(f_i)_x$ must be a unit, since a
    linear combination of the $f_i$ is $1$.  The principal opens
    $D(f_i)$ likewise cover $ops.spec A$.

  + Consider the canonical morphism
    $
      psi:X->ops.spec A
    $
    corresponding under XL-3 to $ops.id_A$.  Its inverse image of
    $D(f_i)$ is $X_(f_i)$.  The latter is affine by hypothesis.

  + Moreover,
    its pairwise intersections are principal opens in an affine scheme, hence
    affine and in particular quasi-compact.  XL-2(c.ii) therefore gives
    $
      Gamma(X_(f_i), shf.o_X) simeq A_(f_i).
    $

  + Under this isomorphism, the restriction of $psi$ over $D(f_i)$ is the
    affine-scheme morphism induced by the identity of $A_(f_i)$, so it is an
    isomorphism.  XL-7, applied to the cover ${D(f_i)}$ of
    $ops.spec A$, now shows that $psi$ is an isomorphism.  Hence $X$ is
    affine.
]

#proposition(key: "sup-xl-9", title: "Injective affine ring maps")[
  Let $phi:A to B$ be a ring map and $f:ops.spec B to ops.spec A$ its scheme morphism.
  Then
  $
    phi " is injective" & arrow.l.r.double \
                        & shf.o_(ops.spec A) to f_*shf.o_(ops.spec B) " is injective".
  $
]

#proof[

  + Put $X=ops.spec A$. Under the affine pushforward formula, the sheaf map in question is $tildeOf(A)->tildeOf(B)$ induced by the $A$-linear map
    $phi$.

  + If $phi$ is injective, its localization $A_f->B_f$ is injective for every $f in A$ by AL-3. These are the maps on the distinguished basis of $X$; sections on any open are detected on that basis, so the sheaf map is injective.

  + Conversely, an injective sheaf map is injective on every open, in particular on $X$, where it is precisely $phi:A->B$.

]
For II.2.A and II.2.18(a), use the spectrum and localization formulas of
#book-link(<text-ii-2>)[II.2, Lemma 2.1 and Proposition 2.2]. Closed points
are indexed in #supplement-link(<sup-xp-3>)[XP-3], reduced closed structures
in #supplement-link(<sup-cs-4>)[CS-4], and quasi-compact principal opens in
#supplement-link(<sup-xp-10>)[XP-10]. Surjectivity and closed immersions are
in #supplement-link(<sup-cs-1>)[CS-1]; dominance is distinguished from
injectivity in #supplement-link(<sup-xp-6>)[XP-6]. For II.3.1–4, use
#book-link(<sup-lp>)[the locality calculus]. Affine intersections and their
separatedness hypothesis are treated in #supplement-link(<sup-mg-8>)[MG-8].
