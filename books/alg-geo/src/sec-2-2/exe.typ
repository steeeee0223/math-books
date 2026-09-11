#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.2, Exercise 2.1
#exercise(title: "Exercise 2.1")[
  For $X=ops.spec A$ and $f in A$, show
  $(D(f),shf.o_X|_(D(f))) simeq ops.spec A_f$.
]

#proof[
  The map $A->A_f$ induces
  $pi:ops.spec A_f->ops.spec A$.  Extension and contraction give inverse
  bijections
  $
    {q in ops.spec A_f} arrow.l.r {p in ops.spec A : f in.not p},
  $
  because the prime ideals of a localization are exactly the primes disjoint
  from the localized multiplicative set ${1,f,f^2,dots}$.  Thus $pi$ is a
  homeomorphism from $ops.spec A_f$ onto $D(f)$.

  This homeomorphism also identifies the structure sheaves.  The principal
  opens $D(g) subset.eq D(f)$ form a basis, and on such an open the two rings
  of sections are
  $
    shf.o_(ops.spec A)(D(f g))=A_(f g)
    quad "and" quad
    shf.o_(ops.spec A_f)(D(g/1))=(A_f)_(g/1).
  $
  The canonical localization map identifies these rings, compatibly with
  restriction.  A morphism of sheaves which is an isomorphism on a basis is
  an isomorphism, so $pi$ yields the required isomorphism of schemes.

  This is exactly mathlib's `basicOpenIsoSpecAway`, used directly in the Lean
  companion.
]

// Hartshorne II.2, Exercise 2.2
#exercise(title: "Exercise 2.2")[
  If $U subset.eq X$ is open in a scheme, show $(U,shf.o_X|_U)$ is a scheme.
  It is the *open subscheme* induced on $U$.
]

#proof[
  Let $x in U$.  Choose an affine neighborhood
  $V=ops.spec A subset.eq X$ of $x$.  The intersection $U inter V$ is open in
  $ops.spec A$, and principal opens form a basis of its topology, so there is
  some $f in A$ with
  $
    x in D(f) subset.eq U inter V.
  $
  By Exercise 2.1, with its restricted structure sheaf this neighborhood is
  $ops.spec A_f$.  Hence every point of $(U,shf.o_X|_U)$ has an affine open
  neighborhood, which is the definition of a scheme.

  In mathlib an open `U : X.Opens` coerces directly to a scheme, and its
  canonical map `U.ι : U ⟶ X` is an open immersion; the Lean companion checks
  both declarations.
]

// Hartshorne II.2, Exercise 2.3
#exercise(title: "Exercise 2.3 (Reduced Schemes)")[
  A scheme is reduced if every $shf.o_X (U)$ has no nonzero nilpotents.

  + Show this is equivalent to every local ring $shf.o_(X,P)$ being reduced.
  + Sheafify $U mapsto shf.o_X (U)_(red)$; show the result defines a scheme
    $X_(red)$ and a morphism $X_(red)->X$ that is a homeomorphism on spaces.
  + If $X$ is reduced, show every $X->Y$ factors uniquely through
    $Y_(red)->Y$.
]

#proof[
  + Suppose first that every $shf.o_(X,x)$ is reduced.  If
    $s in shf.o_X (U)$ is nilpotent, then every germ $s_x$ is nilpotent and
    hence zero.  A section whose germs are all zero is zero, so
    $shf.o_X (U)$ is reduced.

    Conversely, assume every $shf.o_X (U)$ is reduced.  Let a germ
    $a in shf.o_(X,x)$ be nilpotent.  Represent it by
    $s in shf.o_X (U)$.  The equality $a^n=0$ means that after shrinking to
    some neighborhood $V$ of $x$, one has $(s|_V)^n=0$.  Reducedness of
    $shf.o_X (V)$ gives $s|_V=0$, hence $a=0$.  Thus every local ring is
    reduced.

  + Let $cal(N) subset.eq shf.o_X$ be the sheaf of nilpotent sections; it is
    the nilradical ideal sheaf.  Define
    $
      X_(red)=(X,shf.o_X\/cal(N)).
    $
    Equivalently, this quotient sheaf is the sheafification of
    $U mapsto shf.o_X (U)_(red)$.  On an affine open
    $V=ops.spec A$, its restriction is the structure sheaf of
    $ops.spec(A\/sqrt((0)))$.  Hence these affine reductions glue and make
    $X_(red)$ a scheme.  The quotient maps define a closed immersion
    $i:X_(red)->X$.

    Every prime ideal of $A$ contains $sqrt((0))$, so contraction gives a
    homeomorphism
    $ops.spec(A\/sqrt((0))) simeq ops.spec A$.  These local homeomorphisms
    agree, and therefore $i$ is a homeomorphism on underlying spaces.
    Finally, $A\/sqrt((0))$ is reduced on every affine chart, so part (a)
    shows that $X_(red)$ is reduced.

  + Let $f:X->Y$ with $X$ reduced.  Nilpotent local sections of $shf.o_Y$
    pull back to nilpotent sections of $shf.o_X$, hence to zero.  Thus
    $f^sharp$ kills the nilradical ideal sheaf of $Y$ and factors through
    $shf.o_Y\/cal(N)_Y$.  This gives a morphism
    $tilde(f):X->Y_(red)$ with $i compose tilde(f)=f$.  It is unique because
    $i$ is a closed immersion, hence a monomorphism.

  Mathlib already has the nilradical ideal sheaf and its associated
  subscheme.  The Lean companion defines `reduction` from them and verifies
  reducedness, the underlying homeomorphism, and the unique factorization.
]

// Hartshorne II.2, Exercise 2.4
#exercise(title: "Exercise 2.4")[
  Show that taking global sections gives a natural bijection
  $ops.hom(X, ops.spec A, over: cat.sch) simeq
  ops.hom(A, Gamma(X, shf.o_X), over: cat.ring)$.
]

#proof[
  A scheme morphism $f:X->ops.spec A$ induces on global sections a ring map
  $
    A simeq Gamma(ops.spec A, shf.o) ->^(f^sharp)
    Gamma(X, shf.o_X).
  $
  This defines the map from left to right.

  Conversely, let $phi:A->Gamma(X, shf.o_X)$.  For each affine open
  $U=ops.spec B subset.eq X$, restriction gives a ring map
  $A->Gamma(U, shf.o_U) simeq B$, hence a scheme morphism
  $U->ops.spec A$.  On overlaps these morphisms induce the same maps on all
  sections, because both arise by restricting $phi$.  They therefore glue
  to a morphism $X->ops.spec A$.

  On an affine open, the two constructions are inverse by the contravariant
  equivalence between rings and affine schemes.  Since affine opens cover
  $X$, they are inverse globally.  Every step commutes with precomposition in
  $X$ and with ring maps in $A$, so the bijection is natural.

  Mathlib packages precisely this bijection as the hom-set equivalence of
  `ΓSpec.adjunction`; the Lean companion specializes that equivalence to the
  displayed statement.
]

// Hartshorne II.2, Exercise 2.5
#exercise(title: "Exercise 2.5")[
  Describe $ops.spec ZZ$ and show it is a final object in the category of
  schemes.
]

// Hartshorne II.2, Exercise 2.6
#exercise(title: "Exercise 2.6")[
  Describe the spectrum of the zero ring and show it is an initial object in
  the category of schemes.
]

// Hartshorne II.2, Exercise 2.7
#exercise(title: "Exercise 2.7 (Residue Fields)")[
  For $x in X$, put $kappa(x)=shf.o_(X,x)\/idl.m_x$. Show that a morphism
  $ops.spec K->X$, for a field $K$, is equivalent to a point $x in X$ together
  with an inclusion $kappa(x)->K$.
]

// Hartshorne II.2, Exercise 2.8
#exercise(title: "Exercise 2.8 (Zariski Tangent Space)")[
  Define $T_x X$ as the dual of $idl.m_x\/idl.m_x^2$ over $kappa(x)$. If $X$ is
  over $k$, show that $k$-morphisms $ops.spec k[epsilon]\/(epsilon^2)->X$ are
  equivalent to pairs consisting of a $k$-rational point $x$ and an element
  of $T_x X$.
]

// Hartshorne II.2, Exercise 2.9
#exercise(title: "Exercise 2.9 (Generic Points)")[
  A generic point of an irreducible closed subset $Z$ is a point $zeta$ with
  $Z=overline({zeta})$. Show every nonempty irreducible closed subset of a
  scheme has a unique generic point.
]

// Hartshorne II.2, Exercise 2.10
#exercise(title: "Exercise 2.10")[
  Describe $ops.spec RR[x]$. How does its topological space compare with
  $RR$ and with $CC$?
]

// Hartshorne II.2, Exercise 2.11
#exercise(title: "Exercise 2.11")[
  For $k=shf.f_p$, describe $ops.spec k[x]$, determine the residue fields of its
  points, and count the points having each given residue field.
]

// Hartshorne II.2, Exercise 2.12
#exercise(title: "Exercise 2.12 (Glueing Lemma)")[
  Let schemes $X_i$ have open subschemes $U_(i j)$ and isomorphisms
  $phi_(i j):U_(i j)->U_(j i)$ with $phi_(j i)=phi_(i j)^(-1)$ and the
  usual cocycle compatibility on triple overlaps. Show that the $X_i$ glue
  to a scheme $X$ in which each $X_i$ is open and the prescribed overlaps
  are identified. Include the special case of the disjoint union.
]

#proof[
  Form the disjoint union of the underlying spaces and impose the equivalence
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
  $q_i:X_i->X$ are open embeddings.  Their images cover $X$, and
  $q_i(X_i) inter q_j(X_j)$ is the common image of $U_(i j)$ and $U_(j i)$.

  Define the structure sheaf by compatible families:
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

  Since the images $q_i(X_i)$ are open and each is a scheme, every point of
  $(X,shf.o_X)$ has an affine neighborhood.  Thus it is a scheme.  The same
  compatible-family description shows the universal property: compatible
  morphisms out of the $X_i$ glue uniquely.  Consequently any two schemes
  obtained from the data are uniquely isomorphic in a way compatible with
  all $q_i$.

  For the disjoint union take $U_(i j)=emptyset$ when $i != j$ and
  $U_(i i)=X_i$.  There are then no cross-component compatibility conditions,
  so the construction is the ordinary topological disjoint union with
  componentwise structure sheaf.

  Mathlib formalizes the entire construction as `Scheme.GlueData.glued`.
  It proves that the component maps are open immersions, jointly surjective,
  and have the prescribed overlaps as pullbacks; the Lean companion checks
  those interfaces.
]

// Hartshorne II.2, Exercise 2.13
#exercise(title: "Exercise 2.13 (Quasi-compactness)")[
  + Show a space is noetherian iff every open subset is quasi-compact.
  + Show every affine scheme is quasi-compact but need not be noetherian.
  + If $A$ is noetherian, show $ops.sp (ops.spec A)$ is noetherian.
  + Give an example where $ops.sp (ops.spec A)$ is noetherian but $A$ is not.
]

// Hartshorne II.2, Exercise 2.14
#exercise(title: "Exercise 2.14")[
  + Show $ops.proj S=emptyset$ iff every element of $S_+$ is nilpotent.
  + For a graded map $phi:S->T$, let
    $U=ops.proj T - V(phi(S_+))$. Show $U$ is open and
    $phi$ induces $U->ops.proj S$.
  + If $S_d->T_d$ is an isomorphism for all sufficiently large $d$, show
    $U=ops.proj T$ and $ops.proj T->ops.proj S$ is an isomorphism.
  + For a projective variety $V$ with homogeneous coordinate ring $S$, show
    $t(V) simeq ops.proj S$.
]

// Hartshorne II.2, Exercise 2.15
#exercise(title: "Exercise 2.15")[
  + For a variety $V in cat.var(k)$, show $P in t(V)$ is closed iff $kappa(P)=k$.
  + A $k$-morphism of schemes sends points with residue field $k$ to such
    points.
  + Deduce that the natural map
    $ops.hom(V, W, over: cat.var(k))->
    ops.hom(t(V), t(W), over: cat.sch(k))$ is bijective.
]

// Hartshorne II.2, Exercise 2.16
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

  + Choose a finite affine cover $X=union_(i=1)^r U_i$, possible because $X$
    is quasi-compact.  Put $A_i=Gamma(U_i, shf.o_X)$ and let $f_i,a_i$ be the
    restrictions of $f,a$.  On the affine scheme $U_i$ the hypothesis says
    that $a_i/1=0$ in $(A_i)_(f_i)$.  Hence
    $f_i^(n_i)a_i=0$ for some $n_i$.  Taking
    $n=max_i n_i$ gives $(f^n a)|_(U_i)=0$ for every $i$.  A section which
    vanishes on an open cover is zero, so $f^n a=0$ on $X$.

  + Let $X=union_(i=1)^r U_i$ be the given affine cover and set
    $U_(i j)=U_i inter U_j$.  On
    $(U_i)_f=D(f_i)$, Exercise 2.1 identifies $b$ with an element of
    $(A_i)_(f_i)$.  After choosing a common exponent $n$, write
    $
      f_i^n b=a_i|_((U_i)_f)
      quad "for some" quad a_i in A_i.
    $
    On $U_(i j)$ the difference $a_i-a_j$ vanishes after restriction to
    $(U_(i j))_f$.  Each $U_(i j)$ is quasi-compact, so part (b), applied on
    that open subscheme, gives an exponent $m_(i j)$ such that
    $f^(m_(i j))(a_i-a_j)=0$ on $U_(i j)$.  There are only finitely many
    pairs.  Choose one $m$ dominating all $m_(i j)$ and replace every $a_i$
    by $f^m a_i$.  The new $a_i$ agree on all overlaps and therefore glue to
    $a in A$.  On $X_f$ they satisfy
    $f^(n+m)b=a|_(X_f)$.

  + Restriction gives a ring homomorphism
    $
      theta:A_f->Gamma(X_f, shf.o).
    $
    Part (c) says it is surjective.  If $theta(a/f^r)=0$, then
    $a|_(X_f)=0$; by part (b), $f^n a=0$ for some $n$, which is exactly the
    criterion for $a/f^r=0$ in $A_f$.  Thus $theta$ is also injective and is
    the required isomorphism.

  A finite affine cover makes $X$ quasi-compact, and quasi-compact pairwise
  intersections make it quasi-separated.  Mathlib's
  `isLocalization_basicOpen_of_qcqs` states part (d) in this equivalent qcqs
  form.  The Lean companion also checks the open-intersection identity,
  the power-clearing assertion of part (b), and the numerator assertion of
  part (c).
]

// Hartshorne II.2, Exercise 2.17
#exercise(title: "Exercise 2.17 (A Criterion for Affineness)")[
  + If $f:X->Y$ is locally an isomorphism over an open cover of $Y$, show
    $f$ is an isomorphism.
  + Show $X$ is affine iff finitely many $f_i in A=Gamma(X, shf.o_X)$ generate
    the unit ideal and every $X_(f_i)$ is affine.
]

#proof[
  + Let ${U_i}$ be an open cover of $Y$ such that each base change
    $f_i:f^(-1)(U_i)->U_i$ is an isomorphism.  Write
    $g_i:U_i->X$ for the composite of $f_i^(-1)$ with the inclusion
    $f^(-1)(U_i)->X$.  On $U_i inter U_j$, both $g_i$ and $g_j$ are inverse to
    the same restriction of $f$, so they agree.  The gluing lemma for
    morphisms gives $g:Y->X$.

    On every $U_i$ one has $(f compose g)|_(U_i)=ops.id$, hence
    $f compose g=ops.id_Y$.  On every $f^(-1)(U_i)$ one similarly has
    $(g compose f)|_(f^(-1)(U_i))=ops.id$, and these opens cover $X$; hence
    $g compose f=ops.id_X$.  Thus $f$ is an isomorphism.

  + If $X$ is affine, take the single section $f_1=1$.  It generates the unit
    ideal, $X_(f_1)=X$, and this open is affine.

    Conversely, suppose $f_1,dots,f_r$ generate $A$.  Then the opens
    $X_(f_i)$ cover $X$: at every point some $(f_i)_x$ must be a unit, since a
    linear combination of the $f_i$ is $1$.  The principal opens
    $D(f_i)$ likewise cover $ops.spec A$.

    Consider the canonical morphism
    $
      psi:X->ops.spec A
    $
    corresponding under Exercise 2.4 to $ops.id_A$.  Its inverse image of
    $D(f_i)$ is $X_(f_i)$.  The latter is affine by hypothesis.  Moreover,
    its pairwise intersections are principal opens in an affine scheme, hence
    affine and in particular quasi-compact.  Exercise 2.16(d) therefore gives
    $
      Gamma(X_(f_i), shf.o_X) simeq A_(f_i).
    $
    Under this isomorphism the restriction of $psi$ over $D(f_i)$ is the
    affine-scheme morphism induced by the identity of $A_(f_i)$, so it is an
    isomorphism.  Part (a), applied to the cover ${D(f_i)}$ of
    $ops.spec A$, now shows that $psi$ is an isomorphism.  Hence $X$ is
    affine.

  Mathlib records part (a) by making isomorphisms Zariski-local on the target,
  and records the converse direction of part (b) as
  `isAffine_of_isAffineOpen_basicOpen`.  The Lean companion combines the
  latter with the one-element cover ${1}$ to check the stated equivalence.
]

// Hartshorne II.2, Exercise 2.18
#exercise(title: "Exercise 2.18")[
  Let $phi:A->B$ induce $f:ops.spec B->ops.spec A$.

  + Show $a in A$ is nilpotent iff $D(a)=emptyset$.
  + Show $phi$ is injective iff $f^sharp:shf.o_X->f_*shf.o_Y$ is injective, and then
    $f$ is dominant.
  + If $phi$ is surjective, show $f$ is a homeomorphism onto a closed subset
    and $f^sharp$ is surjective.
  + Prove the converse to the preceding assertion.
]

// Hartshorne II.2, Exercise 2.19
#exercise(title: "Exercise 2.19")[
  Show the following are equivalent:

  + $ops.spec A$ is disconnected;
  + there are nonzero orthogonal idempotents $e_1,e_2$ with $e_1+e_2=1$;
  + $A simeq A_1 times A_2$ for two nonzero rings.
]

#exercise(title: "Exercise 2.A (Supplementary)")[
  For $X=ops.spec A$ and $f in A$, verify:

  + $D(f)$ is empty exactly when $f$ is nilpotent
  + $D(f)=X$ exactly when $f$ is a unit
  + $X$ is empty exactly when $A$ is the zero ring
  + closed subsets correspond contravariantly to radical ideals
  + every $D(f)$ is quasi-compact
  + the closed points of $X$ are precisely the maximal ideals.
]
