#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.2, Exercise 2.1
#exercise(title: "Exercise 2.1")[
  For $X=ops.spec A$ and $f in A$, show
  $(D(f),shf.o_X|_(D(f))) simeq ops.spec A_f$.
]

// Hartshorne II.2, Exercise 2.2
#exercise(title: "Exercise 2.2")[
  If $U subset.eq X$ is open in a scheme, show $(U,shf.o_X|_U)$ is a scheme.
  It is the *open subscheme* induced on $U$.
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

// Hartshorne II.2, Exercise 2.4
#exercise(title: "Exercise 2.4")[
  Show that taking global sections gives a natural bijection
  $ops.hom(X, ops.spec A, over: cat.sch) simeq
  ops.hom(A, Gamma(X, shf.o_X), over: cat.ring)$.
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

// Hartshorne II.2, Exercise 2.17
#exercise(title: "Exercise 2.17 (A Criterion for Affineness)")[
  + If $f:X->Y$ is locally an isomorphism over an open cover of $Y$, show
    $f$ is an isomorphism.
  + Show $X$ is affine iff finitely many $f_i in A=Gamma(X, shf.o_X)$ generate
    the unit ideal and every $X_(f_i)$ is affine.
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
