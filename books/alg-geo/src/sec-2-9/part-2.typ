#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *

#show: show-theorion

=== Formal Schemes

// Hartshorne II.9, Definition D1
#definition(number: none, title: "Formal Completion of a Scheme")[
  Let $X$ be noetherian and $Y subset.eq X$ closed with ideal sheaf $shf.i$. The
  *formal completion of $X$ along $Y$* is the ringed space
  $hat(X)=(Y,hat(shf.o)_X)$, where
  $hat(shf.o)_X=op("lim") shf.o_X\/shf.i^n$.
]

// Hartshorne II.9, Remark 9.3.1
#remark(title: "9.3.1")[
  The completed structure sheaf depends only on the closed subset underlying
  $Y$, not its scheme structure: two defining ideals have cofinal systems of
  powers on a noetherian scheme.
]

// Hartshorne II.9, Definition D2
#definition(number: none, title: "Completion of a Coherent Sheaf")[
  For coherent $shf.f$ on $X$, its completion along $Y$ is
  $hat(shf.f)=op("lim") shf.f\/shf.i^n shf.f$, naturally an $hat(shf.o)_X$-module.
]

// Hartshorne II.9, Definition D3
#definition(number: none, title: "Noetherian Formal Schemes")[
  A *noetherian formal scheme* is a locally ringed space having a finite open
  cover by formal completions of noetherian schemes along closed subschemes.
  Morphisms are morphisms of locally ringed spaces. An $shf.o$-module is
  *coherent* if locally it is the completion of a coherent sheaf on such a
  model.
]

// Hartshorne II.9, Definition D4
#definition(number: none, title: "Affine Formal Schemes")[
  An affine noetherian formal scheme is the completion of one affine
  noetherian scheme $ops.spec A$ along $V(I)$. For finite $M$, denote the
  completion of $tildeOf(M)$ on it by $M^triangle$.
]

// Hartshorne II.9, Proposition 9.4
#proposition(number: "9.4")[
  Let $X=ops.spec A$, $Y=V(I)$, and $hat(X)$ its completion.

  + $shf.i^triangle$ is an ideal of $shf.o_(hat(X))$ and
    $shf.o_(hat(X))\/(shf.i^triangle)^n simeq (A\/I^n)^triangle$.
  + For finite $M$, $M^triangle simeq tildeOf(M) times.o_(shf.o_X) shf.o_(hat(X))$.
  + $M mapsto M^triangle$ is exact from finite $A$-modules to coherent
    $shf.o_(hat(X))$-modules.
]


// Hartshorne II.9, Definition D5
#definition(number: none, title: "Ideals of Definition")[
  An ideal sheaf $shf.j subset.eq shf.o_(hat(X))$ on a noetherian formal scheme is
  an *ideal of definition* if $ops.supp shf.o_(hat(X))\/shf.j=hat(X)$ and
  $(hat(X),shf.o_(hat(X))\/shf.j)$ is a noetherian scheme.
]

// Hartshorne II.9, Proposition 9.5
#proposition(number: "9.5")[
  On a noetherian formal scheme:

  + any two ideals of definition contain powers of one another;
  + there is a unique largest ideal of definition, characterized by having a
    reduced quotient; and
  + every positive power of an ideal of definition is again one.
]


// Hartshorne II.9, Proposition 9.6
#proposition(number: "9.6")[
  Let $shf.j$ be an ideal of definition and
  $Y_n=(hat(X),shf.o_(hat(X))\/shf.j^n)$.

  + For coherent $shf.f$, each $shf.f_n=shf.f\/shf.j^n shf.f$ is coherent on $Y_n$, and
    $shf.f simeq op("lim") shf.f_n$.
  + Conversely, a system of coherent $shf.f_n$ with surjective transitions and
    kernels $shf.j^n shf.f_(n')$ has coherent limit $shf.f$, with
    $shf.f_n simeq shf.f\/shf.j^n shf.f$.
]


// Hartshorne II.9, Theorem 9.7
#theorem(number: "9.7")[
  Let $A$ be noetherian and complete for the $I$-adic topology. On the formal
  completion of $ops.spec A$ along $V(I)$, the exact functors
  $M mapsto M^triangle$ and $shf.f mapsto Gamma(hat(X), shf.f)$ are inverse
  equivalences between finite $A$-modules and coherent
  $shf.o_(hat(X))$-modules.
]


// Hartshorne II.9, Corollary 9.8
#corollary(number: "9.8")[
  Completion along a closed subscheme of a noetherian scheme is exact on
  coherent sheaves. If $shf.i$ defines the subscheme, then
  $hat(shf.f)\/(hat(shf.i))^n hat(shf.f) simeq (shf.f\/shf.i^n shf.f)^triangle$ and
  $hat(shf.f) simeq shf.f times.o_(shf.o_X) hat(shf.o)_X$.
]


// Hartshorne II.9, Corollary 9.9
#corollary(number: "9.9")[
  Kernels, cokernels, and images of morphisms of coherent sheaves on a
  noetherian formal scheme are coherent.
]


// Hartshorne II.9, Remark 9.9.1
#remark(title: "9.9.1")[
  Extensions of coherent sheaves are coherent as well. Some familiar global
  generation statements fail for formal schemes: nonzero coherent sheaves
  may have no global sections after any twist.
]
