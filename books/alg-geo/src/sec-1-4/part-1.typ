#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne I.4, Lemma 4.1
#lemma(number: "4.1")[
  Let $X,Y$ be varieties and let $phi,psi:X->Y$ be morphisms. If they agree on
  a nonempty open subset $U subset.eq X$, then $phi=psi$.
]


// Hartshorne I.4, Definition D1
#definition(number: none, title: "Rational Map")[
  A *rational map* $phi:X arrow.r.long Y$ is an equivalence class of pairs
  $(U,phi_U)$, where $U subset.eq X$ is nonempty open and $phi_U:U->Y$ is a
  morphism; two pairs are equivalent when their morphisms agree on the
  intersection. It is *dominant* if the image of one, hence every,
  representative is dense in $Y$.
]

// Hartshorne I.4, Definition D2
#definition(number: none, title: "Birational Map")[
  A *birational map* $phi:X arrow.r.long Y$ is a rational map admitting a rational
  inverse. If one exists, $X$ and $Y$ are *birationally equivalent*, or simply
  *birational*.
]

// Hartshorne I.4, Lemma 4.2
#lemma(number: "4.2")[
  Let $Y=Z(f) subset.eq sch.a^n$ be a hypersurface. Then
  $sch.a^n without Y$ is isomorphic to the hypersurface
  $H=Z(x_(n+1) f-1) subset.eq sch.a^(n+1)$. In particular it is affine, with
  coordinate ring $k[x_1,...,x_n]_f$.
]


// Hartshorne I.4, Proposition 4.3
#proposition(number: "4.3")[
  Every variety has a basis for its topology consisting of open affine subsets.
]


// Hartshorne I.4, Theorem 4.4
#theorem(number: "4.4")[
  For varieties $X,Y$, pullback gives a bijection between dominant rational
  maps $X arrow.r.long Y$ and $k$-algebra homomorphisms $K(Y)->K(X)$. This is an
  arrow-reversing equivalence between varieties with dominant rational maps
  and finitely generated field extensions of $k$.
]


// Hartshorne I.4, Corollary 4.5
#corollary(number: "4.5")[
  For varieties $X,Y$, the following are equivalent:

  #set enum(numbering: "(i)", spacing: 0.8em)

  + $X$ and $Y$ are birational.
  + Some nonempty open subsets $U subset.eq X$ and $V subset.eq Y$ are
    isomorphic.
  + $K(X) simeq K(Y)$ as $k$-algebras.
]


// Hartshorne I.4, Theorem 4.6A
#theorem(number: "4.6A", title: "Primitive Element Theorem")[
  If $L\/K$ is finite separable, then $L=K(alpha)$ for some $alpha in L$. If
  $K$ is infinite and $beta_1,...,beta_n$ generate $L\/K$, then $alpha$ may be
  chosen as a $K$-linear combination of the $beta_i$.
]


// Hartshorne I.4, Definition D3
#definition(number: none, title: "Separably Generated Extension")[
  A field extension $K\/k$ is *separably generated* if it has a transcendence
  basis ${x_i}$ such that $K$ is separable algebraic over $k({x_i})$. Such a
  basis is a *separating transcendence basis*.
]

// Hartshorne I.4, Theorem 4.7A
#theorem(number: "4.7A")[
  If $K\/k$ is finitely and separably generated, every generating set contains
  a separating transcendence basis.
]


// Hartshorne I.4, Theorem 4.8A
#theorem(number: "4.8A")[
  If $k$ is perfect, in particular if it is algebraically closed, every
  finitely generated field extension $K\/k$ is separably generated.
]


// Hartshorne I.4, Proposition 4.9
#proposition(number: "4.9")[
  Every variety $X$ of dimension $r$ is birational to a hypersurface in
  $sch.p^(r+1)$.
]


// Hartshorne I.4, Definition D4
#definition(number: none, title: "Blowing Up a Variety at a Point")[
  The blow-up of $sch.a^n$ at $0$ is the closed subvariety
  $X subset.eq sch.a^n times sch.p^(n-1)$ defined by
  $x_i y_j=x_j y_i$, with projection $phi:X->sch.a^n$. If
  $Y subset.eq sch.a^n$ is a closed subvariety through $0$, its *blow-up at* $0$
  is $tildeOf(Y)=overline(phi^(-1) (Y without {0}))$, with the restricted
  morphism $phi:tildeOf(Y)->Y$. A linear change of coordinates defines the
  blow-up at any other point.
]
