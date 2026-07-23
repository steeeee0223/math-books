#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Exercises

// Hartshorne I.4, Exercise 4.1
#exercise(title: "Exercise 4.1")[
  If regular functions $f$ on $U$ and $g$ on $V$ agree on $U inter V$, show
  that they glue to a regular function on $U union V$. Deduce that every
  rational function on $X$ has a largest open subset on which it is regular.
]

// Hartshorne I.4, Exercise 4.2
#exercise(title: "Exercise 4.2")[
  Prove the analogous statement for rational maps: every rational map
  $X arrow.r.long Y$ has a largest open subset on which it is represented by a
  morphism.
]

// Hartshorne I.4, Exercise 4.3
#exercise(title: "Exercise 4.3")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + For the rational function $f=x_1/x_0$ on $sch.p^2$, find its domain of
    definition and describe the regular function there.
  + Regard $f$ as a rational map $sch.p^2 arrow.r.long sch.a^1 subset.eq sch.p^1$. Find
    its domain of definition and describe the corresponding morphism.
]

// Hartshorne I.4, Exercise 4.4
#exercise(title: "Exercise 4.4 (Rational Varieties)")[
  A variety is *rational* if it is birational to some $sch.p^n$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that every conic in $sch.p^2$ is a rational curve.
  + Show that the cuspidal cubic $y^2=x^3$ is rational.
  + Let $Y$ be the nodal cubic $y^2 z=x^2 (x+z)$ in $sch.p^2$. Show that
    projection from $P=(0:0:1)$ to $z=0$ is birational from $Y$ to $sch.p^1$.
]

// Hartshorne I.4, Exercise 4.5
#exercise(title: "Exercise 4.5")[
  Show that the quadric surface $Q:x y=z w$ in $sch.p^3$ is birational to $sch.p^2$
  but not isomorphic to it.
]

// Hartshorne I.4, Exercise 4.6
#exercise(title: "Exercise 4.6 (Plane Cremona Transformations)")[
  Consider the rational map $phi:sch.p^2 arrow.r.long sch.p^2$ given by
  $(a_0:a_1:a_2) mapsto (a_1 a_2:a_0 a_2:a_0 a_1)$ when no two coordinates
  vanish.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $phi$ is birational and is its own inverse.
  + Find open sets $U,V subset.eq sch.p^2$ for which $phi:U->V$ is an isomorphism.
  + Find the largest domains of definition of $phi$ and $phi^(-1)$ and
    describe the corresponding morphisms.
]

// Hartshorne I.4, Exercise 4.7
#exercise(title: "Exercise 4.7")[
  Suppose $P in X$, $Q in Y$, and $shf.o_(P,X) simeq shf.o_(Q,Y)$ as $k$-algebras.
  Show that there are open neighborhoods $P in U subset.eq X$ and
  $Q in V subset.eq Y$ and an isomorphism $U->V$ sending $P$ to $Q$.
]

// Hartshorne I.4, Exercise 4.8
#exercise(title: "Exercise 4.8")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that every positive-dimensional variety over $k$ has the same
    cardinality as $k$.
  + Deduce that any two curves over $k$ are homeomorphic.
]

// Hartshorne I.4, Exercise 4.9
#exercise(title: "Exercise 4.9")[
  Let $X subset.eq sch.p^n$ be projective of dimension $r$, with $n>=r+2$.
  Show that for suitable $P in.not X$ and a linear $sch.p^(n-1) subset.eq sch.p^n$,
  projection from $P$ induces a birational morphism of $X$ onto its image in
  $sch.p^(n-1)$. Use Theorems 4.6A–4.8A.
]

// Hartshorne I.4, Exercise 4.10
#exercise(title: "Exercise 4.10")[
  Let $Y:y^2=x^3$ be the cuspidal cubic in $sch.a^2$. Blow up $0$, let $E$ be
  the exceptional curve, and let $tildeOf(Y)$ be the strict transform. Show
  that $E$ meets $tildeOf(Y)$ in one point and $tildeOf(Y) simeq sch.a^1$. The
  morphism $tildeOf(Y)->Y$ is bijective and bicontinuous but not an
  isomorphism.
]
