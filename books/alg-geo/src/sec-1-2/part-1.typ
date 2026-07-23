#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne I.2, Definition D1
#definition(number: none, title: "Projective Algebraic Set")[
  Let $S = k[x_0, ..., x_n]$. A subset $Y$ of $sch.p^n$ is an *algebraic set* if
  there is a set $T$ of homogeneous elements of $S$ such that
  $Y = Z(T)$.
]

// Hartshorne I.2, Proposition 2.1
#proposition(number: "2.1")[
  The union of two algebraic sets is an algebraic set. The intersection of any
  family of algebraic sets is an algebraic set. The empty set and the whole
  space are algebraic sets.
]


// Hartshorne I.2, Definition D2
#definition(number: none, title: "Zariski Topology on Projective Space")[
  The *Zariski topology* on $sch.p^n$ is the topology whose open subsets are the
  complements of algebraic sets.
]

// Hartshorne I.2, Definition D3
#definition(number: none, title: "Projective and Quasi-projective Varieties")[
  A *projective algebraic variety* (or simply a *projective variety*) is an
  irreducible algebraic set in $sch.p^n$, with the induced topology. An open
  subset of a projective variety is a *quasi-projective variety*. Their
  dimensions are their dimensions as topological spaces.
]

// Hartshorne I.2, Proposition 2.2
#proposition(number: "2.2")[
  Let $H_i = Z(x_i)$, $U_i = sch.p^n without H_i$, and define
  $phi_i: U_i -> sch.a^n$ by
  $phi_i (a_0:...:a_n) = (a_0/a_i, ..., hat(a_i/a_i), ..., a_n/a_i)$.
  Then $phi_i$ is a homeomorphism from $U_i$, with its induced topology, to
  $sch.a^n$ with its Zariski topology.
]


// Hartshorne I.2, Corollary 2.3
#corollary(number: "2.3")[
  If $Y$ is a projective (respectively quasi-projective) variety, then the
  open sets $Y inter U_i$, for $i = 0, ..., n$, cover $Y$ and are
  homeomorphic under $phi_i$ to affine (respectively quasi-affine) varieties.
]

#note-box(title: "Notations (Localizations of Graded Rings)")[
  Let $S$ be any graded ring, $f in S$ a homogeneous element, and
  $idl.p lt.closed S$ a homogeneous prime ideal.

  - We denote $S_f$ as the localization of $S$ on the multiplicatively closed set
    $T_f := { f^n }_(n>=0)$, i.e. $S_f := T_f^(-1) S$.
  - In fact, $S_f$ is a graded $S$-module, with the natural grading
    $deg a/f^n := deg a - n$ (where $a in S^h$).
    We denote $S_((f)) := (S_f)_0$, the degree-$0$ part of $S_f$.
  - Similarly, $S_idl.p$ has a natural grading structure by
    $deg f/g := deg f - deg g$ (where $f,g in S^h$, with $g in.not idl.p$).
    We denote $S_((idl.p)) := (S_idl.p)_0$.
]

#lemma-box(title: "Fact 2.A")[
  For any graded ring $S$ and any homogeneous element $f in S^h$,
  we have a natural isomorphism:
  $ S_f simeq S_((f))[f,f^(-1)]. $
]
