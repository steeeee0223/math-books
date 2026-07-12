#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Projective Varieties

#note-box(title: "Notations (Localizations of Graded Rings)")[
  Let $S$ be any graded ring, $f in S$ a homogeneous element, and
  $pp lt.closed S$ a homogeneous prime ideal.

  - We denote $S_f$ as the localization of $S$ on the multiplicatively closed set
    $T_f := { f^n }_(n>=0)$, i.e. $S_f := T_f^(-1) S$.
  - In fact, $S_f$ is a graded $S$-module, with the natural grading
    $deg a/f^n := deg a - n$ (where $a in S^h$).
    We denote $S_((f)) := (S_f)_0$, the degree-$0$ part of $S_f$.
  - Similarly, $S_pp$ has a natural grading structure by
    $deg f/g := deg f - deg g$ (where $f,g in S^h$, with $g in.not pp$).
    We denote $S_((pp)) := (S_pp)_0$.
]

#lemma-box(title: "Fact 2.A")[
  For any graded ring $S$ and any homogeneous element $f in S^h$,
  we have a natural isomorphism:
  $ S_f simeq S_((f))[f,f^(-1)]. $
]

#exercise(
  title: "Exercise 2.1 (Homogeneous Nullstellensatz)",
)[
  If $aa lt.closed S$ is a homogeneous ideal, and $f in S$ is any homogeneous polynomial of positive degree such that $f(P) = 0$ for every $P in Z_+(aa)$ (in $PP^n$), i.e. $f in I_+(Z_+(aa))$, then $f^m in aa$ for some $m > 0$.
]

#proof[
  Change the problem into $AA^(n+1)$ and use the usual *Nullstellensatz*.
]

#exercise(title: "Exercise 2.2")[
  For a homogeneous ideal $aa lt.closed S$, the following are equivalent:

  + $Z_+(aa) = emptyset$
  + $sqrt(aa) = S$ or $S_+$, the *irrelevant* maximal ideal.
  + $aa supset S_d$ for some $d > 0$ (and thus $aa supset S_d$ for all large $d > 0$).
]
