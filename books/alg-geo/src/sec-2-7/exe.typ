#import "@preview/theorion:0.4.0": *
#show: show-theorion
#import "../defs.typ": *

=== Exercises

// Hartshorne II.7, Exercise 7.1
#exercise(title: "Exercise 7.1")[
  Let $(X, shf.o_X)$ be a locally ringed space. Show that every surjective map
  $shf.l -> shf.m$ of invertible sheaves is an isomorphism. (Reduce to modules over
  the local rings at the stalks.)
]

// Hartshorne II.7, Exercise 7.2
#exercise(title: "Exercise 7.2")[
  Let $shf.l$ be invertible on a $k$-scheme $X$. Suppose two everywhere-generating
  sets $s_0,dots.c,s_n$ and $t_0,dots.c,t_m$ span the same subspace of
  $Gamma(X, shf.l)$, with $n <= m$. Show that their morphisms to $sch.p_k^n$ and
  $sch.p_k^m$ differ by an automorphism of $sch.p_k^n$ and a linear projection
  $sch.p_k^m - L -> sch.p_k^n$, where $dim L=m-n-1$.
]

// Hartshorne II.7, Exercise 7.3
#exercise(title: "Exercise 7.3")[
  Let $phi:sch.p_k^n -> sch.p_k^m$ be a morphism.

  + Show that either $phi(sch.p^n)$ is a point, or $m >= n$ and
    $dim phi(sch.p^n)=n$.
  + In the latter case show that, for a uniquely determined $d >= 1$, $phi$
    is the composite of the $d$-uple embedding, a linear projection, and an
    automorphism of $sch.p^m$. Show also that $phi$ has finite fibres.
]

// Hartshorne II.7, Exercise 7.4
#exercise(title: "Exercise 7.4")[
  + Use Theorem 7.6 to show that a finite-type scheme over a noetherian ring
    which admits an ample invertible sheaf is separated.
  + For the affine line with doubled origin, calculate $ops.pic X$, determine the
    globally generated invertible sheaves, and prove directly that none is
    ample.
]

// Hartshorne II.7, Exercise 7.5
#metadata(none) <exercise-ii-7-5>
#exercise(title: "Exercise 7.5")[
  Let $X$ be noetherian and $shf.l,shf.m$ invertible. Prove:

  + if $shf.l$ is ample and $shf.m$ globally generated, then $shf.l times.o shf.m$ is ample;
  + if $shf.l$ is ample, then $shf.m times.o shf.l^n$ is ample for all sufficiently
    large $n$;
  + the tensor product of two ample sheaves is ample;
  + if $X$ is of finite type over a noetherian ring, $shf.l$ is very ample, and
    $shf.m$ is globally generated, then $shf.l times.o shf.m$ is very ample;
  + under the same finiteness hypothesis, if $shf.l$ is ample, then $shf.l^n$ is
    very ample for every sufficiently large $n$.
]

#book-link(<sup-pm-4>)[PM-4] uses the very-ample tensor construction for a difference of very ample bundles; it is an application, not a solution of all five assertions.

// Hartshorne II.7, Exercise 7.6
#exercise(title: "Exercise 7.6 (The Riemann–Roch Problem)")[
  Let $X$ be a nonsingular projective variety over an algebraically closed
  field and $D$ a divisor.

  + If $D$ is very ample and $X subset.eq sch.p^N$ is its embedding, show that
    $dim |n D|=P_X (n)-1$ for all sufficiently large $n$.
  + If the class of $D$ has order $r$ in $ops.pic X$, show that $dim |n D|=0$ when
    $r$ divides $n$, and is $-1$ otherwise.
]

// Hartshorne II.7, Exercise 7.7
#exercise(title: "Exercise 7.7 (Some Rational Surfaces)")[
  Put $X=sch.p_k^2$ and let $|D|$ be the complete system of conics.

  + Show that $|D|$ embeds $X$ in $sch.p^5$ as the Veronese surface.
  + Show that $x^2,y^2,z^2,y(x-z),(x-y)z$ give a closed immersion into
    $sch.p^4$.
  + For the system of conics through a fixed point $P$, show that the induced
    map embeds $X-P$ in $sch.p^4$ and extends after blowing up $P$ to a closed
    immersion. Show that its image is a cubic ruled surface and that the
    transformed lines through $P$ are pairwise disjoint lines.
]

// Hartshorne II.7, Exercise 7.8
#exercise(title: "Exercise 7.8")[
  For a locally free coherent sheaf $shf.e$ on a noetherian scheme $X$, show
  that sections of $pi:sch.p (shf.e)->X$ correspond naturally and bijectively to
  invertible quotient sheaves $shf.e -> shf.l -> 0$.
]

// Hartshorne II.7, Exercise 7.9
#exercise(title: "Exercise 7.9")[
  Let $X$ be regular noetherian and let $shf.e$ be locally free of rank at least
  two.

  + Show that $ops.pic sch.p (shf.e) simeq ops.pic X times ZZ$.
  + For another locally free $shf.e'$, show that $sch.p (shf.e) simeq sch.p (shf.e')$ over $X$
    iff $shf.e' simeq shf.e times.o shf.l$ for some invertible $shf.l$ on $X$.
]

// Hartshorne II.7, Exercise 7.10
#metadata(none) <exercise-ii-7-10>
#exercise(title: "Exercise 7.10 ($PP^n$-Bundles)")[
  + Define a projective $n$-space bundle over a noetherian scheme $X$ using
    local products $U times sch.p^n$ and linear transition automorphisms.
  + Show that $sch.p (shf.e)$ is such a bundle when $shf.e$ is locally free of rank
    $n+1$.
  + If $X$ is regular, prove that every $sch.p^n$-bundle is $sch.p (shf.e)$ for some
    locally free $shf.e$, and investigate how far regularity can be weakened.
  + Deduce that, for regular $X$, these bundles correspond to rank $n+1$
    locally free sheaves modulo $shf.e equiv shf.e times.o shf.l$ with $shf.l$ invertible.
]

#book-link(<sup-pj2-6>)[PJ2-6] explains twisting and the specified quotient convention; PJ2-7 supplies the ruled-surface transitions. The converse classification of all projective-space bundles is not asserted there.

// Hartshorne II.7, Exercise 7.11
#metadata(none) <exercise-ii-7-11>
#exercise(title: "Exercise 7.11")[
  Let $X$ be noetherian.

  + Show that blowing up $shf.i^d$ gives the same scheme as blowing up $shf.i$.
  + Show that $shf.j$ and $shf.j dot shf.l$, where $shf.l$ is an invertible ideal sheaf,
    give isomorphic blowups.
  + If $X$ is regular, strengthen Theorem 7.17: for the largest open $U$ on
    which $f$ is an isomorphism, choose the center with support $X-U$.
]

#book-link(<sup-bu-2>)[BU-2] provides the saturated Rees charts, with Veronese and twisting tools in PJ2. These are inputs to this exercise, not a proof of its final assertion.

// Hartshorne II.7, Exercise 7.12
#exercise(title: "Exercise 7.12")[
  Let $Y,Z$ be closed subschemes of a noetherian scheme $X$, neither
  containing the other. Blow up their intersection, defined by
  $shf.i_Y+shf.i_Z$. Show that the strict transforms of $Y$ and $Z$ are disjoint.
]

// Hartshorne II.7, Exercise 7.13
#metadata(none) <exercise-ii-7-13>
#exercise(title: "Exercise 7.13 (A Complete Nonprojective Variety)")[
  Let $k$ be algebraically closed of characteristic not $2$, and let
  $C subset.eq sch.p_k^2$ be the nodal cubic $y^2 z=x^3+x^2z$. Glue two copies
  of $C times sch.a^1$ over $C times shf.g_m$ by
  $(P,u) mapsto (u dot P,u)$, where multiplication by $u$ is translation on
  $C-{P_0} simeq shf.g_m$. Call the resulting scheme $X$, with $pi:X->sch.p^1$.

  + Show that $pi$ is proper, hence $X$ is complete.
  + Compute $ops.pic (C times sch.a^1) simeq shf.g_m times ZZ$ and
    $ops.pic (C times shf.g_m) simeq shf.g_m times ZZ times ZZ$.
  + Show that restriction has the form $(t,n) mapsto (t,0,n)$ and that the
    gluing automorphism acts by $(t,d,n) mapsto (t,d+n,n)$.
  + Deduce that every class in the image of $ops.pic X -> ops.pic (C times {0})$ has
    degree zero. Conclude that $X$ is not projective and $pi$ is not
    projective.
]

#book-link(<sup-lp-57>)[LP-57] gives the nodal gluing construction, both Picard computations, and the degree obstruction.

// Hartshorne II.7, Exercise 7.14
#exercise(title: "Exercise 7.14")[
  + Give a noetherian $X$ and locally free coherent $shf.e$ for which $shf.o (1)$ on
    $sch.p (shf.e)$ is not relatively very ample.
  + Let $f:X->Y$ be of finite type, $shf.l$ ample on $X$, and $shf.s$ a graded
    $shf.o_X$-algebra satisfying $(dagger)$. If $P=sch.proj shf.s$, show that
    $shf.o_P (1) times.o pi^*shf.l^n$ is very ample over $Y$ for all $n$ sufficiently
    large.
]
