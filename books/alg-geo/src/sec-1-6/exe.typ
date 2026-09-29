#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Exercises

// Hartshorne I.6, Exercise 6.1
#exercise(title: "Exercise 6.1")[
  Let $Y$ be a nonsingular rational curve not isomorphic to $sch.p^1$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $Y$ is isomorphic to an open subset of $sch.a^1$.
  + Show that $Y$ is affine.
  + Show that $A(Y)$ is a UFD.
]

// Hartshorne I.6, Exercise 6.2
#exercise(title: "Exercise 6.2 (An Elliptic Curve)")[
  Let $Y:y^2=x^3-x$ in $sch.a^2$, with $ops.char (k)!=2$, and
  $A=k[x,y]\/(y^2-x^3+x)$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $Y$ is nonsingular and $A$ is integrally closed.
  + Show that $k[x]$ is a polynomial ring and $A$ is its integral closure in
    $K(Y)$.
  + Let $sigma:A->A$ fix $x$ and send $y$ to $-y$. For
    $N(a)=a sigma(a)$, show $N(a) in k[x]$, $N(1)=1$, and $N(a b)=N(a) N(b)$.
  + Use the norm to show that $A^times=k without {0}$, that $x,y$ are
    irreducible, and that $A$ is not a UFD.
  + Deduce that $Y$ is not rational.
]

// Hartshorne I.6, Exercise 6.3
#exercise(title: "Exercise 6.3")[
  Give examples showing Proposition 6.8 can fail if either
  (a) $dim X>=2$, or (b) $Y$ is not projective.
]

// Hartshorne I.6, Exercise 6.4
#exercise(title: "Exercise 6.4")[
  Let $Y$ be a nonsingular projective curve. Show that every nonconstant
  $f in K(Y)$ defines a surjective morphism $Y->sch.p^1$ whose fibers are finite.
]

// Hartshorne I.6, Exercise 6.5
#exercise(title: "Exercise 6.5")[
  If a nonsingular projective curve $X$ is a locally closed subvariety of a
  variety $Y$, show that $X$ is closed in $Y$.
]

// Hartshorne I.6, Exercise 6.6
#exercise(title: "Exercise 6.6 (Automorphisms of $PP^1$)")[
  Regard $sch.p^1=sch.a^1 union {oo}$ and let
  $x mapsto (a x+b)/(c x+d)$ with $a d-b c!=0$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that this fractional linear transformation is an automorphism of
    $sch.p^1$; denote their group by $ops.pgl (1)$.
  + Show $ops.aut (sch.p^1) simeq ops.aut_k (k(x))$.
  + Show every $k$-automorphism of $k(x)$ is fractional linear, and deduce
    $ops.pgl (1) simeq ops.aut (sch.p^1)$.
]

// Hartshorne I.6, Exercise 6.7
#exercise(title: "Exercise 6.7")[
  Let $P_1,...,P_r,Q_1,...,Q_s$ be distinct points of $sch.a^1$. If
  $sch.a^1 without {P_1,...,P_r} simeq sch.a^1 without {Q_1,...,Q_s}$, show that
  $r=s$. Is the converse true?
]
