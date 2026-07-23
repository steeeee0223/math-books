#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Exercises

// Hartshorne I.7, Exercise 7.1
#exercise(title: "Exercise 7.1")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Find the degree of the $d$-uple embedding of $sch.p^n$ in $sch.p^N$.
    _Answer:_ $d^n$.
  + Find the degree of the Segre embedding of $sch.p^r times sch.p^s$.
    _Answer:_ $binom(r+s, r)$.
]

// Hartshorne I.7, Exercise 7.2
#exercise(title: "Exercise 7.2 (Arithmetic Genus)")[
  For a projective variety $Y$ of dimension $r$, define
  $p_a (Y)=(-1)^r (P_Y (0)-1)$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show $p_a (sch.p^n)=0$.
  + If $Y$ is a plane curve of degree $d$, show
    $p_a (Y)=(d-1)(d-2)/2$.
  + If $H$ is a degree-$d$ hypersurface in $sch.p^n$, show
    $p_a (H)=binom(d-1, n)$.
  + If $Y$ is a complete intersection of surfaces of degrees $a,b$ in $sch.p^3$,
    show $p_a (Y)=a b(a+b-4)/2+1$.
  + Under the Segre embedding of varieties $Y,Z$ of dimensions $r,s$, show
    $P_(Y times Z) (l)=P_Y (l)P_Z (l)$ and
    $deg(Y times Z)=binom(r+s, r)deg(Y)deg(Z)$.
]

// Hartshorne I.7, Exercise 7.3
#exercise(title: "Exercise 7.3 (The Dual Curve)")[
  Regard lines in $sch.p^2$ as the dual plane $(sch.p^2)^ast$. For a nonsingular
  $P$ on a curve $Y$, show there is a unique line $T_P (Y)$ with
  $i(Y,T_P (Y);P)>1$. Show $P mapsto T_P (Y)$ is a morphism
  $op("Reg")(Y)->(sch.p^2)^ast$. The closure of its image is the *dual curve* $Y^ast$.
]

// Hartshorne I.7, Exercise 7.4
#exercise(title: "Exercise 7.4")[
  If $Y subset.eq sch.p^2$ is a degree-$d$ curve, show there is a nonempty open
  $U subset.eq (sch.p^2)^ast$ such that every $L in U$ meets $Y$ in exactly $d$
  points.

  _Hint:_ Lines tangent to $Y$ or through a singular point lie in a proper
  closed subset of the dual plane.
]

// Hartshorne I.7, Exercise 7.5
#exercise(title: "Exercise 7.5")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that an irreducible plane curve of degree $d>1$ cannot have a point
    of multiplicity $d$.
  + If it has a point of multiplicity $d-1$, show that it is rational.
]

// Hartshorne I.7, Exercise 7.6
#exercise(title: "Exercise 7.6 (Linear Varieties)")[
  Show that a pure $r$-dimensional algebraic set has degree $1$ if and only if
  it is a linear variety. First use Theorem 7.7 for curves, then cut by a
  hyperplane and induct on dimension.
]

// Hartshorne I.7, Exercise 7.7
#exercise(title: "Exercise 7.7")[
  Let $Y subset.eq sch.p^n$ have dimension $r$ and degree $d>1$, and let
  $P in Y$ be nonsingular. Let $X$ be the closure of the union of all lines
  $P Q$ for $Q in Y without {P}$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show $X$ is a variety of dimension $r+1$.
  + Show $deg X<d$, by induction on $dim Y$.
]

// Hartshorne I.7, Exercise 7.8
#exercise(title: "Exercise 7.8")[
  Let $Y subset.eq sch.p^n$ be a degree-$2$ variety of dimension $r$. Show that
  $Y$ lies in a linear subspace of dimension $r+1$, and hence is isomorphic to
  a quadric hypersurface in $sch.p^(r+1)$.
]
