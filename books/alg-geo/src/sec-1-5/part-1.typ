#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne I.5, Definition D1
#definition(number: none, title: "Nonsingularity via the Jacobian")[
  Let $Y subset.eq sch.a^n$ be affine of dimension $r$, and let
  $f_1,...,f_t$ generate $I(Y)$. The variety $Y$ is *nonsingular at*
  $P in Y$ if the Jacobian matrix
  $(partial f_i)/(partial x_j)(P)$ has rank $n-r$. It is *nonsingular* if this
  holds at every point.
]

// Hartshorne I.5, Definition D2
#definition(number: none, title: "Regular Local Ring")[
  A noetherian local ring $(A,idl.m)$ with residue field $k=A\/idl.m$ is *regular* if
  $dim_k (idl.m\/idl.m^2)=dim A$.
]

// Hartshorne I.5, Theorem 5.1
#theorem(number: "5.1")[
  Let $Y subset.eq sch.a^n$ be affine and $P in Y$. Then $Y$ is nonsingular at
  $P$ if and only if $shf.o_(P,Y)$ is a regular local ring.
]


// Hartshorne I.5, Definition D3
#definition(number: none, title: "Nonsingular Variety")[
  An arbitrary variety $Y$ is *nonsingular at* $P$ if $shf.o_(P,Y)$ is a regular
  local ring. It is *nonsingular* if this holds everywhere, and *singular*
  otherwise.
]

// Hartshorne I.5, Proposition 5.2A
#proposition(number: "5.2A")[
  If $(A,idl.m)$ is a noetherian local ring with residue field $k$, then
  $dim_k (idl.m\/idl.m^2) >= dim A$.
]


// Hartshorne I.5, Theorem 5.3
#theorem(number: "5.3")[
  For every variety $Y$, the singular locus $ops.sing Y$ is a proper closed
  subset of $Y$.
]


// Hartshorne I.5, Theorem 5.4A
#theorem(number: "5.4A")[
  Let $(A,idl.m)$ be noetherian local and let $hat(A)$ be its completion.

  #set enum(numbering: "a)", spacing: 0.8em)

  + $hat(A)$ is local with maximal ideal $idl.m hat(A)$, and $A->hat(A)$ is
    injective.
  + For a finitely generated $A$-module $M$, its completion is
    $hat(M) simeq tensor(M, hat(A), over: A)$.
  + $dim hat(A)=dim A$.
  + $A$ is regular if and only if $hat(A)$ is regular.
]


// Hartshorne I.5, Theorem 5.5A
#theorem(number: "5.5A", title: "Cohen Structure Theorem")[
  If $A$ is a complete regular local ring of dimension $n$ containing a field,
  then $A$ is isomorphic to the formal power-series ring
  $k text("[[") x_1,...,x_n text("]] ")$ over its residue field.
]


// Hartshorne I.5, Definition D4
#definition(number: none, title: "Analytic Isomorphism")[
  Points $P in X$ and $Q in Y$ are *analytically isomorphic* if their completed
  local rings $hat(shf.o_(P,X))$ and $hat(shf.o_(Q,Y))$ are isomorphic as
  $k$-algebras.
]

// Hartshorne I.5, Theorem 5.7A
#theorem(number: "5.7A", title: "Elimination Theory")[
  Let $f_1,...,f_r$ be homogeneous polynomials in $x_0,...,x_n$ with
  indeterminate coefficients $a_(i j)$. There are integer polynomials
  $g_1,...,g_t$ in the $a_(i j)$, homogeneous in the coefficients of each
  $f_i$ separately, such that after specialization over any field $k$, the
  $f_i$ have a common nonzero zero if and only if the specialized coefficients
  are a common zero of all $g_j$.
]
