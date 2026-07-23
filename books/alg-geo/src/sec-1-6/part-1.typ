#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne I.6, Definition D1
#definition(number: none, title: "Valuation and Valuation Ring")[
  Let $K$ be a field and $G$ a totally ordered abelian group. A *valuation* of
  $K$ with values in $G$ is a map $v:K without {0}->G$ satisfying
  $v(x y)=v(x)+v(y)$ and $v(x+y)>=min(v(x),v(y))$. Its *valuation ring* is
  $R={x in K | v(x)>=0} union {0}$, with maximal ideal
  $idl.m={x in K | v(x)>0} union {0}$. If $k subset.eq K$ and $v$ vanishes on
  $k without {0}$, then $v$ and $R$ are said to be of $K\/k$.
]

// Hartshorne I.6, Definition D2
#definition(number: none, title: "Domination of Local Rings")[
  If $A,B$ are local rings contained in a field $K$, then $B$ *dominates* $A$
  if $A subset.eq B$ and $idl.m_B inter A=idl.m_A$.
]

// Hartshorne I.6, Theorem 6.1A
#theorem(number: "6.1A")[
  A local ring $R subset.eq K$ is a valuation ring of $K$ if and only if it is
  maximal among local subrings of $K$ under domination. Every local subring of
  $K$ is dominated by a valuation ring.
]


// Hartshorne I.6, Definition D3
#definition(number: none, title: "Discrete Valuation Ring")[
  A valuation is *discrete* if its value group is $ZZ$. Its valuation ring is
  a *discrete valuation ring* (DVR).
]

// Hartshorne I.6, Theorem 6.2A
#theorem(number: "6.2A")[
  For a noetherian local domain $(A,idl.m)$ of dimension $1$, the following are
  equivalent:

  #set enum(numbering: "(i)", spacing: 0.8em)

  + $A$ is a DVR;
  + $A$ is integrally closed;
  + $A$ is regular;
  + $idl.m$ is principal.
]


// Hartshorne I.6, Definition D4
#definition(number: none, title: "Dedekind Domain")[
  A *Dedekind domain* is an integrally closed noetherian domain of dimension
  $1$.
]

// Hartshorne I.6, Theorem 6.3A
#theorem(number: "6.3A")[
  The integral closure of a Dedekind domain in a finite extension of its
  quotient field is again a Dedekind domain.
]


// Hartshorne I.6, Lemma 6.4
#lemma(number: "6.4")[
  Let $Y$ be quasi-projective and $P,Q in Y$. If
  $shf.o_(Q,Y) subset.eq shf.o_(P,Y)$ as subrings of $K(Y)$, then $P=Q$.
]


// Hartshorne I.6, Lemma 6.5
#lemma(number: "6.5")[
  Let $K\/k$ be a function field of dimension $1$ and let $C_K$ be its discrete
  valuation rings over $k$. For every $x in K$, the set
  ${R in C_K | x in.not R}$ is finite.
]


// Hartshorne I.6, Corollary 6.6
#corollary(number: "6.6")[
  Every discrete valuation ring of $K\/k$ is isomorphic to the local ring of a
  point on some nonsingular affine curve.
]


// Hartshorne I.6, Definition D5
#definition(number: none, title: "Abstract Nonsingular Curve")[
  Let $K\/k$ be a function field of dimension $1$ and $C_K$ its set of DVRs
  over $k$, topologized so finite subsets and $C_K$ are closed. For open
  $U subset.eq C_K$, put $shf.o (U)=inter_(P in U)R_P$. An *abstract nonsingular
  curve* is an open subset of $C_K$ with this topology and these regular
  functions.
]

// Hartshorne I.6, Definition D6
#definition(number: none, title: "Morphisms of Abstract Curves")[
  A morphism $phi:X->Y$ between abstract nonsingular curves or varieties is a
  continuous map such that every regular function on an open
  $V subset.eq Y$ pulls back to a regular function on $phi^(-1) (V)$.
]

// Hartshorne I.6, Proposition 6.7
#proposition(number: "6.7")[
  Every nonsingular quasi-projective curve is isomorphic to an abstract
  nonsingular curve.
]


// Hartshorne I.6, Proposition 6.8
#proposition(number: "6.8")[
  Let $X$ be an abstract nonsingular curve, $P in X$, and $Y$ projective.
  Every morphism $phi:X without {P}->Y$ extends uniquely to a morphism
  $bar(phi):X->Y$.
]


// Hartshorne I.6, Theorem 6.9
#theorem(number: "6.9")[
  For every function field $K\/k$ of dimension $1$, the abstract nonsingular
  curve $C_K$ is isomorphic to a nonsingular projective curve.
]


// Hartshorne I.6, Corollary 6.10
#corollary(number: "6.10")[
  Every abstract nonsingular curve is quasi-projective. Every nonsingular
  quasi-projective curve is an open subset of a nonsingular projective curve.
]

// Hartshorne I.6, Corollary 6.11
#corollary(number: "6.11")[
  Every curve is birationally equivalent to a nonsingular projective curve.
]


// Hartshorne I.6, Corollary 6.12
#corollary(number: "6.12")[
  The following categories are equivalent:

  #set enum(numbering: "(i)", spacing: 0.8em)

  + nonsingular projective curves with dominant morphisms;
  + quasi-projective curves with dominant rational maps;
  + function fields of dimension $1$ over $k$ with $k$-homomorphisms.
]
