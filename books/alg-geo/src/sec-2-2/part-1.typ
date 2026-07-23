#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.2, Lemma 2.1
#lemma(number: "2.1")[
  Let $A$ be a ring and, for an ideal $idl.a subset.eq A$, put
  $V(idl.a)={idl.p in ops.spec A | idl.p supset.eq idl.a}$.

  + For ideals $idl.a,idl.b$, $V(idl.a idl.b)=V(idl.a) union V(idl.b)$.
  + For any family $idl.a_i$, $V(sum_i idl.a_i)=inter_i V(idl.a_i)$.
  + $V(idl.a) subset.eq V(idl.b)$ if and only if $sqrt(idl.a) supset.eq sqrt(idl.b)$.
]


// Hartshorne II.2, Definition D1
#definition(number: none, title: "Spectrum of a Ring")[
  Give $ops.spec A$ the topology whose closed subsets are the $V(idl.a)$. On it,
  let $shf.o (U)$ consist of functions $s$ assigning $s(idl.p) in A_idl.p$ to each
  $idl.p in U$ and locally representable as one quotient $a/f$. The *spectrum*
  of $A$ is the ringed space $(ops.spec A,shf.o)$.
]

// Hartshorne II.2, Proposition 2.2
#proposition(number: "2.2", title: "The Structure Sheaf of an Affine Spectrum")[
  Let $(ops.spec A,shf.o)$ be the spectrum of $A$.

  + For $idl.p in ops.spec A$, $shf.o_idl.p simeq A_idl.p$.
  + For $f in A$, $shf.o (D(f)) simeq A_f$.
  + In particular, $Gamma(ops.spec A,shf.o) simeq A$.
]


// Hartshorne II.2, Definition D2
#definition(number: none, title: "Ringed and Locally Ringed Spaces")[
  A *ringed space* is a pair $(X,shf.o_X)$ of a topological space and a sheaf
  of rings. A morphism $(f,f^sharp):(X,shf.o_X)->(Y,shf.o_Y)$ consists of a continuous
  $f:X->Y$ and a sheaf map $f^sharp:shf.o_Y->f_*shf.o_X$.

  It is *locally ringed* when each stalk $shf.o_(X,P)$ is local. A morphism of
  locally ringed spaces must induce a local homomorphism
  $shf.o_(Y,f(P))->shf.o_(X,P)$ at every $P$.
]

// Hartshorne II.2, Proposition 2.3
#proposition(number: "2.3", title: "Functoriality of Spectrum")[
  + $ops.spec A$ is a locally ringed space.
  + A ring homomorphism $phi:A->B$ induces a natural morphism
    $ops.spec B->ops.spec A$ of locally ringed spaces.
  + Every morphism $ops.spec B->ops.spec A$ of locally ringed spaces arises uniquely
    in this way from a ring homomorphism $A->B$.
]


// Hartshorne II.2, Definition D3
#definition(number: none, title: "Affine Scheme and Scheme")[
  An *affine scheme* is a locally ringed space isomorphic to $ops.spec A$ for
  some ring $A$. A *scheme* is a locally ringed space in which every point
  has an open neighborhood that is affine with the restricted sheaf.
  Its sheaf is the *structure sheaf* $shf.o_X$, its underlying space is
  $ops.sp (X)$, and morphisms of schemes are morphisms of locally ringed spaces.
]

// Hartshorne II.2, Lemma 2.4
#lemma(number: "2.4")[
  Let $S$ be graded and let $idl.a,idl.b,idl.a_i$ be homogeneous ideals.

  + $V(idl.a idl.b)=V(idl.a) union V(idl.b)$ in $ops.proj S$.
  + $V(sum_i idl.a_i)=inter_i V(idl.a_i)$.
]


// Hartshorne II.2, Definition D4
#definition(number: none, title: "Proj of a Graded Ring")[
  Let $ops.proj S$ be the homogeneous prime ideals not containing
  $S_+=bigOPlus(S_d,d>0)$, with closed sets $V(idl.a)$. For
  $idl.p in ops.proj S$, let $S_(idl.p)$ be the degree-zero part of the homogeneous
  localization. Define $shf.o (U)$ as functions into the $S_(idl.p)$ that locally
  are quotients of homogeneous elements of equal degree. The resulting
  ringed space is denoted $(ops.proj S,shf.o)$.
]

// Hartshorne II.2, Proposition 2.5
#proposition(number: "2.5", title: "Basic Affine Opens of Proj")[
  Let $S$ be graded.

  + $shf.o_idl.p simeq S_(idl.p)$ for every $idl.p in ops.proj S$.
  + For homogeneous $f in S_+$, $D_+(f)$ is open, these opens cover
    $ops.proj S$, and $D_+(f) simeq ops.spec S_((f))$ as locally ringed spaces,
    where $S_((f))$ is the degree-zero part of $S_f$.
  + Consequently $ops.proj S$ is a scheme.
]


// Hartshorne II.2, Definition D5
#definition(number: none, title: "Schemes over a Base")[
  A *scheme over* $S$ is a scheme $X$ with a morphism $X->S$. An
  $S$-morphism $X->Y$ commutes with the structure maps. Their category is
  denoted $op("Sch")(S)$; for a ring $A$, $op("Sch")(A)$ means
  $op("Sch")(ops.spec A)$.
]

// Hartshorne II.2, Proposition 2.6
#proposition(number: "2.6", title: "Varieties as Schemes")[
  If $k$ is algebraically closed, there is a natural fully faithful functor
  $t:op("Var")(k)->op("Sch")(k)$. For a variety $V$, its space is
  homeomorphic to the closed points of $ops.sp (t(V))$, and its sheaf of regular
  functions is the restriction of the structure sheaf of $t(V)$.
]
