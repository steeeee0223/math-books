#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// --- Summary block ---
#emph-box()[
  *Reference.*

  - _Introduction to Commutative Algebra_ – Atiyah & MacDonald
  - _Commutative Algebra_ – Matsumura
  - (Ch II) _Algebraic Geometry_ – Lei Fu
  - (Ch II) _My Way to Algebraic Geometry_ – Marco lo Giudice
  - (Ch II) _Foundations of Algebraic Geometry_ – Ravi Vakil
]

// Hartshorne I.1, Definition D1
#definition(number: none, title: "Algebraic Set")[
  A subset $Y$ of $sch.a^n$ is an *algebraic set* if there is a subset
  $T subset.eq A = k[x_1, ..., x_n]$ such that
  $Y = Z(T) = { P in sch.a^n | f(P) = 0 text(" for every ") f in T }$.
]

// Hartshorne I.1, Proposition 1.1
#proposition(number: "1.1")[
  The union of two algebraic sets is an algebraic set. The intersection of any
  family of algebraic sets is an algebraic set. The empty set and the whole
  space are algebraic sets.
]


// Hartshorne I.1, Definition D2
#definition(number: none, title: "Zariski Topology on Affine Space")[
  The *Zariski topology* on $sch.a^n$ is the topology whose closed subsets are
  the algebraic sets, or equivalently whose open subsets are their complements.
]

// Hartshorne I.1, Definition D3
#definition(number: none, title: "Irreducible Subset")[
  A nonempty subset $Y$ of a topological space $X$ is *irreducible* if it
  cannot be expressed as $Y = Y_1 union Y_2$ with $Y_1$ and $Y_2$ proper
  subsets that are closed in $Y$. The empty set is not considered irreducible.
]

// Hartshorne I.1, Definition D4
#definition(number: none, title: "Affine and Quasi-affine Varieties")[
  An *affine algebraic variety* (or simply an *affine variety*) is an
  irreducible closed subset of $sch.a^n$, with the induced topology. An open
  subset of an affine variety is a *quasi-affine variety*.
]

// Hartshorne I.1, Proposition 1.2
#proposition(number: "1.2")[
  Let $A = k[x_1, ..., x_n]$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + If $T_1 subset.eq T_2$ are subsets of $A$, then
    $Z(T_1) supset.eq Z(T_2)$.
  + If $Y_1 subset.eq Y_2$ are subsets of $sch.a^n$, then
    $I(Y_1) supset.eq I(Y_2)$.
  + For any two subsets $Y_1, Y_2 subset.eq sch.a^n$,
    $I(Y_1 union Y_2) = I(Y_1) inter I(Y_2)$.
  + For any ideal $idl.a subset.eq A$, $I(Z(idl.a)) = sqrt(idl.a)$.
  + For any subset $Y subset.eq sch.a^n$, $Z(I(Y)) = overline(Y)$, the closure of
    $Y$.
]


// Hartshorne I.1, Theorem 1.3A
#theorem-box(title: "Theorem 1.3A (Hilbert’s Nullstellensatz).")[
  Let $k$ be an algebraically closed field, and let $idl.a$ be an ideal in
  $A = k[x_1, ..., x_n]$, and let $f in A$ be a polynomial which vanishes at all points
  of $Z(idl.a)$, i.e. $f in I(Z(idl.a))$. Then $f^r in idl.a$ for some integer $r > 0$.
]

#proof[
  Suppose on the contrary that $f in.not sqrt(idl.a)$, we must show that
  $f in.not I(Z(idl.a))$. Recall that
  $ sqrt(idl.a) = { idl.p lt.closed A : text("prime ideal with") idl.p supset idl.a }. $

  We pick a prime ideal $idl.p lt.closed A$ with $idl.p supset idl.a$ for which $f
  in.not idl.p$. Consider the natural ring homomorphism
  $A arrow.r.twohead A slash idl.p := B$, and denote the image of $f$ by
  $overline(f) := f + idl.p$. Note that $overline(f) eq.not 0$ in $B$, so we may consider the localization
  $C := B_overline(f)$. Let $idl.m lt.closed C$ be a maximal ideal, then we have the homomorphism
  $
    k arrow.r.hook A = k[x_1,...,x_n] arrow.r.twohead A slash idl.p = B arrow.r.hook B_overline(f) = C arrow.r.twohead C slash idl.m.
  $

  Now, $C = B_overline(f) = B[1/overline(f)]$ is a finitely generated $B$-algebra, and thus a finitely generated $k$-algebra. So $C slash idl.m$ is a finitely generated $k$-algebra. By *Weak Nullstellensatz (AM, 7.10)*, $[C slash idl.m : k] < oo$, i.e. a finite field extension over $k$. But $k$ is algebraically closed, whence $C slash idl.m = k$.

  Back to the homomorphisms in $(2)$, we suppose
  $ A -> C slash idl.m = k, quad x_i mapsto a_i, $
  and pick $P := (a_1,..., a_n) in sch.a^n$.

  Now, to show that $f in.not I(Z(idl.a))$, it suffices to show that $P in Z(idl.a)$ and $f(P)
  eq 0$. The latter is clear, since $1/overline(f) eq 0$. For any $g in idl.a (subset idl.p)$, the homomorphisms in $(2)$ yield:
  $ A -> A slash idl.p -> k, quad g mapsto overline(g) = 0 mapsto 0 = g(a_1,...,a_n) = g(P). $

  Thus, $P in Z(idl.a)$, and therefore $f in.not I(Z(idl.a))$.
]

// Hartshorne I.1, Corollary 1.4
#corollary(number: "1.4")[
  There is a one-to-one inclusion-reversing correspondence between algebraic
  sets in $sch.a^n$ and radical ideals in $A$, given by
  $Y mapsto I(Y)$ and $idl.a mapsto Z(idl.a)$. Furthermore, an algebraic set is
  irreducible if and only if its ideal is prime.
]


// Hartshorne I.1, Definition D5
#definition(number: none, title: "Affine Coordinate Ring")[
  If $Y subset.eq sch.a^n$ is an affine algebraic set, its *affine coordinate
  ring* is $A(Y) = A slash I(Y)$.
]

// Hartshorne I.1, Remark 1.4.6
#remark(title: "1.4.6")[
  If $Y$ is an affine variety, then $A(Y)$ is an integral domain and a
  finitely generated $k$-algebra. Conversely, every finitely generated
  $k$-algebra $B$ that is a domain is the affine coordinate ring of an affine
  variety: write $B$ as a quotient of a polynomial ring $A$ by an ideal
  $idl.a$, and take $Y = Z(idl.a)$.
]

// Hartshorne I.1, Definition D6
#definition(number: none, title: "Noetherian Topological Space")[
  A topological space $X$ is *noetherian* if it satisfies the descending chain
  condition for closed subsets: every chain
  $Y_1 supset.eq Y_2 supset.eq dots$ is eventually stationary.
]

// Hartshorne I.1, Proposition 1.5
#proposition(number: "1.5")[
  In a noetherian topological space $X$, every nonempty closed subset $Y$ can
  be expressed as a finite union $Y = Y_1 union dots union Y_r$ of irreducible
  closed subsets. If no $Y_i$ contains another, then the $Y_i$ are uniquely
  determined; they are the *irreducible components* of $Y$.
]


// Hartshorne I.1, Corollary 1.6
#corollary(number: "1.6")[
  Every algebraic set in $sch.a^n$ can be expressed uniquely as a union of
  varieties, no one containing another.
]

// Hartshorne I.1, Definition D7
#definition(number: none, title: "Dimension of a Topological Space")[
  The *dimension* of a topological space $X$, denoted $dim X$, is the supremum
  of all integers $n$ for which there is a chain
  $Z_0 subset.neq Z_1 subset.neq dots subset.neq Z_n$ of distinct irreducible
  closed subsets of $X$. The dimension of an affine or quasi-affine variety is
  its dimension as a topological space.
]

// Hartshorne I.1, Definition D8
#definition(number: none, title: "Height and Krull Dimension")[
  The *height* of a prime ideal $idl.p$ in a ring $A$ is the supremum of all
  integers $n$ for which there is a chain
  $idl.p_0 subset.neq idl.p_1 subset.neq dots subset.neq idl.p_n = idl.p$ of distinct prime
  ideals. The *(Krull) dimension* of $A$ is the supremum of the heights of all
  its prime ideals.
]

// Hartshorne I.1, Proposition 1.7
#proposition(number: "1.7")[
  If $Y$ is an affine algebraic set, then $dim Y = dim A(Y)$.
]


// Hartshorne I.1, Theorem 1.8A
#theorem(number: "1.8A")[
  Let $k$ be a field and let $B$ be an integral domain that is a finitely
  generated $k$-algebra.

  #set enum(numbering: "a)", spacing: 0.8em)

  + $dim B = ops.trdeg (K(B) slash k)$, where $K(B)$ is the quotient field of $B$.
  + For every prime ideal $idl.p$ of $B$,
    $ops.ht (idl.p) + dim(B slash idl.p) = dim B$.
]


// Hartshorne I.1, Proposition 1.9
#proposition(number: "1.9")[
  The dimension of $sch.a^n$ is $n$.
]


// Hartshorne I.1, Proposition 1.10
#proposition(number: "1.10")[
  If $Y$ is a quasi-affine variety, then $dim Y = dim overline(Y)$.
]


// Hartshorne I.1, Theorem 1.11A
#theorem-box(
  title: "Theorem 1.11A (Krull’s Hauptidealsatz).",
)[
  Let $A$ be a Noetherian ring, and $f in A$ be an element which is neither a zero divisor nor a unit. Then every minimal prime ideal $idl.p lt.closed A$ containing $f$ has height $1$.
]


// Hartshorne I.1, Proposition 1.12A
#proposition(number: "1.12A")[
  A Noetherian integral domain $A$ is a UFD if and only if every prime ideal of height $1$ is principal.
]

#proof[
  This is *(Matsumura, Theorem 47, p.141)*. We use the fact that
  _A Noetherian integral domain is a UFD iff every irreducible element is prime._

  (⇒) Suppose $A$ is a UFD, let $idl.p lt.closed A$ be any prime ideal with $ops.ht (idl.p) = 1$. (May assume $idl.p eq.not 0$, otherwise trivial). Pick a nonzero element $a in idl.p$, and factorize $a = u a_1^r_1 ... a_n^r_n$ (where $a_i$ irreducible, $u in A^times$, $r_i > 0$). Since $idl.p$ is prime, $a_i in idl.p$ for some $i$. From the fact, $a_i$ is a prime element, so $ideal(a_i) lt.closed A$ is a prime ideal contained in $idl.p$. Note $ops.ht (ideal(a_i)) = 1 = ops.ht (idl.p)$, hence $idl.p = ideal(a_i)$.

  (⇐) Suppose the converse holds, it suffices to show every irreducible element is prime. Let $0 eq.not a in A$ be irreducible, and choose a minimal prime ideal $idl.p lt.closed A$ containing $a$. As $A$ is Noetherian, by (1.11A) $ops.ht (idl.p) = 1$. By assumption, such $idl.p$ must be principal, say $idl.p = ideal(b)$. Then $b$ is prime (hence irreducible). Since $a in idl.p = ideal(b)$ and $a$ irreducible, they must be associated, whence $ideal(a) = ideal(b) = idl.p$. Therefore, $a$ is prime.
]

// Hartshorne I.1, Proposition 1.13
#proposition(number: "1.13")[
  A variety $Y$ in $sch.a^n$ has dimension $n - 1$ if and only if it is the zero
  set $Z(f)$ of a single nonconstant irreducible polynomial
  $f in A = k[x_1, ..., x_n]$.
]


// Hartshorne I.1, Remark 1.13.1
#remark(title: "1.13.1")[
  A prime ideal of height $2$ in a polynomial ring need not be generated by
  two elements; see Exercise 1.11.
]
