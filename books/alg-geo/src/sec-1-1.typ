#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Affine Varieties

// --- Summary block ---
#emph-box()[
  *Reference.*

  - _Introduction to Commutative Algebra_ – Atiyah & MacDonald
  - _Commutative Algebra_ – Matsumura
  - (Ch II) _Algebraic Geometry_ – Lei Fu
  - (Ch II) _My Way to Algebraic Geometry_ – Marco lo Giudice
  - (Ch II) _Foundations of Algebraic Geometry_ – Ravi Vakil
]

// --- Theorem 1.3 ---
#theorem-box(title: "Theorem 1.3 (Hilbert’s Nullstellensatz).")[
  Let $k$ be an algebraically closed field, and let $aa$ be an ideal in
  $A = k[x_1, ..., x_n]$, and let $f in A$ be a polynomial which vanishes at all points
  of $Z(aa)$, i.e. $f in I(Z(aa))$. Then $f^r in aa$ for some integer $r > 0$.
]

#proof[
  Suppose on the contrary that $f in.not sqrt(aa)$, we must show that
  $f in.not I(Z(aa))$. Recall that
  $ sqrt(aa) = { pp lt.closed A : text("prime ideal with") pp supset aa }. $

  We pick a prime ideal $pp lt.closed A$ with $pp supset aa$ for which $f
  in.not pp$. Consider the natural ring homomorphism
  $A arrow.r.twohead A slash pp := B$, and denote the image of $f$ by
  $overline(f) := f + pp$. Note that $overline(f) eq.not 0$ in $B$, so we may consider the localization
  $C := B_overline(f)$. Let $mm lt.closed C$ be a maximal ideal, then we have the homomorphism
  $
    k arrow.r.hook A = k[x_1,...,x_n] arrow.r.twohead A slash pp = B arrow.r.hook B_overline(f) = C arrow.r.twohead C slash mm.
  $

  Now, $C = B_overline(f) = B[1/overline(f)]$ is a finitely generated $B$-algebra, and thus a finitely generated $k$-algebra. So $C slash mm$ is a finitely generated $k$-algebra. By *Weak Nullstellensatz (AM, 7.10)*, $[C slash mm : k] < oo$, i.e. a finite field extension over $k$. But $k$ is algebraically closed, whence $C slash mm = k$.

  Back to the homomorphisms in $(2)$, we suppose
  $ A -> C slash mm = k, quad x_i mapsto a_i, $
  and pick $P := (a_1,..., a_n) in AA^n$.

  Now, to show that $f in.not I(Z(aa))$, it suffices to show that $P in Z(aa)$ and $f(P)
  eq 0$. The latter is clear, since $1/overline(f) eq 0$. For any $g in aa (subset pp)$, the homomorphisms in $(2)$ yield:
  $ A -> A slash pp -> k, quad g mapsto overline(g) = 0 mapsto 0 = g(a_1,...,a_n) = g(P). $

  Thus, $P in Z(aa)$, and therefore $f in.not I(Z(aa))$.
]

// --- Theorem 1.11 ---
#theorem-box(
  title: "Theorem 1.11 (Krull’s Hauptidealsatz).",
)[
  Let $A$ be a Noetherian ring, and $f in A$ be an element which is neither a zero divisor nor a unit. Then every minimal prime ideal $pp lt.closed A$ containing $f$ has height $1$.
]

// --- Theorem 1.12 ---
#theorem-box(title: "Theorem 1.12.")[
  A Noetherian integral domain $A$ is a UFD if and only if every prime ideal of height $1$ is principal.
]

#proof[
  This is *(Matsumura, Theorem 47, p.141)*. We use the fact that
  _A Noetherian integral domain is a UFD iff every irreducible element is prime._

  (⇒) Suppose $A$ is a UFD, let $pp lt.closed A$ be any prime ideal with $Ht(pp) = 1$. (May assume $pp eq.not 0$, otherwise trivial). Pick a nonzero element $a in pp$, and factorize $a = u a_1^r_1 ... a_n^r_n$ (where $a_i$ irreducible, $u in A^times$, $r_i > 0$). Since $pp$ is prime, $a_i in pp$ for some $i$. From the fact, $a_i$ is a prime element, so $ideal(a_i) lt.closed A$ is a prime ideal contained in $pp$. Note $Ht(ideal(a_i)) = 1 = Ht(pp)$, hence $pp = ideal(a_i)$.

  (⇐) Suppose the converse holds, it suffices to show every irreducible element is prime. Let $0 eq.not a in A$ be irreducible, and choose a minimal prime ideal $pp lt.closed A$ containing $a$. As $A$ is Noetherian, by (1.11) $Ht(pp) = 1$. By assumption, such $pp$ must be principal, say $pp = ideal(b)$. Then $b$ is prime (hence irreducible). Since $a in pp = ideal(b)$ and $a$ irreducible, they must be associated, whence $ideal(a) = ideal(b) = pp$. Therefore, $a$ is prime.
]
