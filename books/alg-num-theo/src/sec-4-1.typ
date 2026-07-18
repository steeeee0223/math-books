#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge

== $p$-Adic Integers

In this section $p$ always denotes a positive prime number in $bb("Z")$.
#definition(number: "219", title: [$p$-Adic Integer])[
  \ A $p$-*adic integer* is a formal series
  $
    a_0+a_1 p+a_2 p^2+ dots.h.c +, (0 <= a_i<p).
  $

  Here, $bb("Z")_p$ denotes the set of all $p$-adic integers.
]


#lemma(number: 220)[
  For $f in bb("Z")$, the residue classes $f op("mod") p^n$ have a unique decomposition of the form
  $
    f equiv a_0+a_1 p+a_2 p^2+ dots.h.c +a_(n-1)p^(n-1) op("mod") p^n
  $

  with each $0 <= a_i<p$.
]

#proof[
  Induction on $n$. For $n=1$,  we have
  $
    f equiv a_0 op("mod") p text("for a unique") 0 <= a_0<p.
  $

  For $n>1$, assume that there are unique $a_i$'s with $0 <= a_i<p$ such that
  $
    f equiv a_0+a_1 p+ dots.h.c +a_(n-1)p^(n-1) quad op("mod") p^n.
  $

  Then $f=a_0+a_1 p+ dots.h.c +a_(n-1)p^(n-1)+b p^n$ for some $b in bb("Z")$, whence $exists ! 0 <= a_n<p$ such that $b=a_n+p dot c, (c in bb("Z"))$. By moding $p^(n+1)$, we have
  $
    f equiv a_0+a_1 p+ dots.h.c +a_(n-1)p^(n-1)+a_n p^n quad op("mod") p^(n+1).
  $

]


#definition(number: "221", title: [$p$-Adic Expansion])[
  For $f in bb("Z")$ the decomposition of the previous lemma gives rise to the sequence
  $
    s_1=a_0, s_2=a_0+a_1 p, s_3=a_0+a_1 p+a_2 p^2, dots.h.c .
  $

  We succinctly write $sum_(i=0)^oo a_i p^i$ for the sequence $(s_i)$ and call this expression the $p$-*adic expansion* of $f$.\
  Note that $p divides.not f$ implies that $op("gcd"){(f,p^n)}=1$ so that $a dot f+b dot p^n=1$ for some $a,b in bb("Z")$, and thus $a dot f equiv 1 op("mod") p^n$, or equivalently, $f^(-1) equiv a op("mod") p^n$. Hence we can assign a development to $f^(-1)$ as before. In particular, this yields an expansion for every element in $bb("Z")_p$, (cf. Exercise).
]


#definition(number: "222", title: [$p$-Adic Number])[
  \ A $p$-*adic number* is a formal Laurent series $sum_(i=-m)^oo a_i p^i$ with $m in bb("Z"), 0 <= a_i<p$. We then write $bb("Q")_p$ for the set of all $p$-adic numbers.
]


#remark(number: 223)[
  For $f in bb("Q")$, we write $f=frac(g, h) dot p^(-m), (m,g,h in bb("Z"))$ with $op("gcd"){(g h,p)}=1$. Then $frac(g, h) in bb("Z")_p$ has an expansion $sum_(i=0)^oo a_i p^i$ and we assign to $f$ the expansion $sum_(i=-m)^oo a_(i+m)p^i$.\
  It follows that we have an injection $bb("Q") arrow.r.hook bb("Q")_p$ which restricts to $bb("Z") arrow.r.hook bb("Z")_p$, (this is not a morphism yet since we defined $bb("Z")_p$ and $bb("Q")$ as sets, not as rings or fields). In this way we obtained an algebraic counterpart for the development of a holomorphic or meromomorphic function into a power or Laurent series.
]


#example(number: 224)[
  - _(a)_ $3$-adic expansion of $216$:
  $
    216=3^3 dot 8, quad 8=2+3 dot 2,
  $

  so that $216=2 dot 3^3+2 dot 3^4$. This is sometimes also written as $0,0022$ -- the higher the power, the smaller the contribution. Similarly, we find for the $5$-adic expansion
  $
    216=1+5 dot 43, quad 43=3+5 dot 8, quad 8=3+5,
  $

  so we have $216=1,331$.
  - _(b)_ We have $-1= sum_(i=0)^oo (p-1)p^i$, for $-1 equiv p-1+p(p-1) op("mod") p^2$, etc.
  - _(c)_ We have
  $
    frac(1, p-1) equiv 1+p+ dots.h.c +p^(n-1) quad op("mod") p^n
  $

  for $1=(1+p+ dots.h.c +p^(n-1))(p-1)+p^n$.

]


The construction of $bb("Z")_p$ provides an example for the _completion_ of a ring. We are now going to investigate this notion systematically.
#definition(number: "225", title: [Null & Cauchy Sequence])[
  - Let $A$ temporarily denote an abelian topological group, i.e. $A$ carries a topology for which addition and taking inverses are continuous operations.
  - Since the translation $T_b:A -> A, a mapsto a+b$ for a fixed $b in A$ defines a homeomorphism, the topology of $A$ is determined by the neighbourhoods of $0$.
  - In addition, we assume that there is a countable fundamental system ${U_j }_(j in bb("N"))$ of neighbourhoods of $0$, i.e. any open set containing $0$ eventually contains some $U_j$.
  - A *null sequence* $(a_n)$ in $A$ is a sequence such that for all $j in bb("N")$ there exists $N(j) in bb("N")$ with $a_n in U_j$ provided $n >= N(j)$.
  - A *Cauchy sequence* $(a_n)$ in $A$ is a sequence such that for all $j in bb("N")$ there exists $N(j) in bb("N")$ with $a_n-a_m in U_j$ provided $n,m >= N(j)$. Moreover, two Cauchy sequences $(a_n)$ and $(b_n)$ are *equivalent*, write $(a_n) tilde (b_n)$, if $(a_n-b_n)$ is a null sequence.

]


#definition(number: "226", title: [Completions])[
  - We define the *completion* of $A$ by
  $
    hat(A) := text("Cauchy sequences in $A$")/ tilde .
  $

  - To define a topology on $hat(A)$ we exhibit a fundamental system ${hat(U)_j }_(j in bb("N"))$ of neighbourhoods at $hat(0)$, the equivalence class of the constant sequence $(a_n)=(0)$. Namely, $U_j$ consists of equivalence classes $overline((a_n))$ with $a_n in U_j subset A$ for all except finitely many $n in bb("N")$.
  - Addition of Cauchy sequences makes $hat(A)$ a topological group. The natural map $phi:A -> hat(A), a mapsto overline((a_n))=overline((a))$, is a continuous group homomorphism. If $phi$ is an isomorphism, we say that $A$ is *complete*.
  - If $phi:A -> B$ is a continuous group homomorphism, then $phi$ maps Cauchy sequences to Cauchy sequences and induces a continuous ring homomorphism $hat(phi):hat(A) -> hat(B)$. The assignment $A -> hat(A), phi mapsto hat(phi)$ is thus functorial.

]


#remark(number: 227)[
  If we start with a topological ring, then its completion is also a topological ring using the natural product of Cauchy sequences.
]


From an algebraic point of view, a natural way to obtain a topological group is by choosing a _filtration_ for $A$.
#definition(number: "228", title: [Filtration])[
  Let $A$ be an abelian group. A *filtration*
  $
    A=frak("a")_0 supset frak("a")_1 supset frak("a")_2 supset dots.h.c
  $

  is a descending chain of subgroups. It gives $A$ the structure of a topological group by taking $U_j=frak("a")_j$ as a system of open neighbourhoods of $0$. In particular, let $A$ be a ring and $frak("a") lt.closed A$ an ideal. The $frak("a")$-*adic filtration* is given by $frak("a")_j := frak("a")^j$. We denote the resulting completion by $hat(A)_frak("a")$.
]


#note(number: "228*", title: [])[
  If $A$ is a topological group whose topology is determined by a filtration $frak("a")_0 supset frak("a")_1 supset dots.h.c$ and $(a_n)$ is a Cauchy sequence, then its image in $A/frak("a")_j$ is fixed, becomes eventually constant and is equal to $xi_j equiv a_N (op("mod") frak("a")_j)$, where $N$ is minimal among all $M$ such that $a_k-a_l in frak("a")_j$ for all $k,l >= M$.\
  Note that $xi_j equiv a_M (op("mod") frak("a")_j)$ for all $M >= N$. The resulting sequence is therefore _coherent_ in the sense that the canonical projection
  $
    theta_(j+1):A/frak("a")_(j+1) arrow.r.twohead A/frak("a")_j, quad a+frak("a")_(j+1) arrow.r.long.bar a+frak("a")_j
  $

  maps $xi_(j+1) mapsto xi_j$. It follows that we can identify the completion $hat(A)$ with the space of coherent sequences. This motivates the following construction.
]


#definition(number: "229", title: [Inverse System & Inverse Limit])[
  \ Let ${A_i }_(i in bb("N"))$ be a family of abelian groups together with group homomorphisms $theta_(i j):A_j -> A_i$ such that
  - $theta_(i i)=1_(A_i)$ for all $i in bb("N")$.
  - $theta_(i k)=theta_(i j) compose theta_(j k):A_k -> A_i$ whenever $i <= j <= k$.

  We also say that $(A_i, theta_(i j))$ (or simply $A_i$ for short) defines an *inverse system*. The abelian group
  $
    attach(op("lim"), b: arrow.l, br: i in I) A_i := {a in product_(i in I)A_i:a_i=theta_(i j)(a_j), forall i <= j text("in") I}
  $

  is called the *inverse limit* of the family.
]


#remark(number: 230)[
  The inverse limit comes with natural projections
  $
    pi_j: attach(op("lim"), b: arrow.l) A_i arrow.r.twohead A_j quad text("satisfying") quad theta_(i j) compose pi_j=pi_i.
  $

  This even characterises the inverse limit via the following universal property: If $A$ is an abelian group together with morphisms $psi_i:A -> A_i$ such that $theta_(i j) compose psi_j=psi_i$, then there exists a unique morphism
  $
    psi:A -> attach(op("lim"), b: arrow.l) A_i quad text("such that") quad pi_j compose psi=psi_j, forall j in I.
  $

  #align(center)[#diagram(
    cell-size: 18mm,
    $
      & A edge("d", psi_j, ->) edge("dl", exists! psi, "-->", stroke: std.red) \
      attach(op("lim"), b: arrow.l) A_i edge("r", pi_j, ->) & A_j
    $,
  )]
]


#note(number: "231", title: [Completions as Inverse Limits])[
  \ Let $A$ be an abelian group whose topology is defined by the filtration
  $
    A=frak("a")_0 supset frak("a")_1 supset frak("a")_2 supset dots.h.c .
  $

  Let $pi_(i j):A/frak("a")_j arrow.r.twohead A/frak("a")_i, (i <= j)$, be the natural projection map. Since the completion $hat(A)$ with respect to this filtration equals the set of coherent sequences which is just the inverse limit of the system ${A/frak("a")_i }$, we thus obtain
  $
    hat(A) equiv attach(op("lim"), b: arrow.l) A/frak("a")_i = {a in product_(i in I)A/frak("a")_i:a_i=pi_(i j)(a_j), forall i <= j text("in") I}.
  $

]


#remark(number: 232)[
  If $A$ is a ring and ${frak("a")_j }_(j in bb("N"))$ is a filtration by ideals, then restricting multiplication from the product ring $product_(j in bb("N"))A/frak("a")_j$ yields a ring structure in $hat(A)$.
]


#example(number: 233)[
  - _(a)_ *$p$-Adic Integers.* Let $p$ be a prime number. Then we have
  $
    bb("Z")_p equiv hat(bb("Z"))_((p)) equiv attach(op("lim"), b: arrow.l, br: n in bb("N")) bb("Z")/p^(n+1) bb("Z").
  $

  proof. We obtain a bijection by associating to every $p$-adic integer $a := sum_(i=0)^oo a_i p^i$ the sequence $(overline(s_n))$ given by $overline(s_n) := a+(p^(n+1)) in bb("Z")/p^(n+1) bb("Z")$, (cf. *Lemma 220*). In particular, this induces a ring structure on $bb("Z")_p$. Note that addition is done by "carrying", not "termwise". \
  For instance,
  $
    1+[p-1+a p]=cases((a+1)p & text("if") a<p-1, p^2 & text("if") a=p-1).
  $

  - _(b)_ *Power Series.* Let $A=B[x_1, dots.h.c ,x_n]$ be a polynomial ring over $B$ and take the maximal ideal $frak("m")=(x_1, dots.h.c ,x_n)$. Then
  $
    hat(A)_frak("m") equiv attach(op("lim"), b: arrow.l, br: j in bb("N")) A/frak("m")^(j+1) equiv B ⟦x_1, dots.h.c ,x_n⟧.
  $

  proof. Indeed, we obtain a bijection by sending as in the previous item
  $
    B ⟦x_1, dots.h.c ,x_n⟧ , arrow.r.long hat(A)_frak("m"),; f := sum_(alpha >= 0)a_(alpha)x^alpha , arrow.r.long.bar (overline(s_j)): overline(s_j) := f+frak("m")^(j+1) in A/frak("m")^(j+1).
  $


]


Now, we see that the inverse limit has good functorial properties:
#definition(number: 234)[
  - An inverse system ${A_i }$ is called *surjective* if for any $i <= j, theta_(i j):A_j -> A_i$ is surjective.
  - An *exact sequence* of inverse systems
  $
    0 -> {A'_j } -> {A_j } -> {A''_j } -> 0
  $

  consists of a commutative diagram
  #align(center)[#diagram(
    cell-size: 15mm,
    $
      0 edge("r", ->) & A'_(j+1) edge("r", ->) edge("d", theta'_(j,j+1), ->)
      & A_(j+1) edge("r", ->) edge("d", theta_(j,j+1), ->)
      & A''_(j+1) edge("r", ->) edge("d", theta''_(j,j+1), ->) & 0 \
      0 edge("r", ->) & A'_j edge("r", ->) & A_j edge("r", ->) & A''_j edge("r", ->) & 0
    $,
  )]
  of exact sequences where the maps $theta'_(i j), theta_(i j)$ and $theta''_(i j)$ are provided by the inverse systems ${A'_i }, {A_i }$ and ${A''_i }$, respectively.

]


The followings are the rather straightforward homological arguments involving the so-called "_Snake Lemma_":
#proposition(number: 235)[
  If $0 -> {A'_j } -> {A_j } -> {A''_j } -> 0$ is an exact sequence of inverse systems, then taking inverse limit is a "left exact functor", i.e.
  $
    0 -> attach(op("lim"), b: arrow.l) A'_j -> attach(op("lim"), b: arrow.l) A_j -> attach(op("lim"), b: arrow.l) A''_j \
  $

  is exact. Furthermore, if ${A_j }$ is a surjective system, then
  $
    0 -> attach(op("lim"), b: arrow.l) A'_j -> attach(op("lim"), b: arrow.l) A_j -> attach(op("lim"), b: arrow.l) A''_j -> 0
  $

  is exact. [AM, 10.2]
]


#corollary(number: 236)[
  Let $0 -> A' -> A attach(arrow.r.twohead, t: p) A'' -> 0$ be an exact sequence of groups. Let ${frak("a")_j }$ be a filtration of subgroups in $A$, and endow $A'$ and $A''$ with the *induced filtrations* given by ${A' inter frak("a")_j }$ and ${p(frak("a")_j)}$, respectively. Then we have the exact sequence of groups
  $
    0 -> hat(A)' -> hat(A) -> hat(A)'' -> 0
  $

  completed with respect to these filtrations. [Exercise]
]


#corollary(number: 237)[
  If we complete with respect to the induced filtrations, then $hat(frak("a")_j)$ is a subgroup of $hat(A)$ and $hat(A)/hat(frak("a")_j) equiv A/frak("a")_j$. In particular, completing $hat(A)$ with respect to ${hat(frak("a")_j)}$ yields $hat(hat(A)) equiv hat(A)$. [Exercise]
]


Before we investigate completions further, we give an important application, see, for example, [Commutative Algebra, Eisenbud, 7.3] for a proof:
#theorem(number: "238", title: [Hensel's Lemma Ver. I])[
  \ Let $A equiv hat(A)_frak("m")$ be a ring that is complete with respect to the ideal $frak("m")$ and let $f in A[x]$. If $a$ is an approximate root of $f$ in the sense that $f(a) equiv 0 (op("mod") f'(a)^2 frak("m"))$, then there exists a root $b in A$ of $f$ which is near $a$ in the sense that $b equiv a (op("mod") f'(a) frak("m"))$. If $f'(a)$ is not a zero-divisor in $A$, then $b$ is unique with this property. In particular, if $f'(a)$ is a unit, then $f(a) equiv 0 (op("mod") frak("m"))$ implies that there exists a unique $b in A$ such that
  $
    f(b)=0 quad text("and") quad b equiv a op("mod") frak("m").
  $

]


#example(number: 239)[
  - _(a)_ We use *Hensel's Lemma* to determine the $p$-adic integer $c$ which admits a square root in $bb("Z")_p$. First write $c=p^n b$ for some $n in bb("N")$ and $b in bb("Z")_p^times$. Hence $c$ is a square iff $n$ is even and $b$ admits a square root in $bb("Z")_p$. \
    proof. If $b$ is not a square in $bb("Z")_p$, we are done. Otherwise, $overline(b)=overline(a)^2$ in $bb("Z")_p/(p) bb("Z")_p$ for a unit $a in bb("Z")_p^times$. Since $bb("Z")_p/(p) bb("Z")_p equiv bb("Z")/(p)$, (where $hat((p)) equiv (p) bb("Z")_p$ follows from *Lemma 296* below), we can effectively decide whether or not $overline(b)$ is a square by computing its _Legendre symbol_ from elementary number theory.\
    Then $f=x^2-b in bb("Z")_p[x]$ has a root. If $p=2$, this follows from elementary considerations, [Exercise]. Otherwise, $f'(a)=2a$ is a unit in $bb("Z")_p$. Further, $f(a) equiv 0 (op("mod") (p) bb("Z")_p)$ by design of $a$. *Hensel's Lemma* therefore guarantees the existence of a unique root $b equiv a (op("mod") (p) bb("Z")_p)$.
  - _(b)_ If $f(t,x) in k[t,x]$ is a polynomial in two variables, and $x=a$ is a simple root of $f(0,x)$, then there is a unique power series $x(t) in k [[ t ]]$ with $x(0)=a$ and $f(t,x(t))=0$ identically.\
    proof. Indeed, consider $f(t,x)=f_t(x)$ as an element of $k [[ t ]][x]=hat(k[t])_((t))[x]$. Since $f_t(a) equiv f_0(a) equiv 0 (op("mod") (t) hat(k[t])_((t)))$, there exists a unique $x(t) in k [[ t ]]$ with $f_t(x(t))=0$ and $x(t) equiv a (op("mod") (t))$, i.e. $x(0)=a$.

]


#remark(number: 240)[
  The condition that $f(0,a)$ is a simple root means that $∂_x f(0,a) eq.not 0$. In this sense, *Hensel's Lemma* is the algebraic (and equally powerful) analogue of _Implicit Function Theorem_.
]


#example(number: 241)[
  To illustrate the previous remark further and to emphasise the (yet to make precise) "local" nature of completions, we consider the inclusion
  $
    k[x] arrow.r.hook A=k[x,y]/(y^2-x-1), x mapsto x op("mod") (y^2-x-1).
  $

  Taking spectra we obtain a ramified finite cover which is generically 2-1. In a neighbourhood without branching points (e.g. near $(x,y)=(0,-1)$), one should be able to invert this map and to find local sections of this covering -- this is certainly trur if $k=bb("R")$ or $bb("C")$ using the _Inverse Function Theorem_.\
  In general, we face the problem that the map
  $
    y op("mod") (y^-x-1) arrow.r.long.bar sqrt(x+1)
  $

  is not defined at $sqrt(x+1) in.not k[x]$. However,
  $
    sqrt(x+1) = 1+frac(x, 2)-frac(x^2, 8)+ dots.h.c
  $

  has a development in the completion $k [[ x ]]$. Therefore, it follows from *Cor. 298* that the inverse map
  $
    hat(A)_((overline(x),overline(y+1))) equiv k [[ x,y ]]/(y^2-x-1)^e , -> k [[ x ]],; x , mapsto x;; y , mapsto 1+frac(x, 2)-frac(x^2, 8)+ dots.h.c
  $

  is defined at the level of completions.
]
