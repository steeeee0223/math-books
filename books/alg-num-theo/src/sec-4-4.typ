#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge

== Completions of Modules

We already considered the completion of ideals. Next we consider the completion of modules in general.
#definition(number: "288", title: [$frak("a")$-Filtration])[
  \ Let $M$ be an $A$-module and $frak("a") lt.closed A$ an ideal.
  - The $frak("a")$-*adic filtration* of $M$ is given by $M_n := frak("a")^n dot M$.
  - The $frak("a")$-adic completion of $M$ is the $hat(A)$-module defined by
  $
    hat(M)_frak("a") := attach(op("lim"), b: arrow.l, br: n in bb("N")) M/frak("a")^n M.
  $

  - An $A$-linear map $phi:M -> N$ maps $M_n$ to $N_n$ and induces the map $hat(phi):hat(M)_frak("a") -> hat(N)_frak("a")$.
  - A descending filtration $(M_n)$ is called an $frak("a")$-*filtration* if $frak("a")M_n subset M_(n+1)$ for all $n$.
  - If we have equality for all sufficiently large $n$, then the $frak("a")$-filtration is called *stable*. For instance, the $frak("a")$-adic filtration $(frak("a")^n M)$ is trivially $frak("a")$-stable.

]


#lemma(number: 289)[
  If $(M_n)$ and $(M'_n)$ are stable $frak("a")$-filtrations, then there exists an integer $k in bb("N")$ such that $M_(n+k) subset M'_n subset M_(n-k)$ for all $n >= k$, i.e. both filtrations have *bounded difference*.\ In particular, all stable $frak("a")$-filtrations induce the same topology on $M$, namely the $frak("a")$-topology. [AM, 10.6]
]

#proof[
  By cutting off a sufficiently large number of submodules $M'_1, dots.h.c .M'_(n_0)$, we may assume that $M'_n=frak("a")^n M$. As $(M_n)$ is an $frak("a")$-filtration, the definition $frak("a")M_n subset M_(n+1)$ for all $n$ implies that
  $
    M_n supset frak("a")M_(n-1) supset dots.h.c supset frak("a")^n M_0=frak("a")^n M, quad text("for all") n.
  $

  Moreover, $(M_n)$ is stable, so there is a sufficiently large $k in bb("N")$ such that for all $n >= 0$ we have
  $
    M_(n+k)=frak("a")^n M_k subset frak("a")^n M=M'_n subset M_n subset M_(n-k).
  $

]


In the sequel, all completions will be taken with respect to some $frak("a")$-adic topology unless mentioned otherwise.\
Let $A$ be a ring and $frak("a") lt.closed A$ an ideal. Then
$
  A^ast := plus.o.big_(n >= 0) frak("a")^n
$

defines a graded ring. For instance, if $A$ is Noetherian so that $frak("a")=(a_1, dots.h.c ,a_n)$ is finitely generated, then $A^ast =A[a_1, dots.h.c ,a_n]$. In particular, $A^ast$ is Noetherian. Now, if $M$ is an $A$-module with an $frak("a")$-filtration $(M_n)$, then
$
  M^ast := plus.o.big_(n >= 0)M_n
$

is a graded $A^ast$-module.

#lemma(number: 290)[
  Let $A$ be a Noetherian ring and $M$ be a finitely generated $A$-module with an $frak("a")$-filtration $(M_n)$. T.F.A.E.:
  - _(a)_ $M^ast$ is a finitely generated $A^ast$-module.
  - _(b)_ The filtration $(M_n)$ is stable.

  In particular, any $frak("a")$-filtration of a finitely generated $A^ast$-module $M$ with $A$ Noetherian induces the same topology on $M$. [AM, 10.8]
]

#proof[
  Note that $M$ is a Noetherian $A$-module, so each $M_n$ is finitely generated, whence each $Q_n := plus.o.big_(i=0)^n M_n subset M^ast$ is a finitely generated $A$-module (but not in general an $A^ast$-module). However, for each $n >= 0$,
  $
    M_n^ast := Q_n plus.o ( plus.o.big_(k >= 1) frak("a")^k M_n)
  $

  is an $A^ast$-submodule of $M^ast$. Since $Q_n$ is finitely generated over $A$, and the finite set of $A$-generators of $M_n$ generates $plus.o.big_(k >= 1) frak("a")^k M_n$ over $A^ast$, it follows that $M_n^ast$ is finitely generated over $A^ast$. Now, $(M_n^ast )$ forms an ascending chain whose union is $M^ast$. Since $A^ast$ is Noetherian, we have
  $
    M^ast text("is finitely generated over") A^ast . , arrow.l.r.double text("The chain $(M_n^ ast )$ stops").; , arrow.l.r.double M^ast =M_(n_0)^ast text("for some") n_0.; , arrow.l.r.double M_(n_0+r)=frak("a")^r M_(n_0) text("for all") r >= 0.; , arrow.l.r.double text("The $frak(\"a\")$-filtration $(M_n)$ is stable").
  $

]


#proposition(number: "291", title: [Artin-Rees Lemma])[
  Let $A$ be a Noetherian ring, $M$ a finitely generated $A$-module, and $(M_n)$ a stable $frak("a")$-filtration of $M$. If $N$ is an $A$-submodule of $M$, then $(N inter M_n)$ is a stable $frak("a")$-filtration on $N$.
  In particular, taking $M_n=frak("a")^n M$, there exists an integer $k$ such that
  $
    N inter frak("a")^n M=frak("a")^(n-k)(N inter frak("a")^k M),
  $

  for all $n >= k$. [AM, 10.9-10]
]

#proof[
  Note that for any $n >= 0$,
  $
    frak("a")(N inter M_n) subset frak("a")N inter frak("a")M_n subset N inter M_(n+1),
  $

  thus $(N inter M_n)$ is an $frak("a")$-filtration. Hence it defines a graded $A^ast$-module $N^ast := plus.o.big_(n >= 0)(N inter M_n)$, which is a submodule of $M^ast$ and thus finitely generated (for $M^ast$ is Noetherian $A^ast$-module by *Lemma 290*). Again, by *(290)*, $(N inter M_n)$ is stable. For the last statement, we note that $(M_n)=(frak("a")^n M)$ is a stable $frak("a")$-filtration.
]


#theorem(number: 292)[
  Let $A$ be a Noetherian ring, $M$ a finitely generated $A$-module, and $N$ an $A$-submodule of $M$. Then the filtrations $(frak("a")^n N)$ and $(N inter frak("a")^n M)$ have bounded difference. In particular, the $frak("a")$-topology of $N$ coincides with the topology induced by the $frak("a")$-adic topology of $M$. [AM, 10.11]
]

#proof[
  Clearly, $(frak("a")^n N)$ is a stable $frak("a")$-filtration, thus the results follows from *(289)*. Coinciding topology follows from the fact that in a bounded difference we can always find an open neighbourhood of one topology which is contained in an open neighbourhood of the other topology.
]


#proposition(number: 293)[
  Let
  $
    0 -> M' -> M -> M'' -> 0
  $

  be an exact sequence of finitely generated modules over a Noetherian ring $A$. Then the sequence of $frak("a")$-adic completions
  $
    0 -> hat(M)'_frak("a") -> hat(M)_frak("a") -> hat(M)''_frak("a") -> 0
  $

  is exact. [AM, 10.12]
]

#proof[
  We have seen from *(236)* that if $(M_n)$ is an $frak("a")$-filtration of $M$, then completing $M', M''$ by $(M' inter M_n), (p(M_n))$, respectively, yields the exactness at the level of completions. Since $p:M arrow.r.twohead M''$ is $A$-linear, from some sufficiently large $k$, we have
  $
    frak("a")p(M_n) subset p(M_(n+1))=p(frak("a")M_n) subset frak("a")p(M_n), quad forall n >= k.
  $

  Thus, $(p(M_n))$ is stable and it follows from *(289)* that this induces the same $frak("a")$-topology, so that the completions with respect to these filtrations are isomorphic.
]


The completion $hat(A)$ is a natural $A$-algebra via the completion map $A -> hat(A)$. In particular, given an $A$-module $M$, we can form the $hat(A)$-module $hat(A) times.o_(hat(A))M$. Since $hat(M)$ is an $hat(A)$-module by design, we get the sequence of $hat(A)$-modules
$
  hat(A) times.o_A M -> hat(A) times.o_A hat(M) -> hat(M)=hat(A) times.o_(hat(A)) hat(M).
$

This behaves particularly well for $A$ Noetherian and finitely generated $M$.

#proposition(number: 294)[
  If $M$ is finitely generated, then $hat(A) times.o_A M -> hat(M)$ is surjective. If, in addition, $A$ is Noetherian, then $hat(A) times.o_A M -> hat(M)$ is an isomorphism. [AM, 10.13]
]

#proof[
  Since $M$ is finitely generated, we have an exact sequence $0 -> N -> F -> M -> 0$ for a free $A$-module $F equiv A^n$. By the exactness of the completion functor *(236)* it follows that $frak("a")$-adic completion commutes with finite direct sums. Hence
  $
    hat(A) times.o_A F equiv (hat(A) times.o_A A)^n equiv (hat(A))^n equiv hat(F).
  $

  This gives rise to the commutative diagram
  #align(center)[#diagram(
    cell-size: 15mm,
    $
      & hat(A) times.o_A N edge("r", ->) edge("d", gamma, ->)
      & hat(A) times.o_A F edge("r", ->) edge("d", beta, ->)
      & hat(A) times.o_A M edge("r", ->) edge("d", alpha, ->) & 0 \
      0 edge("r", ->) & hat(N) edge("r", ->) & hat(F) edge("r", delta, ->)
      & hat(M) edge("r", ->) & 0
    $,
  )]
  in which the top row is exact (for $hat(A) times.o_A-$ is a right exact functor) and the bottom row is exact by *(236)*. Hence $delta$ is surjective. Since $beta$ is an isomorphism, it follows that $alpha$ is surjective, whence the first assertion.\
  Now, if $A$ is Noetherian, then $N$ is also finitely generated so that $gamma$ is also surjective, and that the bottom row is exact by *(293)*. A standard diagram chasing argument implies that $alpha$ is injective, thus an isomorphism.
]


#proposition(number: 295)[
  If $A$ is a Noetherian ring, then the functor $T_(hat(A)) := hat(A) times.o_A-$ is exact on the category of finitely generated $A$-modules. In particular, the $frak("a")$-adic completion $hat(A)$ of $A$ is a flat $A$-algebra. [AM, 10.14]
]

#proof[
  Since $A$ is Noetherian, it follows from *(293-294)* that the functor $T_(hat(A))=hat(A) times.o_A dot equiv hat(dot)$ is an exact functor on the category of finitely generated $A$-modules.
]


Next, we study the ring theoretic properties of $hat(A)$ in more detail.
#lemma(number: 296)[
  If $A$ is Noetherian with $frak("a")$-adic completion $hat(A)$. Then
  - _(a)_ $hat(frak("a")) equiv hat(A) times.o_A frak("a") equiv hat(A) frak("a")=frak("a")^e$.
  - _(b)_ $hat(frak("a")^n)=(hat(frak("a")))^n$.
  - _(c)_ $hat(A)/hat(frak("a"))^n equiv A/frak("a")^n$ and $hat(frak("a"))^n/hat(frak("a"))^(n+1) equiv frak("a")^n/frak("a")^(n+1)$.
  - _(d)_ $hat(frak("a")) subset frak("R")(hat(A))$, the Jacobson radical of $hat(A)$. [AM, 10.15]

  *Recall.* The *Jacobson radical* of a ring $A$ is defined $frak("R")(A) := inter.big {frak("m") lt.closed A: text("maximal")}$.
]

#proof[
  (i) Since $A$ is Noetherian, $frak("a")$ is finitely generated so that we have $hat(A) times.o_A frak("a") equiv hat(frak("a"))$ by *(294)*. Moreover, $hat(A)$ is flat by *(295)*, it follows that the injection $0 -> frak("a") arrow.r.hook A$ induces an injection
  $
    0 -> frak("a") times.o_A hat(A) arrow.r.hook A times.o_A hat(A) equiv hat(A), x times.o a mapsto x dot a,
  $

  and thus $frak("a") times.o_A hat(A) equiv frak("a") dot hat(A)=frak("a")^e$.\ (ii) Applying (i) to $frak("a")^n$, we see that
  $
    hat(frak("a")) equiv frak("a")^n dot hat(A)=(frak("a")^n)^e=(frak("a")^e)^n equiv (hat(frak("a")))^n.
  $

  (iii) We showed the first assertion in *(237)*. Further, completing the exact sequence $0 -> frak("a")^(n+1) -> frak("a")^n -> frak("a")^n/frak("a")^(n+1) -> 0$ gives the second isomorphism.\
  (iv) For any $x in hat(frak("a"))$, the sequence $a_n= sum_(i=0)^n x^i$ is Cauchy in $A$ with respect to its $frak("a")$-topology and thus converges in $hat(A)$. For its limit we have $(1-x) dot sum_(i=0)^oo x^i=1$, i.e. $1-x$ is a unit. Since $hat(frak("a"))$ is an ideal, we can prove that $1-a x$ is a unit for all $a in hat(A)$. Hence, if $x$ were not in some maximal ideal $hat(frak("m"))$, we have $(x)+hat(frak("m"))=(1)$, whence $hat(frak("m"))=hat(A). ( -> arrow.l )$. Therefore $x in frak("R")(hat(A))$.
]


#corollary(number: 297)[
  Let $(A,frak("m"))$ be a Noetherian local ring. Then the $frak("m")$-adic completion $hat(A)$ of $A$ is a local ring with maximal ideal $hat(frak("m"))$. [AM, 10.16]
]

#proof[
  By *(296c)* we have $hat(A)/hat(frak("m")) equiv A/frak("m")$, thus $hat(A)/hat(frak("m"))$ is a field and it follows that $hat(frak("m"))$ is maximal, so $frak("R")(hat(A)) subset hat(frak("m"))$. On the other hand, we have seen in *(296d)* that $hat(m) subset frak("R")(hat(A))$, hence we have the equality and so $hat(frak("m"))$ is the unique maximal ideal. Therefore $(hat(A),hat(frak("m")))$ is local.
]


#corollary(number: 298)[
  Let $A$ be a Noetherian ring and $frak("a")=(a_1, dots.h.c ,a_n) lt.closed A$ be an ideal. Then the $frak("a")$-adic completion is
  $
    hat(A)_frak("a") equiv A ⟦x_1, dots.h.c ,x_n⟧/(x_1-a_1, dots.h.c ,x_n-a_n).
  $

  In particular, the completion of $A=K[x_1, dots.h.c ,x_n]/frak("a")$ for some field $K$ and ideal $frak("a") subset.not.eq K[x_1, dots.h.c ,x_n]$ with respect to the maximal ideal $((x_1-a_1, dots.h.c ,x_n-a_n)+frak("a"))/frak("a")$ is
  $
    hat(A)_frak("p") equiv K ⟦x_1, dots.h.c ,x_n⟧/frak("a") dot K ⟦x_1, dots.h.c ,x_n⟧.
  $

]


#theorem(number: "299", title: [Cohen Structure Theorem])[
  If $(A,frak("m"))$ is a complete regular local ring of dimension $n$ containing some field, then $A equiv k ⟦x_1, dots.h.c ,x_n⟧$, (the ring of formal power series over the residue field $k=A/frak("m")$ of $A$).
]

#proof[
  See [Commutative Ring Theory, H.Matsumura, Thm. 29.8].
]


#theorem(number: "300", title: [Krull's Intersection Theorem])[
  \ Let $A$ be a Noetherian ring, $M$ a finitely generated $A$-module and $hat(M)$ the $frak("a")$-completion of $M$. Then the kernel $E= inter.big_(n=1)^oo frak("a")^n M$ of the completion map $M -> hat(M)$ consists of those $x in M$ annihilated by some element of $1+frak("a")$. [AM, 10.17]
]

#proof[
  "$supset$"\ If $(1-a)x=0$ for some $a in frak("a")$, then
  $
    x=a x=a^2 x= dots.h.c in inter.big_(n=1)^oo frak("a")^n M=E.
  $

  "$subset$"\ Since $E$ is the intersection of all neighbourhoods of $0 in M$, the subspace topology induced on $E$ is trivial, i.e. $E$ is the only neighbourhood of $0 in E$. By *Artin-Rees*, the induced topology on $E$ coincides with its $frak("a")$-topology. In particular, since $frak("a")E$ is a neighbourhood of $0$ in the $frak("a")$-topology, it follows that $frak("a")E=E$. Since $M$ is finitely generated and $A$ is Noetherian, $E$ is also finitely generated, whence by [AM, 2.5], $(1-a)E=0$ for some $a in frak("a")$.
]


#remark(number: 301)[
  *Krull's Thm.* may fail when $A$ is not Noetherian\
  proof. Consider $cal("C")^oo (bb("R"))$ and let $cal("P")$ be the maximal ideal of functions vanishing at the origin. By _Taylor's Thm._, $cal("P")=(x)$ so that $E= inter.big cal("P")^k$ consists of functions whose derivative at the origin vanishes up to any order. On the other hand, $f in cal("C")^oo (bb("R"))$ is annihilated by some element in $1+cal("P")$ iff $f$ vanishes identically near $0$. However, $f=e^(-1/x^2) in N$ does not vanish for $x>0$.
]


#corollary(number: 302)[
  Let $A$ be a Noetherian integral domain and $frak("a") lt.closed.not A$ an ideal. Then $inter.big_(n=1)^oo frak("a")^n=0$. In particular, the $frak("a")$-topology on $A$ is Hausdorff. [AM, 10.18]
]

#proof[
  The ideal $1+frak("a")$ contains no nonzero zero-divisors as $A$ is an integral domain. The last assertion follows from *(A.5)*.
]


#corollary(number: 303)[
  Let $A$ be a Noetherian ring, $frak("a") lt.closed A$ an ideal containing in the Jacobson radical $frak("R")(A)$ and $M$ a finitely generated $A$-module. Then the $frak("a")$-topology of $M$ is Hausdorff, i.e. $inter.big frak("a")^n M=0$. In particular, this applies to the situation of a Noetherian local ring $(A,frak("m"))$ with the $frak("m")$-topology on $M$. [AM, 10.19-20]
]

#proof[
  Since $frak("a") subset frak("R")(A)$, every element of $1+frak("a")$ is a unit, (cf. [AM, 1.9]). Otherwise, $1+a, (a in frak("a"))$, is contained in some maximal ideal $frak("m") lt.closed A$. Since $a in frak("a") subset frak("m")$, we have $1 in frak("m"). ( -> arrow.l )$. But if $1+a$ is a unit, $x mapsto (1+a) dot x$ has trivial kernel.
]


Our final aim is to show that the $frak("a")$-adic completion of a Noetherian is again Noetherian.
#definition(number: "304", title: [Associated Graded Ring])[
  \ Let $A$ be a ring and $frak("a") lt.closed A$ an ideal. We define the *associated graded ring* of $A$ by
  $
    op("Gr")_frak("a")(A)= plus.o.big_(n >= 0) op("Gr")_(frak("a"),n)(A) := plus.o.big_(n >= 0) frak("a")^n/frak("a")^(n+1), quad (frak("a")^0=A).
  $

  If the underlying ideal $frak("a")$ is clear from the context, we simply write $op("Gr")(A)$. This is indeed a graded ring in the sense: if $x_n in frak("a")^n$ and $x_m in frak("a")^m$, then
  $
    (x_n+frak("a")^(n+1)) dot (x_m+frak("a")^(m+1)) := x_n x_m+frak("a")^(n+m+1).
  $

  Similarly, if $M$ is an $A$-module with $frak("a")$-filtration $(M_n)$, we define
  $
    op("Gr")(M)= plus.o.big_(n >= 0) op("Gr")_n(M) := plus.o.big_(n >= 0)M_n/M_(n+1).
  $

  This is a graded $op("Gr")(A)$-module. We write $op("Gr")_frak("a")(M)$ if $M_n=frak("a")^n M$ is the $frak("a")$-adic filtration.
]


For example, if $A$ is Noetherian and $frak("a")=(x_1, dots.h.c ,x_r)$, then
$
  op("Gr")(A)=(A/frak("a"))[overline(x)_1, dots.h.c ,overline(x)_r], quad text("(where $overline(x)_i := x_i+frak(\"a\")^2)$").
$

proof. Indeed, $op("Gr")_(frak("a"),n)(A)=frak("a")^n/frak("a")^(n+1)$ is finitely generated as an $A/frak("a")$-module by $(overline(x)_1^n, dots.h.c ,overline(x)_r^n)$. Hence
$
  op("Gr")(A)= plus.o.big_(n >= 0)(overline(x)_1^n, dots.h.c ,overline(x)_r^n)=(A/frak("a"))[overline(x)_1, dots.h.c ,overline(x)_r].
$


#proposition(number: 305)[
  Let $A$ be a Noetherian ring and $frak("a") lt.closed A$ an ideal. Then
  - _(a)_ $op("Gr")_frak("a")(A)$ is Noetherian.
  - _(b)_ $op("Gr")_frak("a")(A)$ and $op("Gr")_(hat(frak("a")))(hat(A))$ are isomorphic as graded rings.
  - _(c)_ $op("Gr")(M)$ is a finitely generated graded  $op("Gr")_frak("a")(A)$-module if $M$ is a finitely generated $A$-module and $(M_n)$ is a stable $frak("a")$-filtration of $M$.
  - _(d)_ In particular, $op("Gr")_frak("a")(M)$ is a finitely generated graded $op("Gr")_frak("a")(A)$-module if $M$ is a finitely generated $A$-module. [AM, 10.22]

]

#proof[
  (a) Since $A$ is Noetherian, $frak("a")$ is finitely generated, say by $x_1, dots.h.c ,x_r$. From the discussion above, we have $op("Gr")(A)=(A/frak("a"))[overline(x)_1, dots.h.c ,overline(x)_r]$. As $A/frak("a")$ is Noetherian, $op("Gr")(A)$ is also Noetherian by *Hilbert Basis Thm*.\
  (b) Recall from *(296c)* that $frak("a")^n/frak("a")^(n+1) equiv hat(frak("a"))^n/hat(frak("a"))^(n+1)$. The result follows from the definition.\
  (c) Since $(M_n)$ is stable, there exists $k in bb("N")$ such that $M_(k+r)=frak("a")^r M_k, forall r >= 0$, hence $op("Gr")(M)$ is generated by $plus.o.big_(n <= k) op("Gr")_n(M)$ as a $op("Gr")(A)$-module. Furthermore, each $op("Gr")_n(M)=M_n/M_(n+1)$ is Noetherian and annihilated by $frak("a")$, and hence a finitely generated $A/frak("a")$-module, which follows that $plus.o.big_(n <= k) op("Gr")_n(M)$ is generated by a finite number of elements (as an $A/frak("a")$-module). Hence $op("Gr")(M)$ is a finitely generated $op("Gr")(A)$-module. Finally, (d) is just a special case from (c).
]


#lemma(number: 306)[
  Let $phi:M -> N$ be an $A$-linear homomorphism of *filtered modules*, i.e. $phi(M_n) subset N_n$, and let $op("Gr")(phi):op("Gr")(M) -> op("Gr")(N)$ and $hat(phi):hat(M) -> hat(N)$ be the induced homomorphisms of the associated graded and completed modules, respectively. Then
  - _(a)_ $op("Gr")(phi)$ is injective. $arrow.r.double hat(phi)$ is injective.
  - _(b)_ $op("Gr")(phi)$ is surjective. $arrow.r.double hat(phi)$ is surjective.

  In particular, $op("Gr")(M)$ and $op("Gr")(N)$ are isomorphic via such a map $phi:M -> N$, then the completions are isomorphic. [AM, 10.23]
]

#proof[
  For each $n in bb("N")$, consider the commutative diagram of exact sequences:
  #align(center)[#diagram(
    cell-size: 15mm,
    $
      0 edge("r", ->) & M_n/M_(n+1) edge("r", ->) edge("d", op("Gr")_n(phi), ->)
      & M/M_(n+1) edge("r", ->) edge("d", phi_(n+1), ->)
      & M/M_n edge("r", ->) edge("d", phi_n, ->) & 0 \
      0 edge("r", ->) & N_n/N_(n+1) edge("r", ->) & N/N_(n+1) edge("r", ->)
      & N/N_n edge("r", ->) & 0.
    $,
  )]
  This gives the exact sequence
  $
    0 -> op("ker Gr")_n(phi) -> op("ker") phi_(n+1) -> op("ker") phi_(n) \
    -> op("Coker Gr")_n(phi) -> op("Coker") phi_(n+1) -> op("Coker") phi_(n) -> 0
  $

  by _Snake Lemma_. From this we see, by induction on $n$, that\
  case 1. _$op("Gr")(phi)$ is injective_, then each $op("Gr")_n(phi)$ is injective. For $n=0$, we have $M=M_0$ and $N=N_0$, so that $phi_0:M/M={0} -> N/N={0}$ is injective, whence $phi_1$ is injective by _Short Five Lemma_. Now, proceed by induction to conclude that $phi_n$ is injective for all $n$. Finally, apply the inverse limit functor to the sequence
  $
    0 -> M/M_n attach(arrow.r.hook, t: phi_n) N/N_n arrow.r.twohead op("Coker") phi_n -> 0.
  $

  As this is a left exact functor by *(235)*, $hat(phi)$ is injective.\
  case 2. _$op("Gr")(phi)$ is surjective_, then each $op("Gr")_n(phi)$ is surjective. Similarly, we obtain by _Short Five Lemma_ that $phi_n$ is surjective for all $n$. Finally, apply the inverse limit functor to the sequence
  $
    0 -> op("ker") phi_n arrow.r.hook M/M_n attach(arrow.r.twohead, t: phi_n) N/N_n -> 0.
  $

  Moreover, the inverse system ${op("ker") phi_n }$ is surjective (from the long exact sequence), hence $hat(phi)$ is surjective by *(235)*.
]


#proposition(number: 307)[
  Let $A$ be a ring, $M$ an $A$-module, and $(M_n)$ an $frak("a")$-filtration of $M$. Suppose that $A$ is complete in the $frak("a")$-topology and that $M$ is Hausdorff in its filtration topology, (i.e. $inter.big_(n >= 0)M_n=0$). If $op("Gr")(M)$ is a finitely generated $op("Gr")(A)$-module, then $M$ is a finitely generated $A$-module. [AM, 10.24]
]

#proof[
  Let $overline(x)_i := x_i+M_(n_i+1) in op("Gr")_(n_i)(M), (x_i in M_(n_i))$ such that ${overline(x)_i }_(i=1)^nu$ is a finite set of homogeneous generators of degree $n_i$. Let $F^i$ be the module $A$ with the stable $frak("a")$-filtration given by $F_k^i=frak("a")^(k+n_i)$ and put $F := plus.o.big_(i=1)^(nu)F^i equiv A^nu$, where we endow the filtration $F_n := plus.o.big_(i=1)^(nu)F_n^i= plus.o.big_(i=1)^(nu) frak("a")^(n+n_i)$. Now, mapping the generator $a_i=1 in F^i$ to $x_i$ defines a homomorphism $phi:F -> M$ of filtered modules for $phi(frak("a")^(n-n_i)) subset frak("a")^(n-n_i)M_(n_i) subset M_n$, and that $op("Gr")(phi):op("Gr")(F) -> op("Gr")(M)$ is a surjective homomorphism of $op("Gr")(A)$-module by design. Hence $hat(phi)$ is surjective by *(306)*. Consider now the diagram
  #align(center)[#diagram(
    cell-size: 18mm,
    $
      F edge("r", phi, ->) edge("d", alpha, ->) & M edge("d", beta, ->) \
                 hat(F) edge("r", hat(phi), ->) & hat(M).
    $,
  )]
  Since $F equiv A^nu$ and $hat(A)=A$, it follows that $alpha$ is an isomorphism. As $M$ is Hausdorff, $beta$ is injective. Moreover, $hat(phi)$ is surjective, which implies that $phi$ is surjective, i.e. $M$ is finitely generated by ${x_i }_(i=1)^nu$ over $A$.
]


#corollary(number: 308)[
  With the hypothesis of *(307)*, if $op("Gr")(M)$ is a Noetherian $op("Gr")(A)$-module, then $M$ is a Noetherian $A$-module. [AM, 10.25]
]

#proof[
  We claim that every $A$-submodule $M'$ of $M$ is finitely generated. Consider the $frak("a")$-filtration $M'_n := M' inter M_n$ of $M'$, then the embedding $M'_n arrow.r.hook M_n$ gives rise to an injective homomorphism $M'_n/M'_(n+1) arrow.r.hook M_n/M_(n+1)$, and hence an embedding $op("Gr")(M') arrow.r.hook op("Gr")(M)$. Since $op("Gr")(M)$ is Noetherian, $op("Gr")(M')$ is finitely generated. Moreover, $M'$ is Hausdorff since $inter.big M'_n subset inter.big M_n=0$. Hence $M'$ is finitely generated by *(307)*.
]


#theorem(number: 309)[
  If $A$ is Noetherian, then the $frak("a")$-completion $hat(A)_frak("a")$ of $A$ is Noetherian. [AM, 10.26]
]

#proof[
  As $A$ is Noetherian, from *(305)* we know that $op("Gr")_(hat(frak("a")))(hat(A))=op("Gr")_(frak("a"))(A)$ is a Noetherian $op("Gr")_(frak("a"))(A)$-module. Now apply *(308)* to the complete ring $hat(A)$ and take $M=hat(A)$ (filtered by $(hat(frak("a"))^n)$, and so Hausdorff since $inter.big hat(frak("a"))^n=0$). Thus, $hat(A)$ is Noetherian.
]


#corollary(number: 310)[
  If $A$ is Noetherian, then the ring of formal power series $A ⟦x_1, dots.h.c ,x_n⟧$ is Noetherian. In particular, $k ⟦x_1, dots.h.c ,x_n⟧$ is Noetherian. [AM, 10.27]
]

#proof[
  Note that $A ⟦x_1, dots.h.c ,x_n⟧$ is the completion (under the $(x_1, dots.h.c ,x_n)$-adic topology) of $A[x_1, dots.h.c ,x_n]$, which is Noetherian by *Hilbert Basis Thm*.
]
