#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge

#definition(number: "1", title: [Topological Group])[
  \ A *topological group* consists of a topological space $(G,cal("T"))$ and a group $(G, dot ,1)$, (write $(G,+,0)$ if it is abelian) such that the operation $dot :G -> G, (x,y) mapsto x dot y$ and the inversion $iota:G -> G, x mapsto x^(-1)$ are continuous.
]


In this chapter, we only consider the topological abelian group $(G,cal("T"),+,0)$:
#note(number: 2)[
  - _(a)_ Note that $iota$ is a homeomorphism, for each neighbourhood $U in cal("N")_0$, we also have $-U=iota(U) in cal("N")_0$. Now, set $V := U inter -U in cal("N")_0$, then we have $V=-V$.
  - _(b)_ Since $+$ is continuous and sends $(0,0) mapsto 0$, for any neighbourhood $U in cal("N")_0$, there is a neighbourhood $W subset G times G$ of $(0,0)$ such that $+:W arrow.r.hook U$. By the definition of product topology, there are $V_1,V_2 in cal("N")_0$ such that $V_1 times V_2 subset W$.\ Now, set $V := V_1 inter V_2 in cal("N")_0$, then we have $V+V subset U$.

]


#lemma(number: 3)[
  If ${0}$ is closed in $G$, then the diagonal $D := {(x,x):x in G}$ is closed in $G$. Hence $G$ is Hausdorff.
]

#proof[
  Note that the map
  $
    kappa:G times G arrow.r.long G times G, (x,y) arrow.r.long.bar (x,-y)
  $

  is continuous since $mu=(1_G, iota)$. It follows that the map
  $
    phi:G times G arrow.r.long G, (x,y) arrow.r.long.bar x-y
  $

  is continuous since $phi=+ compose mu$. Hence by assumption $D=phi^(-1)(0)$ is closed in $G times G$.
]


#proposition(number: 4)[
  - _(a)_ If $a$ is a fixed element of $G$, the *translation* defined by
  $
    T_a:G arrow.r.long G, x arrow.r.long.bar x+a
  $

  is a homeomorphism.
  - _(b)_ If $U in cal("N")_0$ is any neighbourhood, then $a+U in cal("N")_a$; conversely, if $V in cal("N")_a$, then $V$ is of the form $V := a+U$ for some $U in cal("N")_0$.

  *Remark.* The topology of $G$ is thus uniquely determined by the neighbourhoods of $0$ in $G$.
]

#proof[
  (a) Note that $T_a=+ compose kappa$, where $kappa:G arrow.r.hook G times G, x mapsto (x,a)$ is continuous. Hence $T_a$ is continuous. Moreover,  $(T_a)^(-1)=T_(-a)$ is also continuous, whence $T_a$ is a homeomorphism.\
  (b) Since $T_(-a)(a)=0$ and the map $T_(-a)$ is continuous, it follows that $a+U=(T_(-a))^(-1)(U) in cal("N")_a$. Conversely, since $T_a(0)=a$ and $T_a$ is continuous, $U := T_a^(-1)(V) in cal("N")_0$. Moreover, $T_a$ is a homeomorphism, thus $V=T_a compose U=a+U$.
]


#lemma(number: 5)[
  Let $H := inter.big_(U in cal("N")_0(G))U$. Then
  - _(a)_ $H$ is a subgroup of $G$.
  - _(b)_ $H$ is the closure of ${0}$.
  - _(c)_ $G/H$ is Hausdorff.
  - _(d)_ $G$ is Hausdorff $arrow.l.r.double.long H=0$. $quad$ [AM, 10.1]

]

#proof[
  (a) This follows from the continuity of group operations and *Note 2*. \ For (b) we have:
  $
    x in H arrow.l.r.double x in U, forall U in cal("N")_0(G) arrow.l.r.double 0 in x-U, forall U in cal("N")_0(G) arrow.l.r.double x in overline({0}).
  $

  (c) From (b) the cosets of $H$ are all closed, thus points are closed in $G/H$ and so $G/H$ is Hausdorff. (d) By definition of Hausdorff and construction of $H$, it's clear that $H=0$; the converse is trivial.
]


#definition(number: "6", title: [Convergent & Cauchy Sequences])[
  - A sequence $(a_n)$ in $A$ *converges* converges to $0$ if for all $U in cal("N")_0$ there exists $N in bb("N")$ with $a_n in U$ provided $n >= N$. In this case we write $a_n arrow.r.long 0$.
  - A *Cauchy sequence* $(a_n)$ in $A$ is a sequence such that for all $U in cal("N")_0$ there exists $N in bb("N")$ with $a_i-a_j in U$ provided $i,j >= N$. Moreover, two Cauchy sequences $(a_n)$ and $(b_n)$ are *equivalent*, write $(a_n) tilde (b_n)$, if $(a_n-b_n)$ converges to $0$.

]


#lemma(number: 7)[
  The relation $tilde$ of Cauchy sequences in $G$ is an equivalence relation.
]

#proof[
  - $(x_i) tilde (x_i)$ since $x_i-x_i=0 arrow.r.long 0$.
  - If $(x_i) tilde (y_i)$, then $x_i-y_i arrow.r.long 0$. Since the map $iota:G -> G, x mapsto -x$ is continuous, it follows that
  $
    y_i-x_i=iota(x_i-y_i) arrow.r.long iota(0)=0,
  $

  whence $(y_i) tilde (x_i)$.
  - Now, suppose $(x_i) tilde (y_i)$ and $(y_i) tilde (z_i)$. For any neighbourhood $U in cal("N")_0$, we take $V in cal("N")_0$ such that $V+V subset U$. By assumption, there exist $N_1,N_2 in bb("N")$ such that
  $
    x_i-y_i in V, forall i >= N_1 quad text("and") quad y_i-z_i in V, forall i >= N_2.
  $

  Take $N := op("max"){N_1,N_2 }$, then for any $i >= N$, we have
  $
    x_i-z_i=(x_i-y_i)+(y_i-z_i) in V+V subset U.
  $


]


#definition(number: "8", title: [Completion])[
  In the following, we assume for simplicity that $0 in G$ has a _countable local base_. We define the *completion* of $G$ by
  $
    hat(G) := text("Cauchy sequences in $G$")\/ tilde .
  $

]


#proposition(number: 9)[
  Let $(x_i)$ and $(y_i)$ be Cauchy sequences in a topological abelian group $G$. Then
  - _(a)_ $(x_i+y_i)$ is a Cauchy sequence and its class in $hat(G)$ depends only on the classes of $(x_i)$ and $(y_i)$.
  - _(b)_ $(-x_i)$ is a Cauchy sequence and its class in $hat(G)$ depends only on the class of $(x_i)$.
  - _(c)_ $(0)$ is a Cauchy sequence.
  - _(d)_ We thus obtain an addition $+$ in $hat(G)$ making it an abelian group.

]

#proof[
  (a) For any neighbourhood $U in cal("N")_0$, we take $V in cal("N")_0$ such that $V+V subset U$. Since $(x_i)$ and $(y_i)$ are Cauchy, there exist $N_1,N_2 in bb("N")$ such that
  $
    x_i-x_j in V, forall i,j >= N_1 quad text("and") quad y_i-y_j in V, forall i >= N_2.
  $

  Take $N := op("max"){N_1,N_2 }$, then for any $i,j >= N$, we have
  $
    (x_i+y_i)-(x_j-y_j)=(x_i-x_j)+(y_i-y_j) in V+V subset U.
  $

  Now, if $overline((x'_i))=overline((x_i))$, then $x_i-x'_i arrow.r.long 0$. Note that
  $
    (x_i+y_i)-(x'_i+y_i)=x_i-x'_i arrow.r.long 0,
  $

  whence $(x_i+y_i) tilde (x'_i+y_i)$. Similarly, if $overline((y'_i))=overline((y_i))$, we have $(x'_i+y_i) tilde (x'_i+y'_i)$. By transitivity $(x_i+y_i)$ and $(x'_i+y'_i)$ are equivalent.\
  (b) For any $U in cal("N")_0$, since $(x_i)$ is Cauchy, there is $N in bb("N")$ such that $x_i-x_j in U$ if $i,j >= N$. Now, we have
  $
    (-x_i)-(-x_j)=x_j-x_i in U, quad forall i,j >= N.
  $

  Hence $(-x_i)$ is also Cauchy. If $(x'_i)$ represents the same class as $(x_i)$, so that $x_i-x'_i arrow.r.long 0$, then $(-x_i)-(-x'_i) arrow.r.long 0$ as well; for any $U in cal("N")_0$, we may find $V in cal("N")_0$ with $V=-V subset U$ and some $N in bb("N")$ such that $x_i-x'_i in V=-V, forall i >= N$, thus
  $
    (-x_i)-(-x'_i)=-(x_i-x'_i) in V subset U,
  $

  i.e. $(-x'_i) tilde (-x_i)$.\
  (c) Clearly, since all differences are zero.\
  (d) By the above facts on independence of representatives, it will be enough to show that the set of Cauchy sequences in $G$ forms an abelian group. But this easily follows from the facts that this group is defined as a subgroup of the product group $G^bb("N")$ and that the abelian group identities hold componentwise:
  $
    ,op("bullet") [(x_i)+(y_i)]+(z_i)= (x_i+y_i)+(z_i)=(x_i+y_i+z_i) =(x_i)+(y_i+z_i)=(x_i)+[(y_i)+(z_i)]; ,op("bullet") (x_i)+(0)=(x_i+0)=(x_i); ,op("bullet") (x_i)+(-x_i)=(x_i-x_i)=(0); ,op("bullet") (x_i)+(y_i)=(x_i+y_i)=(y_i+x_i)=(y_i)+(x_i).
  $

]


#proposition(number: 10)[
  There is a natural topology making $hat(G)$ a topological group.
]

#proof[
  For each $U in cal("N")_0$, we define $hat(U) subset hat(G)$ to be the set of all elements $hat(x) in hat(G)$ such that all representatives $(x_i)$ of $hat(x)$ are "eventually" in $U$, i.e.
  $
    hat(U) := {hat(x) in hat(G): forall (x_i) in hat(x), exists N in bb("N") text("with") x_i in U, forall i >= N}.
  $

  Note that for all $U,V in cal("N")_0(G)$, we have $hat(0) in hat(U inter V)=hat(U) inter hat(V)$. Now we consider the set
  $
    hat(cal("N")) := {hat(U):U in cal("N")_0(G)}
  $

  and take all translates in $hat(G)$, these sets together generate a unique topology on $hat(G)$ for which $hat(cal("N"))$ forms a _local base_ of $hat(0)$. Now we claim that the addition and inversion are continuous.\ Suppose $hat(x),hat(y) in hat(G)$ such that $hat(x)+hat(y) in W$ for some open set $W subset hat(G)$. By our definition of topology, $exists hat(U) in hat(cal("N"))$ such that $(hat(x)+hat(y))+hat(U) subset W$. Moreover, there exists $V in cal("N")_0(G)$ with $V+V subset U$. Now, if $(x_i)$ and $(y_i)$ are Cauchy sequences representing elements of $hat(V)$, then $exists N in bb("N")$ sufficiently large with $x_i,y_i in V, forall i >= N$, whence $x_i+y_i in U$. Hence, we have $hat(V)+hat(V) subset hat(U)$ and the addition
  $
    hat(+):(hat(x)+hat(V)) times (hat(y)+hat(V)) arrow.r.hook (hat(x)+hat(y))+hat(U) subset W
  $

  is continuous. Similarly, any open neighbourhood of $-hat(x)$ contains a basic open set $-hat(x)+hat(U)$. Moreover, there exists $V in cal("N")_0(G)$ with $V=-V subset U$. Then the "negative" of any sequence eventually in $V$ is also eventually in $V$. Thus $-hat(V)=hat(V)$ and the inversion
  $
    hat(iota):-(hat(x)+hat(V)) attach(arrow.r.hook, t: =) -hat(x)+hat(V) subset -hat(x)+hat(U)
  $

  is continuous.
]


#proposition(number: 11)[
  The natural map $phi:G -> hat(G), x mapsto overline((x))$, is a continuous homomorphism of abelian groups. If $phi$ is an isomorphism, we say that $G$ is *complete*.
]

#proof[
  Clearly, a constant sequence $(x)$ is a Cauchy sequence.\
  claim. $phi$ is a continuous homomorphism.
  - $phi(0)$ is the equivalence class of $(0)$, which is the zero of $hat(G)$.
  - From *Prop. 9*, we have $(x+y)=(x)+(y)$ and $(-x)=-(x)$. By taking classes we have $phi(x+y)=phi(x)+phi(y)$ and $phi(-x)-phi(x)$.
  - *(Continuity).* Let $x in G$ and consider a basic open set $phi(x)+hat(U)$ of $hat(G)$ for some $U in cal("N")_0(G)$. If $u in U$, then $exists V in cal("N")_0(G)$ such that $u+V subset U$. Now, if $(y_i) tilde (u)$ in $hat(G)$, we have "eventually" $y_i-u in V$, i.e. eventually $y_i in u+V subset U$. It follows that $phi(u) in hat(U)$ and hence $phi(x+U) subset phi(x)+hat(U)$, thus $phi$ is continuous.

]


#remark(number: 12)[
  We have $op("ker")phi= inter.big_(U_in cal("N")_0(G))U$, and so by *Lemma 5*, $phi$ is injective iff $H$ is Hausdorff.
]

#proof[
  "$subset$"\ If $x in op("ker")phi$, then $(x) tilde (0)$, i.e. $x=x-0 arrow.r.long 0$ as the index increases. Now, for any neighbourhood $U in cal("N")_0(G)$, the sequence $(x)$ is eventually in $U$, but it is constant, whence $x in U$. Hence $x in inter.big_(U in cal("N")_0(G))U$. "$supset$"\ Clearly if $x in inter.big_(U in cal("N")_0(G))U$, then the constant sequence $(x)$ converges to $0$, whence $(x) tilde (0)$, i.e. $phi(x)=(x)=(0)$.
]


#proposition(number: 13)[
  Let $G,H$ be two abelian topological group.
  - _(a)_ If $f:G -> H$ is a continuous homomorphism, then $f$ maps a Cauchy sequence in $G$ into a Cauchy sequence of $H$.
  - _(b)_ From (a), $f$ induces a continuous homomorphism $hat(f):hat(G) -> hat(H)$.
  - _(c)_ If we have $G attach(arrow.r.long, t: f) H attach(arrow.r.long, t: g) K$, then $hat(g compose f)=hat(g) compose hat(f)$.

]

#proof[
  (a) Let $(x_i)$ be a Cauchy sequence and let $U in cal("N")_0(H). because f(0)=0$ and $f$ is continuous. $therefore exists V in cal("N")_0(G)$ such that $f(V) subset U. because (x_i)$ is Cauchy. $therefore exists N in bb("N")$ such that $x_i-x_j in V, forall i,j >= N$. Now, since $f$ is a homomorphism, we have
  $
    f(x_i)-f(x_j)=f(x_i-x_j) in f(V) subset U.
  $

  Hence $(f(x_i))$ is a Cauchy sequence in $H$.\
  (b) We first show that $hat(f)$ is well-defined.
  - *(Well-defined).* If $(x_i) tilde (y_i)$ in $hat(G)$, then $x_i-y_i arrow.r.long 0$. Since $f$ is a continuous homomorphism, we have
  $
    f(x_i)-f(y_i)=f(x_i-y_i) arrow.r.long f(0)=0.
  $

  Thus, $(f(x_i)) tilde (f(y_i))$ in $hat(H)$, and so  $hat(f)(overline((x_i)))=overline((f(x_i)))=overline((f(y_i)))=hat(f)(overline((y_i)))$.
  - *(Homomorphism).* Obviously, $f$ is a homomorphism since operations on Cauchy sequences are defined componentwise and $hat(f)$ is induced by applying $f$ componentwise to Cauchy sequences.
  - *(Continuity).* Given any basic open set $hat(f)(x)+hat(V)$ in $hat(H)$, where $V in cal("N")_0(H)$. Since $f$ is continuous and $f(0)=0$, there exists $U in cal("N")_0(G)$ such that $f(U) subset V$. Now, for any Cauchy sequence $(u_i)$ eventually in $U$, the image $(f(u_i))$ is a Cauchy sequence eventually in $V$ by (a), hence $hat(f)(hat(U)) subset hat(V)$. It follows that $hat(f)(hat(x)+hat(U)) subset hat(f)(hat(x))+hat(V)$, thus $hat(f)$ is continuous.

  (c) For any Cauchy sequence $(x_i)$ in $G$, we have
  $
    hat(g compose f)((x_i)_i)=(g compose f(x_i))_i=g compose f((x_i))_i=hat(g)((f(x_i))_i)=hat(g) compose hat(f)((x_i)_i).
  $

]


From now on, we restrict ourselves to the special kind of topologies on $G$ occurring in commutative algebra:
#definition(number: 14)[
  We assume that $0 in G$ has a fundamental system of neighborhoods (local base) consisting of _subgroups_. Thus we have a sequence of subgroups
  $
    G=G_0 supset G_1 supset dots.h.c supset G_n supset dots.h.c
  $

  and $U in cal("N")_0(G)$ iff $U supset G_n$ for some $n in bb("N")$. Moreover, in such topologies the subgroups $G_n$ of $G$ are both open and closed.
]

#proof[
  (i) It is a well-defined topological group in the sense that:
  - $g+G_n subset (g+G_n) inter (g+G_m)$ for any $m <= n$.
  - Clearly, $g in g+G_n$ for any $n in bb("N")$.
  - For any $y in g+G_n$, we have $y+G_n=g+G_n+G_n=g+G_n$.
  - $iota:G -> G, x mapsto -x$ is continuous since $g+G_n arrow.r-g+G_n$.
  - $+:G times G -> G, (x,y) mapsto x+y$ is continuous since for any given $(x+y)+G_n in cal("N")_(x+y)(G)$, we have
  $
    (x+G_n) times (y+G_n) attach(arrow.r.hook, t: +) (x+y)+G_n.
  $


  (ii) If $g in G_n$, then $g+G_n in cal("N")_g(G)$. Since $g+G_n subset G_n$, it follows that $G_n$ is open. Moreover, note that the complement of $G_n$ is indeed the union of nontrivial cosets
  $
    G without G_n= union.big_(h in.not G_n)(h+G_n),
  $

  which is open since each $h+G_n$ is open. Thus, $G_n$ is also closed in $G$.
]


#definition(number: "15", title: [Coherent Sequence])[
  Suppose $(x_i)$ is a Cauchy sequence in $G$. Then the image of $x_i$ in $G/G_n$ is eventually constant, say $x_i+G_n arrow.r.long xi_n$ in $G/G_n$. If we pass from $n+1$ to $n$ it is clear that the projection $G/G_(n+1) attach(arrow.r.long, t: theta_(n+1)) G/G_n$ maps $xi_(n+1) mapsto xi_n$.\ In this case we say that $(x_i)$ induces the *coherent sequence* $(xi_n)$.
]


#remark(number: 16)[
  - It is clear that the equivalent Cauchy sequences define the same coherent sequence.
  - On the other hand, given any coherent sequence $(xi_n)$, we can construct a Cauchy sequence $(x_n)$ giving rise to it by taking $x_n in xi_n$ so that we have $x_(n+1)-x_n in G_n$.
  - $hat(G)$ can also be well-defined as the set of coherent sequences $(xi_n)$ with the obvious group structure.

]


#definition(number: "17", title: [Inverse System & Inverse Limit])[
  \ A set $I$ is *directed* by $<=$ if
  - (Reflexive) $i <= i, forall i in I$.
  - (Transitive) If $i <= j$ and $j <= k$ in $I$, then $i <= k$.
  - For any $i,j in I$, there exists $k in I$ such that both $i,j <= k$.

  Let ${A_i }_(i in I)$ be a family of (abelian) groups together with group homomorphisms ${theta_(i j):A_j -> A_i }_(i <= j)$ such that
  - $theta_(i i)=1_(A_i)$ for all $i in I$.
  - $theta_(i k)=theta_(i j) compose theta_(j k):A_k -> A_i$ whenever $i <= j <= k$.

  We also say that $(A_i, theta_(i j))$ (or simply $A_i$ for short) defines an *inverse system*. The abelian group
  $
    attach(op("lim"), b: arrow.l, br: i in I) A_i := {a in product_(i in I)A_i:a_i=theta_(i j)(a_j), forall i <= j text("in") I}
  $

  is called the *inverse limit* of the family.
]


#remark(number: 18)[
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


In this section we always consider $I=bb("N")_( >= 1)$:
#note(number: "19", title: [Completions as Inverse Limits])[
  \ Let $G$ be an (abelian) group whose topology is defined by the subgroups
  $
    G=G_0 supset G_1 supset dots.h.c supset G_n supset dots.h.c .
  $

  Let $pi_(i j):G/G_j arrow.r.twohead G/G_i, g+G_j mapsto g+G_i, (i <= j)$, be the natural projection map. Since the completion $hat(G)$ with respect to this topology equals the set of coherent sequences which is just the inverse limit of the system ${G/G_i }$, we thus obtain
  $
    hat(G) equiv attach(op("lim"), b: arrow.l) G/G_i = {a in product_(i in I)G/G_i:a_i=pi_(i j)(a_j), forall i <= j text("in") I}.
  $

]


#definition(number: 20)[
  - An inverse system ${A_i }$ is called *surjective* if for each $i, theta_i := theta_(i,i+1):A_(i+1) -> A_i$ is surjective.
  - An *exact sequence* of inverse systems
  $
    0 -> {A_i } -> {B_i } -> {C_i } -> 0
  $

  consists of a commutative diagram
  #align(center)[#diagram(
    cell-size: 20mm,
    $
      0 edge("r", ->) & A_(i+1) edge("r", ->) edge("d", theta'_(i+1), ->)
      & B_(i+1) edge("r", ->) edge("d", phi_(i+1), ->)
      & C_(i+1) edge("r", ->) edge("d", psi_(i+1), ->) & 0 \
      0 edge("r", ->) & A_i edge("r", ->) & B_i edge("r", ->) & C_i edge("r", ->) & 0
    $,
  )]
  of exact sequences where the maps $theta_(i+1), phi_(i+1)$ and $psi_(i+1)$ are provided by the inverse systems ${A_i }, {B_i }$ and ${C_i }$, respectively.

]


#proposition(number: 21)[
  If $0 -> {A_i } -> {B_i } -> {C_i } -> 0$ is an exact sequence of inverse systems, then taking inverse limit is a "left exact functor", i.e.
  $
    0 -> attach(op("lim"), b: arrow.l) A_i -> attach(op("lim"), b: arrow.l) B_i -> attach(op("lim"), b: arrow.l) C_i \
  $

  is exact. Furthermore, if ${A_i }$ is a surjective system, then
  $
    0 -> attach(op("lim"), b: arrow.l) A_i -> attach(op("lim"), b: arrow.l) B_i -> attach(op("lim"), b: arrow.l) C_i -> 0
  $

  is exact. [AM, 10.2]
]

#proof[
  For each $i$, we have the commutative diagram of groups
  #align(center)[#diagram(
    cell-size: 20mm,
    $
      0 edge("r", ->) & A_(i+1) edge("r", f_(i+1), ->) edge("d", theta_(i+1), ->)
      & B_(i+1) edge("r", g_(i+1), ->) edge("d", phi_(i+1), ->)
      & C_(i+1) edge("r", ->) edge("d", psi_(i+1), ->) & 0 \
      0 edge("r", ->) & A_i edge("r", f_i, ->) & B_i edge("r", g_i, ->) & C_i edge("r", ->) & 0
    $,
  )]
  by assumption. Let $A := product_(i)A_i$ and consider $d^A:A -> A, a_i mapsto a_i-theta_(i+1)(a_(i+1))$, then, clearly from the above definition, $op("ker")d^A= attach(op("lim"), b: arrow.l) A_i$. We define this on $B$ and $C$ similarly.\ Now, consider the diagram
  #align(center)[#diagram(
    cell-size: 20mm,
    $
      0 edge("r", ->) & A edge("r", f, ->) edge("d", d^A, ->)
      & B edge("r", g, ->) edge("d", d^B, ->)
      & C edge("r", ->) edge("d", d^C, ->) & 0 \
      0 edge("r", ->) & A edge("r", ->) & B_i edge("r", ->) & C_i edge("r", ->) & 0.
    $,
  )]
  The horizontal rows are exact since $0 -> A_i -> B_i -> C_i -> 0$ is exact for each $i$ and the diagram is commutative since
  $
    f compose d^A(a_i) = f(a_i-theta_(i+1)(a_(i+1))) \
    = (f_i(a_i-theta_(i+1)(a_(i+1))))_i \
    = (f_i(a_i)-phi_(i+1) compose f_(i+1)(a_(i+1)))_i=d^B compose f_i(a_i)
  $

  and similarly, $g compose d^B=d^C compose g$. Therefore, by *Snake Lemma*, we obtain the first result.\ Now, if ${A_i }$ is surjective, we claim that $d^A$ is surjective. Let $a := (a_i)_i in A$. Take $x_1=0$. Since $theta_2:A_2 -> A_1$ is surjective, for $-a_1 in A_1, exists x_2 in A_2$ such that $theta_2(x_2)=-a_1$. Now, $x_1=0 mapsto x_1-theta_2(a_2)=a_1$. Inductively for $i >= 2$, since $theta_(i+1)$ is surjective, for $x_i-a_i in A_i, exists x_(i+1) in A_(i+1)$ such that $theta_(i+1)(x_(i+1))=x_i-a_i$, thus $x_i mapsto x_i-theta_(i+1)(x_(i+1))=a_i$. Hence $d^A((x_i)_i)=(a_i)_i$, i.e. $d^A$ is surjective. It follows that $op("Coker")d^A=0$, thus the required result.
]


#lemma(number: 22)[
  Suppose that $0 -> M' attach(arrow.r.hook, t: i) M attach(arrow.r.twohead, t: p) M'' -> 0$ is a short exact sequence as modules. If $N subset M$ is a submodule, then
  $
    0 -> frac(M', M' inter N) attach(arrow.r.hook, t: iota) frac(M, N) attach(arrow.r.twohead, t: pi) frac(M'', p(N)) -> 0
  $

  is exact as modules.
]

#proof[
  We first prove the well-definedness of
  $
    iota:x+M' inter N mapsto i(x)+N quad text("and") quad pi:m+N mapsto p(m)+p(N)
  $

  - If $overline(x)=x+M' inter N=y+M' inter N=overline(y)$, then $x-y in M' inter N subset N. arrow.r.double i(x)-i(y)=i(x-y) in i(N) equiv N$. It follows that
  $
    iota(overline(x))=i(x)+N=i(y)+N=iota(overline(y)).
  $

  - If $m+N=n+N$, then $m-n in N. arrow.r.double p(m)-p(n)=p(m-n) in p(N)$. Thus,
  $
    pi(m+N)=p(m)+N=p(n)+N=pi(n+N).
  $


  Now, it suffices to show $iota$ is 1-1, $pi$ is onto and the exactness at $M/N$:
  - *($iota$ is 1-1).* Suppose $iota(overline(x)) := iota(x+M' inter N)=0+N$, then $i(x)=0$. Since $i$ is 1-1, we have $x=0$. Hence, $iota$ is 1-1.
  - *($pi$ is onto).* Let $x+p(N) in M''/p(N)$ where $x in M''$. Since $p$ is onto, $exists m in M$ with $p(m)=x$. Thus, $pi(m+N)=p(m)+N=x+N$.
  - *(Exactness at $M/N$).*
  $
    (subset): m+N in op("ker") pi \
    arrow.r.double p(m) in p(N) arrow.r.double exists n in N text("such that") p(m)=p(n) \
    arrow.r.double p(m-n)=0 arrow.r.double m-n in op("ker")p=op("Im")i \
    arrow.r.double exists x in M' text("such that") i(x)=m-n \
    arrow.r.double m+N=(m-n)+N=iota(x+M' inter N) in op("Im")iota; \
    (supset): m+N in op("Im")iota \
    arrow.r.double exists x in M' text("such that") m+N=iota(x+M' inter N)=i(x)+N \
    arrow.r.double pi(m+N)=pi(i(x)+N)=p(i(x))+p(N)=0+p(N) \
    arrow.r.double m+N in op("ker")pi.
  $


]


#corollary(number: 23)[
  Let $0 -> G' attach(arrow.r.hook, t: i) G attach(arrow.r.twohead, t: p) G'' -> 0$ be an exact sequence of groups. Let $G$ have the topology defined by a decreasing sequence ${G_n }$ of subgroups, and endow $G'$ and $G''$ with the induced topologies given by ${G' inter G_n }$ and ${p(G_n)}$, respectively. Then we have the exact sequence of groups
  $
    0 -> hat(G)' -> hat(G) -> hat(G)'' -> 0
  $

  completed with respect to these topologies. [AM, 10.3]
]

#proof[
  We claim that the inverse systems are exact and that ${theta_(n+1)}$ is surjective. \ For each $n in bb("N")_( >= 1)$, consider the diagram:
  #align(center)[#diagram(
    cell-size: 22mm,
    $
      0 edge("r", ->) & frac(G', G' inter G_(n+1)) edge("r", iota_(n+1), ->) edge("d", theta_(n+1), ->)
      & frac(G, G_(n+1)) edge("r", pi_(n+1), ->) edge("d", phi_(n+1), ->)
      & frac(G'', p(G_(n+1))) edge("r", ->) edge("d", psi_(n+1), ->) & 0 \
      0 edge("r", ->) & frac(G', G' inter G_n) edge("r", iota_n, ->)
      & frac(G, G_n) edge("r", pi_n, ->) & frac(G'', p(G_n)) edge("r", ->) & 0
    $,
  )]
  - *(Commutative).*
  $
    phi_(n+1) compose iota_(n+1)(x+G' inter G_(n+1)) \
    = phi_(n+1)(i(x)+G_(n+1))=i(x)+G_n \
    = iota_n(x+G' inter G_n) \
    = iota_n compose theta_(n+1)(x+G' inter G_(n+1)); \
    psi_(n+1) compose pi_(n+1)(g+G_(n+1)) \
    = psi_(n+1)(p(g)+p(G_(n+1)))=p(g)+p(G_n) \
    = pi_n(g+G_n) \
    = pi_n compose phi_(n+1)(g+G_(n+1)).
  $

  - *(Exactness).* It follows from the previous lemma for each $n >= 1$.
  - *(Surjective).* For $theta_(n+1):frac(G', G' inter G_(n+1)) -> frac(G', G' inter G_n), x+G' inter G_(n+1) mapsto x+G' inter G_n$, we note that:
  $
    x in G' inter G_(n+1) in op("ker") theta_(n+1) \
    arrow.l.r.double x+G' inter G_n=0+G' inter G_n \
    arrow.l.r.double x in G' inter G_n \
    arrow.l.r.double x in frac(G' inter G_n, G' inter G_(n+1)).
  $

  It follows that $op("ker") theta_(n+1)=frac(G' inter G_n, G' inter G_(n+1))$. Hence, $op("Im") theta_(n+1) equiv frac(G'/G' inter G_(n+1), op("ker") theta_(n+1)) equiv frac(G', G' inter G_n)$, i.e. $theta_(n+1)$ is surjective.

  Therefore by *Prop. 21*,
  #align(center)[#diagram(
    cell-size: 22mm,
    $
      0 edge("r", ->) & attach(op("lim"), b: arrow.l) frac(G', G' inter G_n) edge("r", ->) edge("d", equiv, ->)
      & attach(op("lim"), b: arrow.l) frac(G, G_n) edge("r", ->) edge("d", equiv, ->)
      & attach(op("lim"), b: arrow.l) frac(G'', p(G_n)) edge("r", ->) edge("d", equiv, ->) & 0 \
      0 edge("r", ->) & hat(G)' edge("r", ->) & hat(G) edge("r", ->) & hat(G)'' edge("r", ->) & 0
    $,
  )]
  is exact.
]


#remark(number: 24)[
  - _(a)_ If we apply the previous corollary with $G'=G_n$ and $G''=G/G_n$, then $G''$ has the discrete topology.
  - _(b)_ We may deduce that $hat(G)''=G''$, i.e. $G''$ is complete.

]

#proof[
  (a) For any $g+G_n in G/G_n, (g in G)$. Since $G_n$ is open in $G$ (with the topology), its translation $g+G_n$ is also open in $G$, whence the singleton ${g+G_n }$ is open in $G/G_n$. Therefore $G''=G/G_n$ is discrete.\
  (b) We claim that $phi:G'' -> hat(G)''$ is an isomorphism. But from the previous discussion we already know $phi$ is a surjective group homomorphism. It remains to show that $phi$ is 1-1.\ From (a), $G''$ is discrete, thus Hausdorff, and hence by *Rmk. 12*, $phi$ is 1-1.
]


#corollary(number: 25)[
  (a) $hat(G)_n$ is a subgroup of $hat(G)$; (b) $hat(G)/hat(G)_n equiv G/G_n$; (c) $hat(hat(G)) equiv hat(G)$. [AM, 10.4-5]
]

#proof[
  (a)(b) Note that $0 -> G_n arrow.r.hook G arrow.r.twohead G/G_n -> 0$ is exact. Apply *Cor. 23*, we have
  $
    0 -> hat(G)_n arrow.r.hook hat(G) arrow.r.twohead hat(G/G_n) -> 0.
  $

  Thus, $hat(G)_n subset hat(G)$ is a subgroup and $hat(G)/hat(G)_n equiv hat(G/G_n) equiv G/G_n$.\
  (c) It follows from the completions as inverse limits and (b) that:
  $
    hat(hat(G)) equiv attach(op("lim"), b: arrow.l) hat(G)/hat(G)_n equiv attach(op("lim"), b: arrow.l) G/G_n equiv hat(G).
  $

]
