#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Discriminants

#definition(number: "107", title: [Discriminants])[
  Let $V$ be a finite dimensional $K$-vector space and $psi:V times V -> K$ a bilinear symmetric form. Fixing a basis ${e_1, dots.h.c ,e_n }$ represents $psi$ as the matrix $[psi(e_i, e_j)]$. The *discriminant* of this basis is then defined by
  $
    D(e_1, dots.h.c ,e_n) := op("det")[psi(e_i, e_j)].
  $

  If $f_i := sans("T")e_i$ obtained by the transformation $sans("T"):V -> V, forall 1 <= i <= n$, then
  $
    D(f_1, dots.h.c ,f_n)=(op("det") sans("T"))^2 dot D(e_1, dots.h.c ,e_n).
  $

  For instance, let $L/K$ be finite. We consider the bilinear symmetric form
  $
    psi:L times L -> K, (alpha,beta) mapsto op("Tr")_(L/K)(alpha beta).
  $

  More generally, this definition applies to a finite ring extension $A subset B$ with $B tilde.equiv A^m$.\ The *discriminant of elements* $beta_1, dots.h.c ,beta_m in B$ is given by
  $
    D(beta_1, dots.h.c ,beta_m) := op("det")(op("Tr")_(B/A)(beta_i beta_j)).
  $

  Since two bases are related by a transformation $sans("T")$ with $op("det") sans("T") in A^ast$, this defines a nontrivial ideal $op("disc")(B/A)$ in $A$, called the *discriminant* of $B$ over $A$. In particular, $op("disc")(B/bb("Z")) in bb("Z")$ is a well-defined integer, (since $1$ is the only square of a unit in $bb("Z")$).
]


#proposition(number: 108)[
  Let $A subset B$ be integral domains such that $B tilde.equiv A^m$ and $op("disc")(B/A) eq.not 0$.\ Then elements $b_1, dots.h.c ,b_m in B$ form a basis as an $A$-module iff as ideals in $A$, we have
  $
    D(b_1, dots.h.c ,b_m)= op("disc")(B/A).
  $

]

#proof[
  Let ${e_1, dots.h.c ,e_m }$ be an $A$-basis for $B$. For each $i$, we write $b_i := sum a_(i j)e_j, (a_(i j) in A)$. Then
  $
    D(b_1, dots.h.c ,b_m)= op("det")(a_(i j))^2 dot D(e_1, dots.h.c ,e_m).
  $

  Note that $op("det")(a_(i j))$ is a unit $arrow.l.r.double {b_1, dots.h.c ,b_n }$ is an $A$-basis for $B$.
]


#remark(number: 109)[
  If $A=bb("Z")$ and $B tilde.equiv bb("Z")^m$, then $b_1, dots.h.c ,b_m in B$ generates a submodule $N$ of finite index $(B:N)$ in $B$ iff $D(b_1, dots.h.c ,b_m) eq.not 0$. In this case
  $
    D(b_1, dots.h.c ,b_m) = (B:N)^2 dot op("disc")(B/ bb("Z"))
  $

]

#proof[
  It is well-known from the theory of finite $bb("Z")$-modules that $op("det")(a_(i j))=(B:N)$, where $b_i= sum a_(i j)e_j$ and $op("disc")(B/bb("Z"))=op("det")(op("Tr")_(B/bb("Z"))(e_i e_j))$. (cf. proof of *Prop. 108*.)
]


#proposition(number: 110)[
  Let $L/K$ be a finite separable field extension of degree $[L:K]=m$, and $sigma_1, dots.h.c ,sigma_m in op("Hom")_K(L,overline(K))$ be the distinct $K$-homomorphisms of $L$ into the algebraic closure of $K$. Then, for any $K$-basis ${beta_1, dots.h.c ,beta_m }$ of $L$,
  $
    D(beta_1, dots.h.c ,beta_m) =op("det")(sigma_i(beta_j))^2 eq.not 0.
  $

  In particular, $psi:L times L -> K$ from *Def. 107* is non-degenerate.
]

#proof[
  By direct calculation, we have
  $
    D(beta_1, dots.h.c ,beta_m) ,attach(=, t: text("def.")) op("det") (op("Tr")_(B/A)(beta_i beta_j)) =op("det")( sum_k sigma_k(beta_i beta_j)) =op("det")( sum_k sigma_k(beta_i) sigma_k(beta_j)) ; , =op("det")(sigma_k(beta_i)) dot op("det")(sigma_k(beta_j)) =op("det")(sigma_k(beta_i))^2.
  $

  Suppose $op("det")(sigma_i(beta_j))=0$. Then there exist $c_1, dots.h.c ,c_m in overline(K)$ such that $sum_i c_i sigma_i(beta_j) =0, forall j$.
]


#corollary(number: 111)[
  Let $A$ be an integral domain, $K := op("Quot")(A)$ and $L/K$ a finite separable extension of degree $m$. If the integral closure $B$ of $A$ in $L$ satisfies $B tilde.equiv A^m$, then $op("disc")(B/A) eq.not 0$.
]

#proof[
  Let ${b_1, dots.h.c ,b_n }$ be an $A$-basis for $B$, then it generates $L$ as a $K$-vector space.\ Indeed, if $x in L$ is algebraic over $K$, by *Lemma. 100*, there exists $d in A$ such that $d dot x in B$,\ i.e. $d dot x := sum a_i b_i, (a_i in A). arrow.r.double x= sum frac(a_i, d) dot b_i in K-op("span"){b_1, dots.h.c ,b_n }$.
]


#proposition(number: 112)[
  Let $A$ be integrally closed, $K := op("Quot")(A)$, $L/K$ a finite separable extension of degree $m$ and $B := overline(A)$ the integral closure of $A$ in $L$. Then there exist $A$-submodules $M$ and $M'$ of $L$ such that $M,M' tilde.equiv A^m$ and $M subset B subset M'$.\ In particular, $B$ is a finitely generated $A$-module if $A$ is Noetherian, and it is free of rank $m$ if $A$ is a PID.
]

#proof[
  Let ${beta_1, dots.h.c ,beta_m }$ be a $K$-basis for $L$. By *Lemma. 100*, there exists $d in A$ such that $d dot beta_i in B, forall i$. Now, we may assume that $beta_i in B, forall i. because psi:L times L -> K$ is non-degenerate by *Prop. 110*.  $therefore exists beta'_1, dots.h.c beta'_m$ such that $psi(beta_i dot beta'_j)=delta_(i j). arrow.r.double {beta'_1, dots.h.c ,beta'_m }$ is also a $K$-basis for $L$.
  claim. $A beta_1+ dots.h.c +A beta_m subset B subset A beta'_1+ dots.h.c + A beta'_m$. \ The first inclusion is obvious; for the second, let $beta in B$, we have $beta := sum b_j beta'_j, (b_j in K)$. Now, $because beta, beta_i in B. therefore beta_i dot beta in B. arrow.r.double op("Tr")_(L/K)(beta_i dot beta)= sum_(k=1)^m sigma_k(beta_i dot beta) in A$. Moreover, $A$ is integrally closed, it follows that  $op("Tr")_(L/K)(beta_i dot beta)= sum_j b_j op("Tr")(beta_i dot beta'_j)=b_i in A$.\
  If $A$ is Noetherian, then $M'$ is a Noetherian $A$-module, and so $B$ is finitely generated as an $A$-module. If $A$ is a PID, then $B$ is free of rank $<= m$ since it is contained in a free $A$-module of rank $m$, and it has rank $>= m$ because it contains a free $A$-module of rank $m$.
]


#remark(number: "113", title: [Integral Basis])[
  The *Prop. 112* applies in particular to the ring of integers $cal("O")_L$ of a number field $L$. A $bb("Z")$-basis of $cal("O")_L$ and thus a $K$-basis of $L$ is called an *integral basis* of $L$.
]


#corollary(number: 114)[
  The ring of integers $cal("O")_L$ in a number field $L$ is the largest subring of $L$ which is finitely generated as a $bb("Z")$-module.
]

#proof[
  We have just seen that $cal("O")_L$ is a finitely generated $bb("Z")$-module. Let $B$ be another subring of $L$ that is finitely generated as a $bb("Z")$-module; then every element of $B$ is integral over $bb("Z")$, and so $B subset cal("O")_L$.
]
