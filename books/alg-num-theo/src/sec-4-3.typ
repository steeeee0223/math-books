#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Local & Global Fields

#proposition(number: 278)[
  \ Let $K$ be complete with respect to a nonarchimedean discrete valuation and $A$ be the valuation ring of $K$ with maximal ideal $frak("m")$. Then $A$ is compact iff its residue field $k=A/frak("m")$ is finite.
]

#proof[
  Let $S$ be a set of representatives for $k=A/frak("m")$. claim. $A$ is compact $arrow.l.r.double S$ is finite. \
  "$arrow.r.double$"\ Clearly, $frak("m")={x in K:|x|<1}$ is open in $K$. As $A= union.sq.big_(s in S)(s+frak("m"))$ is the disjoint union of the open sets $s+frak("m")$ covering $A$. Thus $S$ is finite if $A$ is compact.\
  "$arrow.l.double$"\ Recall that a metric space $X$ is compact iff it is complete and totally bounded (i.e. for any $r>0$, there is a finite covering of $X$ by open balls of radius $r$). But every element of $A$ can be written as
  $
    s_0+s_1 pi+s_2 pi^2+ dots.h.c +s_n pi^n+ dots.h.c , quad (s_i in S).
  $

  For fixed $n in bb("N")$, since $S$ is finite, there are only finitely many sums
  $
    s_0+s_1 pi+s_2 pi^2+ dots.h.c +s_n pi^n, quad (s_i in S),
  $

  and that every element of $A$ is at distance at most $|pi^(n+1)|$, which tends to $0$ as $n -> oo$.\ Thus $A$ is compact.
]


#definition(number: "279", title: [Local Field])[
  \ A *local field* is a field $K$ with a valuation $| dot |$ which is locally compact (and hence complete) with respect to the induced topology.
]


#remark(number: 280)[
  - _(a)_ A topological vector space, (e.g. a field $K$ with a valuation), is locally compact iff $0$ has a neighbourhood whose closure is compact.\
    proof. Since a local base at $0$ is given by $U_n={x in K:|x|<frac(1, n)}$ by *(250)*, $K$ is locally compact iff $A$ is compact, where $A$ being the closure of its maximal ideal $frak("m")$.
  - _(b)_ It follows from the *Gelfand-Mazur Theorem* that a field which is locally compact with respect to an archimedean valuation is isomorphic to $bb("R")$ or $bb("C")$, (see [Algebra, Lang, Ch.XII]).

]


#proposition(number: 281)[
  The local fields which are locally compact with respect to a discrete nonarchimedean valuation are precisely the finite extensions of $bb("Q")_p$ and $bb("F")_p ((t))$.
]

#proof[
  We first claim that: $L$ is a finite extension of $K arrow.l.r.double L$ is a  local field.\ "$arrow.r.double$"\ Indeed, by *(270)*, $L$ is complete with respect to the discrete nonarchimedean valuation $|x|_L=|op("N")_(L/K)(x)|_K^(1/n)$, where $n=[L:K]$. Now, it remains to show that $ell =kappa(L)$ is finite. For this, it suffices to show that $ell /bb("F")_p$ is finite for $k=kappa(K)=bb("F")_p$ is finite. We let ${overline(x_i)}_(i=1)^n$ be $k$-independent in $ell$ with $overline(x_i) equiv x_i op("mod") frak("n"), (x_i in L)$. If
  $
    a_1 x_1+ dots.h.c +a_n x_n=0, quad (a_i in K)
  $

  is a nontrivial relation, then dividing by the $a_i$ with the highest valuation gives a relation with coefficients in the DVR $(A,frak("m"))$ of $K$. Hence, we get a nontrivial relation of $overline(x_i)$ over $k. ( -> arrow.l )$. Therefore, ${overline(x_i)}_(i=1)^n$ is $k$-independent, whence $ell$ is finite, which implies $L$ is local.\
  "$arrow.l.double$"\ Since $L$ is local, $ell$ is finite, thus of $op("char") ell =p>0$. We distinguish into two cases:\
  case 1. $op("char")L=0$. Then $bb("Q") subset L$ and if we restrict the additive valuation $nu$ of $L$ to $bb("Q")$, then we have $nu|_(bb("Q"))=nu_p$, (since $p in frak("n")$ for the DVR $(B,frak("n"))$ where $op("char")B/frak("n")=p$, and thus $nu(p)>0$). Hence the completion of $bb("Q")$ with respect to $nu_p$, namely $bb("Q")_p$, is contained in $L$. This turns $L$ into a locally compact topological $bb("Q")_p$-vector space which necessarily has finite $bb("Q")_p$-dimension.\
  case 2. $op("char")L>0$. Since $p dot 1=0$ in $B$ (for $op("char")B/frak("n")=p$), we conclude that $op("char")L=p$. Now, we write $ell := bb("F")_p(a)$ since $bb("F")_p$ is perfect, and let $f in bb("F")_p[x]$ be the minimal polynomial of $a$ over $bb("F")_p$. Since $bb("F")_p$ is perfect, $bb("F")_p(a)/bb("F")_p$ is separable, whence $f$ splits completely in $bb("F")_p(a)[x]$ and $bb("F")_p(a)=bb("F")_p(b)$ for any root of $f$. Considering $bb("F")_p subset B$ and thus $bb("F")_p[x] subset B[x]$, $f$ has a root $b in B$ with $b equiv a op("mod") frak("n")$. Hence $bb("F")_p(b)=bb("F")_p(a)= ell subset L$. But $ell$ serves as a representative set for itself. Since any $x in L$ can be developed into a Laurent series with coefficients in $ell$, we conclude that $bb("F")_p ((t)) subset L$ for a local parameter $t in B$ with $(t)=frak("n")$. Moreover, $L/bb("F")_p ((t))$ is finite (follows as above).
]


#definition(number: "282", title: [Global Field])[
  \ A *global field* is a finite extension of $bb("Q")$ (i.e. a number field) or $bb("F")_p(t)$ (i.e. a *function field* over $bb("F")_p$ in one variable).
]


#summary-box(title: [Summary Local-Global Principle. 283])[
  \ $X=op("Spec") cal("O")_K$ is a smooth curve for the ring of integers of a number field $K$, (cf. *Ch3*); $cal("O")_K$ is the ring of global functions on $X$, and $K$ is the field of *rational functions*. This corresponds to the ring [resp. field] of global holomorphic [resp. meromorphic] functions of a complex curve. The local fields completed with respect to $| dot |_frak("p")$ correspond to Laurent series of meromorphic functions centered at that given point $frak("p")$.\
  So a local field $K_nu$ obtained by completion should be thought of as local information. Usually, it is easier to extract information/ solve problems locally than globally. Of course, passing from local information/ solutions to global information/ solutions is usually nontrivial (think for instance of the _Mittag-Leffler Problem_ to stay in the picture). Loosely speaking, a *local-global principle* holds whenever the passage from local to global is unobstructed.
]


A famous instance is the *local-global principle* for the quadratic forms which we sketch next, see [F, Ch5] for details
#definition(number: "284", title: [Isotropic Quadratic Forms])[
  \ Let us consider quadratic forms over a field $K$ of $op("char")K eq.not 2$. A *quadratic form* is a function $Q:K^n -> K$ of the form $Q= sum_(i,j=1)^n a_(i j)x_i x_j$ with $a_(i j)=a_(j i) in K$. It is an elementary fact that via a suitable coordinate change, any quadratic form can be transformed into
  $
    Q(a_1, dots.h.c ,a_n) = sum_(i=1)^n a_i x_i^2.
  $

  We say that $Q$ is *isotropic* if $Q eq.not 0$ and there exists a nontrivial solution $x=(x_1, dots.h.c ,x_n)$ such that $Q(a_1, dots.h.c ,a_n)(x)=0$.
]


Given a quadratic form $Q(a_1, dots.h.c ,a_n), (a_i in K)$, we now try to solve the quadratic equation $Q(a_1, dots.h.c ,a_n)(x)=b$ in $x=(x_1, dots.h.c ,x_n)$ for arbitrary $b in K$.
#lemma(number: 285)[
  If $Q(a_1, dots.h.c ,a_n)$ is isotropic, then for every $b in K$, there exists $x=(x_1, dots.h.c ,x_n)$ such that $Q(a_1, dots.h.c ,a_n)(x)=b$.
]

#proof[
  Let $x=(x_1, dots.h.c ,x_n) in K^n$ with $sum_(i=1)^n a_i x_i^2=0$, (WLOG may assume that $a_1 x_1 eq.not 0$). Let $b in K$ and $t in K$. Put
  $
    y_i=cases(x_i(1+t) & text("if") i=1, x_i(1-t) & text("if") i >= 2).
  $

  Then
  $
    sum a_i y_i^2=(1+t^2) sum a_i x_i^2+2t a_1 x_1^2-2t sum_(i=2)^n a_i x_i^2=4t a_1 x_1^2.
  $

  By setting $t := frac(b, 4a_1 x_1^2)$ yields the required result.
]


#theorem(number: "286", title: [Hasse's Local-Global Principle for Quadratic Forms])[
  \ A quadratic form $Q$ over $bb("Q")$ is isotropic iff $Q$ is isotropic when considered as a quadratic form over $bb("R")$ and $bb("Q")_p$.
]


We will not prove this theorem in full generality for lack of time and content ourselves with the special case $n=2$. In this case, $Q(a_1,a_2)=a_1 x_1^2+a_2 x_2^2 eq.not 0$ iff $a_(1,2) in K^times$. Furthermore, $Q$ is isotropic iff $-frac(a_1, a_2) in (K^times )^2$, i.e. $-frac(a_1, a_2)$ is a square in $K^times$. Hence we need to prove the following:
#proposition(number: "287", title: [Hasse for $n=2$])[
  A nonzero rational number is a square in $bb("Q")$ iff it is a square in $bb("R")$ and $bb("Q")_p$.
]

#proof[
  Let $frac(m, n) in bb("Q")^times$. then $frac(m, n)= plus.minus p_1^(r_1) dots.h.c p_g^(r_g)$ (with $r_i in bb("Z")$) is a square if and only if $frac(m, n)>0$ and $2|r_i$ for all $i$.
  If $frac(m, n)>0$, clearly $frac(m, n)$ is a square in $bb("R")$; if $2|r_i$ for all $i$, then $nu_p(frac(m, n)) equiv 0 op("mod") 2$, so $frac(m, n)=p^(2l) dot u, (u in bb("Z")_p^times )$, whence $frac(m, n)$ is a square in $bb("Q")_p$.
]
