#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Nonarchimedean Valuations

Completing fields is also extremely useful; in particular, this yields the $p$-adic numbers $bb("Q")_p$. For this we will use valuations.
#definition(number: "242", title: [Nonarchimedean Valuation])[
  \ Let $K$ be a field. A *(multiplicative) valuation* on $K$ is a function
  $
    K arrow.r.long bb("R"), x arrow.r.long.bar |x|
  $

  such that
  - $|x|>0$ except for $|0|=0$.
  - $|x y|=|x| dot |y|$.
  - (Triangle Inequality): $|x+y| <= |x|+|y|$.

  Further, we call $| dot |$ a *nonarchimedean valuation* if $|x+y| <= op("max"){|x|,|y|}$ holds.
]


#remark(number: 243)[
  - _(a)_ The first two axioms of a valuation imply that a valuation restricts to a multiplicative group hmomorphism $K^times -> bb("R")_(>0)$. Since $bb("R")_(>0)$ is torsion-free, any root of unity in $K^times$ maps to $1$. In particular, $|-1|=|1|$ and $|-x|=|x|$. Further, the third axiom generalises to
  $
    | sum x_i| <= op("max"){|x_i|}.
  $

  - _(b)_ A valuation satisfies the usual properties of the absolute modulus on $bb("R")$ or $bb("C")$, so one can apply the standard estimates from analysis.

]


#example(number: 244)[
  - _(a)_ Any field admits the trivial valuation given by
  $
    |a|=cases(1 & text("if") a eq.not 0, 0 & text("if") a=0).
  $

  On a finite field $bb("F")$ there is no other valuation as all $bb("F")^times$ consists of roots of unity.
  - _(b)_ For any number field $K$, there exists an embedding $sigma:K arrow.r.hook bb("C")$. We get a valuation on $K$ by setting $|x| := |sigma(x)|$, where the latter valuation denotes the absolute modulus of a complex number.
  - _(c)_ For an (additive) discrete valuation $nu:K^times -> bb("Z")$, let $e in bb("R")$ with $e>1$. Then
  $
    |a| := cases(e^(-nu(a)) & text("if") a eq.not 0, 0 & text("if") a=0).
  $

  is a nonarchimedean valuation on $K$. A popular choice is the $p$-*adic valuation* on $bb("Q")$ induced by $nu_p$, where $p in bb("Z")$ a prime (cf. *Example 150*), together with $e=p$. Thus, if $a=a_0 p^r$, then $|a|=p^(-r)$. It reflects our intuition that numbers which are divisible by high powers of $p$ should be thought of as small quantities.
  - _(d)_ One can generalise (c) to any number field $K$. Fix  $frak("p") in op("Spec") cal("O")_K$ and let $bb("N")(frak("p")) := p^f$ (the *numerical norm* of $frak("p")$), where $(p)=frak("p") inter bb("Z")$ and $f$ the residue class degree (cf. *Prop. 155*). Using the $frak("p")$-adic discrete valuation $nu_frak("p")$ from *(150a)* yields the multiplicative $frak("p")$-*adic valuation* $|x|_frak("p") := bb("N")(frak("p"))^(-nu_frak("p")(x))$.

]


#proposition(number: 245)[
  A valuation $| dot |$ is nonarchimedean iff it takes bounded values on the set  ${m 1:m in bb("Z")}$ in $K$.
]

#proof[
  "$arrow.r.double$"\ Let $m in bb("Z")_(>0)$, since $| dot |$ is nonarchimedean, we have
  $
    |m 1|=|1+ dots.h.c +1| <= |1|=1.
  $

  As we noted above, $|-1|=|1|$, thus $|-m 1|=|m 1| <= 1$.\
  "$arrow.l.double$"\ Conversely, for $x,y in K$ we note that
  $
    |x+y|^n ,=|(x+y)^n|=| sum_r binom(n, r)x^r y^(n-r)| <= sum_r|binom(n, r)||x|^r|y|^(n-r); , <= sum_r|binom(n, r)| dot op("max"){|x|^n,|y|^n } = sum_r|binom(n, r)| dot op("max"){|x|,|y|}^n.
  $

  Suppose $|m 1|$ is bounded by $N$ for all $m$. Since $binom(n, r)$ is an integer, we have
  $
    |x+y|^n <= N(n+1) dot op("max"){|x|,|y|}^n.
  $

  On taking $n$th roots we find that
  $
    |x+y| <= N^(frac(1, n))(n+1)^(frac(1, n)) dot op("max"){|x|,|y|}.
  $

  Let $n -> oo$ and take $op("log")$, we can see that $N^(frac(1, n))(n+1)^(frac(1, n)) -> 1$. Thus $| dot |$ is a nonarchimedean valuation.
]


#corollary(number: 246)[
  If $op("char")K eq.not 0$, then $K$ has only nonarchimedean valuations.
]

#proof[
  Suppose $op("char")K := n$, then the set  ${m 1:m in bb("Z")} equiv bb("Z")/n bb("Z")$ is finite, thus bounded.
]


#proposition(number: 247)[
  Let $| dot |$ be a nontrivial nonarchimedean valuation and let $op("log")$ be the logarithm taken with respect to a real base $e>1$. Then the map
  $
    nu:K^times arrow.r.long bb("R"), x mapsto -op("log")|x|
  $

  satisfies
  $
    text("(i)") nu(x y)=nu(x)+nu(y) quad text("and quad (ii)") nu(x+y) >= op("min"){nu(x),nu(y)}.
  $

  If $| dot |$ is *discrete*, i.e. $nu(K^times)$ is a discrete subgroup of $bb("R")$, then $nu$ is a multiple of some discrete valuation $K^times -> bb("Z") subset bb("R")$.
]

#proof[
  The two properties (i) and (ii) are clear by the definition. For the last statement, note that $nu(K^times)$ is an (additive) subgroup of $bb("R")$. Thus, if it is discrete, then it must be a lattice, i.e. $nu(K^times) := m bb("Z")$ for some $m in bb("R")_(>0)$. Hence
  $
    op("ord"):K^times arrow.r.twohead bb("Z"), quad x arrow.r.long.bar frac(1, m) dot nu(x)
  $

  is an additive discrete valuation.
]


#remark(number: 248)[
  By *Thm. 270* and *Rmk. 271* we can extend the $p$-adic valuation $| dot |_p$ on $bb("Q")$ to its algebraic closure $overline(bb("Q"))$. Since $p^(frac(1, n)) in overline(bb("Q"))$ and $|p^(frac(1, n))|_(bb("Q"))=p^(-frac(1, n))$ tends to $1$ as $n -> oo$, a nonarchimedean valuation is not necessarily discrete.
]


#proposition(number: "249", title: [Local Parameter])[
  \ Let $| dot |$ be a nonarchimedean valuation and $nu=-op("log")| dot |$ as above. Then
  - _(a)_ $A := {a in K:|a| <= 1}={a in K:nu(a) >= 0}$ is a valuation ring.
  - _(b)_ $A^times ={a in K:|a|=1}={a in K:nu(a)=0}$ is its group of units.
  - _(c)_ $frak("m") := {a in K:|a|<1}={a in K:nu(a)>0}$ is its unique maximal ideal.

  Furthermore, $| dot |$ is discrete iff $A$ is a DVR. In this case, the maximal ideal $frak("m")=(pi)$, where $nu(K^times)=nu(pi) bb("Z")$ and we call such $pi$ a *local (uniformising) parameter*.
]

#proof[
  (a) Note that $|a| dot |a^(-1)|=|a dot a^(-1)|=1$, we have $|a^(-1)|=|a|^(-1)$, thus if $a in.not A$, then $|a|>1$, whence $|a^(-1)|=|a|^(-1)<1$, i.e. $a^(-1) in A$. Hence $A$ is a valuation ring.\
  (b) Since $|a| dot |a^(-1)|=|a dot a^(-1)|=1$, we have
  $
    a in A^times arrow.l.r.double a^(-1) in A arrow.l.r.double |a|^(-1) <= 1 arrow.l.r.double |a|=1.
  $

  (c) Note that $A without frak("m")=A^times$, it suffices to show that $frak("m")$ is an ideal.\
  If $x,y in frak("m")$, then $|x+y| <= op("max"){|x|,|y|}<1$, i.e. $x+y in frak("m")$. If $a in A$, then $|a x|=|a| dot |x|<1$, i.e. $a x in frak("m")$. Hence $frak("m")$ is an ideal.\
  "$arrow.r.double$"\ If $| dot |$ is discrete, then this follows from *Prop. 247* that $nu(K^times)=m bb("Z"), (m>0)$ and there exists $pi in K^times$ with $nu(pi)=m>0$, thus $pi in frak("m") subset A$. Now let $a in A$, then $0 <= nu(a) := k nu(pi)$ for some $k in bb("R")_( >= 0)$. Now, since $0=nu(a)-k nu(pi)=nu(a pi^(-k))$, we have $u := a pi^(-k) in A^times$, whence $a=u dot pi^k in (pi^k)$. Thus every ideal is of the form $(pi^k)$, so that $A$ is a PID and thus a DVR as being local.\
  "$arrow.l.double$"\ Conversely, if $A$ is a DVR. Since $nu(x^(-1))=-nu(x)$, it suffices to show that: if $nu(x)>0$, then $nu(x) in nu(pi) bb("Z")$, where $frak("m") := (pi)$. Indeed, $because nu(x)>0. therefore x in A. because A$ is a DVR. $therefore x := u pi^k$ for some $u in A^times , k in bb("N")$. Thus,
  $
    nu(x)=nu(u)+k nu(pi)=k nu(pi) in nu(pi) bb("Z").
  $

]


#note(number: "250", title: [Metrics])[
  \ A valuation $| dot |$ defines a metric on $K$ with the distance function $d(a,b)=|a-b|$ and thus induces a metric topology on $K$. A countable local base at $0$ is given by
  $
    U_n := {x in K:|x|<frac(1, n)}.
  $

  For instance, $|a-b|$ is small with respect to the metric on $bb("Q")$ defined by $| dot |_p$ if $p^n|a-b$ for large $n$.
  Now, let $K$ be a number field and fix $frak("p") in op("Spec") cal("O")_K$. The topology on $K$ defined by the $frak("p")$-adic valuation $| dot |_frak("p")$ from *(244)* is called the $frak("p")$-*adic topology* on $K$.
]


#proposition(number: "251", title: [Equivalent Valuations])[
  \ Let $| dot |_1$ and $| dot |_2$ be two valuations on $K$ with $| dot |_1$ nontrivial. Then T.F.A.E.:
  - _(i)_ $| dot |_1$ and $| dot |_2$ define the same topology.
  - _(ii)_ $|alpha|_1<1$ implies $|alpha|_2<1$ for any $alpha in K$.
  - _(iii)_ $| dot |_2=| dot |_1^a$ for some $a>0$.

  The valuations $| dot |_1$ and $| dot |_2$ are *equivalent* if they satisfy one and thus all of these conditions.
]

#proof[
  "(i) $arrow.r.double$ (ii)"\ Since $|alpha^n|=|alpha|^n$, clearly $alpha^n -> 0$ iff $|alpha|<1$. Thus (i) implies that
  $
    |alpha|_1<1 arrow.l.r.double.long |alpha|_2<1.
  $

  "(ii) $arrow.r.double$ (iii)"\ Since $| dot |_1$ is nontrivial, there exists $y in K$ with $|y|>1$. Consider\ $a := op("log")|y|_2/op("log")|y|_1$, so that $op("log")|y|_2=a dot op("log")|y|_1. arrow.r.double |y|_2=|y|_1^a$. Now, for any $0 eq.not x in K$, choose $b := op("log")|x|_1/op("log")|y|_1$, then $|x|_1=|y|_1^b$. claim. $|x|_2=|y|_2^b$.\
  Suppose the rational $frac(m, n)>b, (n>0)$. Then $|x|_1=|y|_1^b<|y|_1^(m/n). arrow.r.double |frac(x^n, y^m)|_1<1$. From assumption, this implies $|frac(x^n, y^m)|_2<1$, so $|x|_2<|y|_2^(m/n)$. Moreover, this is true for all rationals $frac(m, n)>b$, thus $|x|_2 <= |y|_2^b$. A similar argument with rationals $frac(m, n)<b$ shows that $|x|_2 >= |y|_2^b$. Thus we have the equality and finally
  $
    |x|_2=|y|_2^b=|y|_1^(a b)=|x|_1^a.
  $

  "(iii) $arrow.r.double$ (i)"\ By assumption, a sequence converges with respect to  $| dot |_1$ iff it converges with respect to $| dot |_2$. Hence these valuations define the same topology.
]


Now, we give a complete list of the valuations on $bb("Q")$ (up to equivalence).
#theorem(number: "252", title: [Ostrowski])[
  Let $| dot |$ be a nontrivial valuation on $bb("Q")$.
  - _(a)_ If $| dot |$ is archimedean, then $| dot |$ is equivalent to $| dot |_oo$, the valuation defined by the restriction of the usual absolute modulus on $bb("R")$ to $bb("Q")$.
  - _(b)_ If $| dot |$ is nonarchimedean, then $| dot |$ is equivalent to $| dot |_p$, for unique prime $p$.

]

#proof[
  Let $m,n>1$ be integers. Then we can write
  $
    m := a_0+a_1 n+ dots.h.c +a_r n^r, quad (0 <= a_i<n, n^r<m).
  $

  Note that
  $
    |a_i|=|op("underbrace"){1+ dots.h +1}_(a_i text("-times"))| <= a_i dot |1|=a_i<n.
  $

  Pick $N := op("max"){1,|n|}$, then we have
  $
    |m| <= sum_(i=0)^r|a_i||n|^i <= sum_(i=0)^r n N^r=(r+1)n N^r <= (1+frac(op("log") m, op("log") n))n N^(frac(op("log") m, op("log") n)).
  $

  Now, replace $m$ by $m^t (t in bb("N"))$, we have
  $
    |m| <= (1+frac(t op("log") m, op("log") n))^(frac(1, t))n^(frac(1, t))N^(frac(op("log") m, op("log") n)) -> 1 quad text("as") quad t -> oo .
  $

  Hence, $|m| <= N^frac(op("log") m, op("log") n)$. Now we distinguish cases.\
  case 1. For all integers $n>1$ with $|n|>1$. In this case, $N=|n|$ and the above result yields: $|m|^(1/op("log") m) <= |n|^(1/op("log") n)$. By symmetry, we must have the equality, and so for some $c>1$ we have $c=|m|^(frac(1, op("log") m))=|m|^(frac(1, op("log") n)), forall m,n in bb("N")_(>1)$. Hence, for any integers $n>1$, we have
  $
    |n|=c^(op("log") n)=e^(op("log") c op("log") n)=n^(op("log") c)=|n|_oo^a quad text("where") a := op("log") c.
  $

  Since both $| dot |$ and $| dot |_oo^a$ are homomorphisms $bb("Q")^times -> bb("R")_(>0)$, the fact that they agree on a set of generators (the primes and $-1$) for the group $bb("Q")^times$ implies that they agree on all of $bb("Q")^times$, hence these two valuations are equivalent.\
  case 2. For some integer $n>1$ with $|n| <= 1$. In this case we have $N=1$ and the above result implies $|m| <= 1$ for all integers $m$, whence the valuation is nonarchimedean by *(245)*. Let $(A,frak("m"))$ be the associated local ring as in *(249)*, then $bb("Z") subset A$. Note that
  - $frak("m") inter bb("Z")$ is a prime ideal in $bb("Z")$ since $frak("m")$ is prime.
  - $frak("m") inter bb("Z")$ is nonzero otherwise the valuation would be trivial.

  Hence $frak("m") inter bb("Z")=(p)$ for some prime $p in bb("Z")$. It follows that $|m|=1, forall p divides.not m$, and so $|frac(m, n) dot p^r|=|p|^r$ if $m,n in bb("Z")$ with $p divides.not m,n$. Thus, if $a>0$ satisfies that $|p|=(frac(1, p))^a$, then $|x|=|x|_p^a$ for all $x=frac(m, n) in bb("Q")$.
]


#theorem(number: "253", title: [Product Formula])[
  \ For $p in cal("P") := {text("prime numbers")} union { oo }$, let $| dot |_p$ be the corresponding $p$-adic valuation on $bb("Q")$. Then
  $
    product_(p in cal("P"))|x|_p=1, quad text("for all") x in bb("Q")^times .
  $

]

#proof[
  Note that the $p$-adic valuation $| dot |_p$ is defined by
  $
    bb("Q")^times arrow.r.long bb("R"), x := frac(a, b) dot p^r arrow.r.long.bar p^(-r), quad (p divides.not a,b).
  $

  Let $x=frac(a, b), (a,b in bb("Z"))$. Then $|x|_p=1$ unless $p|a$ or $p|b$. Hence $|x|_nu eq.not 1$ for all but finitely many $nu$, so the product is actually finite. Now, consider the well-defined (multiplicative) group homomorphism
  $
    pi:bb("Q")^times arrow.r.long bb("R")^times , x arrow.r.long.bar product |x|_nu
  $

  We factorise $x := p_1^(r_1) dots.h.c p_k^(r_k), (p_i bb("Z"), r in bb("Z"))$ into primes and note that
  $
    |x|_p=|p_1^(r_1) dots.h.c p_k^(r_k)|_p=|p_1|_p^(r_1) dots.h.c |p_k|_p^(r_k).
  $

  Since $pi(-1)=1$ (as $|-1|_p=1$ for any $p$), and from the definition of the $p$-adic valuation, we have
  $
    |p|_p=frac(1, p); quad |p|_q=1 text("if") q eq.not p; quad |p|_oo =p.
  $

  Hence, $pi(p_i)=1$ for all $i$, it follows that the product $pi(x)=1$.
]


Let $K$ be an algebraic number field. We can generalise the previous results as follows:
#definition(number: "254", title: [Primes of a Number Field])[
  \ An equivalence class of valuations on $K$ is called a *prime* or *place* of $K$. We usually denote the primes of $K$ by $upsilon$.\
  For instance, the primes of $bb("Q")$ are the primes of $bb("Z")$ and the valuation $| dot |_oo$ induced by the real embedding $sigma:bb("Q") arrow.r.hook bb("C")$, i.e. $sigma$ factorises via $bb("R")$.
]


#theorem(number: 255)[
  There exists exactly one prime of $K$, for each
  - _(a)_ prime ideal $frak("p") subset op("Spec") cal("O")_K: |x|_(frak("p"))=bb("N")(frak("p"))^(-nu_(bb("p"))(x))$.
  - _(b)_ real embedding $K attach(arrow.r.hook, t: sigma) bb("R") subset bb("C"): |x|=|sigma(x)|$.
  - _(c)_ complex pair of complex embedding $K attach(arrow.r.hook, t: sigma) bb("C"): |x|=|sigma(x)|^2$.

]


#theorem(number: "256", title: [Product Formula])[
  For each prime $upsilon$ of $K$, we let $| dot |_upsilon$ be the valuation defined in *(255)*. Then
  $
    product_(upsilon)|x|_upsilon=1, quad text("for all") x in K^times .
  $

]


#lemma(number: 257)[
  If $| dot |_1,| dot |_2, dots.h.c ,| dot |_n$ are nontrivial inequivalent valuations of a field $K$, there exists $a in K$ such that $|a|_1>1$ and $|a|_i<1$ for all $i eq.not 1$.
]

#proof[
  For $n=2$, since $| dot |_1$ and $| dot |_2$ are inequivalent, by *(251ii)*, there exist $b,c in K$ such that
  $
    |b|_1<1, quad ,|b|_2 >= 1;; |c|_1 >= 1, quad ,|c|_2<1.;
  $

  Take $a := frac(c, b) in K$, then done. Now, we proceed by induction assuming that it is true for $n-1$ valuations. There exist $b,c in K$ such that
  $
    |b|_1>1, quad ,|b|_i<1, forall 2 <= i <= n-1;; |c|_1<1, quad ,|c|_n>1.;
  $

  $
    |a|=|c| dot |b|^r arrow.r.long cases(|c| & text("if") |b|=1, 0 & text("if") |b|<1, oo & text("if") |b|>1) quad text("as") r -> oo .
  $

  If $|b|_n>1$, then $a := frac(c b^r, 1+b^r)$ works for sufficiently large $r$ since
  $
    |a|=|c| dot frac(|b|^r, |1+b|^r) arrow.r.long cases(|c| & text("if") |b|>1, 0 & text("if") |b|<1) quad text("as") r -> oo .
  $

]


#lemma(number: 258)[
  If $| dot |_1,| dot |_2, dots.h.c ,| dot |_n$ are nontrivial inequivalent valuations of a field $K$ and $epsilon>0$, we can find an $a in K$ with
  $
    |a-1|_1<epsilon quad text("and") quad |a|_i<epsilon, forall i eq.not 1.
  $

]

#proof[
  Choose $a in K$ as in the previous lemma and set $a_r := frac(a^r, 1+a^r)$. Then
  $
    |a_r-1|_1 ,=frac(1, |1+a^r|_1) <= frac(1, |a|_1^r-1) arrow.r.long 0; ; |a_r|_i ,=frac(|a|_i^r, |1+a|_i^r) <= frac(|a|_i^r, 1-|a|_i^r) arrow.r.long 0, quad text("for") i >= 2
  $

  as $r -> oo$.
]


#theorem(number: "259", title: [Weak Approximation])[
  In the situation of *(257)*, let $a_1, dots.h.c ,a_n in K$. For any $epsilon>0$, there is an element $a in K$ such that $|a-a_i|_i<epsilon$ for all $i$.
]

#proof[
  Choose $b_i, (1 <= i <= n)$ close to $1$ for $| dot |_i$ and close to $0$ for $| dot |_j, (j eq.not i)$. Then $a := sum_(j=1)^n a_j b_j$ works since $|a-a_i|_i <= |a_i|_i|b_i-1|_i+ sum_(j eq.not i)|a_j|_j|b_j|_j arrow.r.long 0+0=0$.
]


#remark(number: 260)[
  - _(a)_ This theorem can be regarded as a valuation form of the CRT.
  - _(b)_ In particular, it follows that there is no finite product formula: If
  $
    product_(i=1)^n|a|_i^(r_i)=1, (r_i in bb("R")), quad text("for all") a in K^times ,
  $

  then $r_i=0$ for all $i$.

]

#proof[
  If $r_i eq.not 0$, we can choose $a$ such that $|a|_i$ is sufficiently large and $|a|_j$ sufficiently small for $j eq.not i. ( -> arrow.l )$
]


#note(number: "261", title: [The Completion of Fields])[
  \ An equivalence class $upsilon$ of $| dot |$ turns $K$ into a topological field and determines a completion $K_upsilon := hat(K)$ which is unique up to homeomorphism, (cf. *Thm. 266*). Then every $x in hat(K)$ is the limit of a Cauchy sequence $(x_n)$ in $K$. Since
  $
    |x_n-x_m| >= ||x_n|-|x_m||,
  $

  $(|x_n|)$ is a Cauchy sequence in $bb("R")$ and thus has a limit. We can therefore extend $| dot |$ to a valuation on $hat(K)$ by setting $|x| := op("lim")_n|x_n|$. In the same way we can extend the associated additive valuation $nu=-op("log")| dot |$ to $hat(K)$.\
  Now, let $| dot |$ be a discrete nonarchimedean valuation on $K$. Since $nu(K^times)=c bb("Z")$ is closed in $bb("R")$, we have $nu(hat(K)^times)=nu(K^times)$. Hence $| dot |$ extends to a  discrete valuation on $hat(K)$ which is normalised if $nu$ is normalised. The associated DVR is
  $
    hat(A) := {a in hat(K):|a| <= 1}.
  $

  It is the completion of the DVR $A={a in K:|a| <= 1}$ with respect to the $frak("m")$-adic topology defined by its maximal ideal
  $
    frak("m") = {a in K:|a|<1} = (pi).
  $

  In particular, $hat(A)$ is complete. The completion of $frak("m")$ is
  $
    hat(frak("m")) = {a in hat(K):|a|<1} = (pi) hat(A),
  $

  and that $hat(A)/hat(frak("m"))^n equiv A/frak("m")^n$. [Exercise]
]


#proposition(number: 262)[
  Let $S subset A$ be a set of representatives of $A/frak("m")$ with $0 in S$, and let $frak("m")=(pi)$. Then every element $0 eq.not x in hat(K)$ has a unique representation as a convergent series
  $
    x = pi^m(a_0+a_1 pi+a_2 pi^2+ dots.h.c ), quad (a_i in S, a_0 eq.not 0, m in bb("Z")).
  $

]

#proof[
  Since $| dot |$ is discrete and $frak("m")=(pi)$, we may write $x := u dot pi^m, (u in hat(A)^times , m in bb("Z"))$. Then $nu(x)=-m nu(pi)$, so $nu(x pi^m)=0$. Since $u in hat(A)^times$ and $hat(A)/hat(frak("m")) equiv A/frak("m")$, there is a unique representative $0 eq.not a_0 in S$ for $u op("mod") hat(frak("m"))$. Hence $u=a_0+b_1 pi$ for some $b_1 in hat(A)$. Continuing this process we get
  $
    u=a_0+a_1 pi+ dots.h.c +a_(n-1)pi^(n-1)+b_n pi^n, quad (b_n in hat(A)).
  $

  Then there is a unique representative $a_n in S equiv A/frak("m") equiv hat(A)/hat(frak("m"))$ for $b_n op("mod") hat(frak("m"))$, whence $b_n=a_n+b_(n+1)pi^(n+1)$ for some $b_(n+1) in hat(A)$. Now, it remains to show that the series converges to $x$. But
  $
    |x-pi^m sum_(i=0)^n a_i pi^i|=|pi|^m|b_(n+1)pi^(n+1)| <= |pi|^(m+n+1) arrow.r.long 0 quad text("as") n -> oo
  $

  for $| dot |=| dot |_((pi))=| dot |_frak("m")$ the $frak("m")$-adic valuation.
]


#example(number: "263", title: [The $p$-Adic Numbers])[
  \ $bb("Q")_p$ is precisely the completion of $bb("Q")$ by the prime $| dot |_p$, ($p in bb("Z")$ prime).\ A set of representatives of $bb("Z")_p/(p) bb("Z")_p equiv bb("Z")/p bb("Z")$ is given by ${0,1, dots.h.c ,p-1}$. Hence *(262)* interprets a $p$-adic number in $bb("Q")_p$ as a Laurent series $sum_(i=-n)^oo a_i pi^i, (n in bb("N"), 0 <= a_i<p)$, in complete analogy with holomorphic or meromorphic functions.
]


#remark(number: 264)[
  - Primes of a number field $K$ which correspond to nonarchimedean valuations $| dot |_frak("p"), (frak("p") in op("Spec") cal("O")_K)$, are called *finite*.
  - Primes which correspond to an archimedean prime are called *infinite*. This reflected in the notation $| dot |_oo$ for the valuation on $bb("Q")$ which is usually considered in your analysis course which yields the real numbers $bb("R")$.

]


#example(number: "265", title: [The Field of Laurent Series])[
  \ Our initial motivation concerned an algebraic analogue of the meromorphic functions in one variable. \
  Consider a *rational function field* $k(t) := op("Quot") k[t]$ and the valuation induced by the prime $frak("p") := (t-a) lt.closed k[t]$. A set of representatives for the completion $k op("llparenthesis") t op("rrparenthesis") := k(t)_((t-a))$ is given by
  $
    k [[ t ]]/(t-a)^e equiv k[t]/(t-a) equiv k.
  $

  In particular, any rational function $frac(f(t), g(t))$ has a development into a Laurent series
  $
    sum_(i=-n)^oo a_i(x-a)^i text("in") k op("llparenthesis") t op("rrparenthesis"), quad (a_i in k, n in bb("N")).
  $

]


Let $A$ be a DVR with maximal ideal $frak("m")=(pi)$ and residue field $k=A/frak("m")$, and we assume that $A$ is complete with respect to the $frak("m")$-adic topology. For $f in A[x]$, let $overline(f) in k[x]$ denote the reduction of the coefficients of $f$ modulo $frak("m")$. The first version of *Hensel's Lemma* asserts that if $overline(f)$ has a simple root, then we can split off a linear factor from $f$. This generalises the following:
#theorem(number: "266", title: [Hensel's Lemma Ver. II])[
  \ We use the previous notation and consider a monic polynomial $f in A[x]$. If $overline(f)$ factors as $overline(f)=g_0 h_0$ in $k[x]$ where $g_0$ and $h_0$ are monic and relatively prime, then there exist $g,h in A[x]$ monic which are uniquely determined and such that $f=g h, overline(g)=g_0$ and $overline(h)=h_0$. Furthermore, we have $(g,h)=A[x]$. [Exercise]
]


#remark(number: 267)[
  The lemma holds in fact for any valuation ring or a field which is complete with respect to a nonarchimedean valuation, (cf. [N, II.4.6]).
]


#example(number: 268)[
  \ We claim that the $p$-adic numbers $bb("Q")_p$ contain the $p$th roots of unity. Indeed, consider the polynomial $f := x^(p-1)-1 in bb("Z")_p[x]$. The residue field is $bb("Z")_p/(p) bb("Z")_p equiv bb("Z")/p bb("Z")$ and so splits into linear factors over $k=bb("F")_p$. Repeated application of *Hensel's Lemma* allows us to split off a linear factor of $f$ at each stage so that $x^(p-1)-1= product_(i=1)^(p-1)(x-xi_i)$.
]


#corollary(number: 269)[
  Let $K$ be complete with respect to a discrete nonarchimedean valuation and let $A$ be a DVR. Then for any irreducible polynomial $f := a_0+a_1 x+ dots.h.c +a_n x^n in K[x]$, we have
  $
    |f| := op("max"){|a_0|, dots.h.c ,|a_n|}=op("max"){|a_0|,|a_n|}.
  $

  In particular, $a_n=1$ and $a_0 in A$ imply $f in A[x]$.
]

#proof[
  Since $K=op("Quot")A$ (where $A$ is a valuation ring), multiplying by a suitable element yields $x dot f in A[x]$. Furthermore, dividing by a coefficient $a_j$ with $|a_j| := op("max"){|a_0|, dots.h.c ,|a_n|}$ yields
  $
    |frac(x, a_j) dot f|=1 quad text("and") quad frac(x, a_j) dot f in A[x].
  $

  Since rescaling of $f$ does not affect the assertion, we may straight away assume that $f in A[x]$ and $|f|=1$. Now, let $a_r$ be the first coefficient such that $|a_r|=1$. Then
  $
    f equiv x^r(a_r+a_(r+1)x+ dots.h.c +a_n x^(n-r)) quad op("mod") frak("m").
  $

  If $0<r<n$, this contradicts the *Hensel's Lemma* since $f$ is irreducible. Thus we get the result $|f|=op("max"){|a_0|,|a_n|}$.
]


#theorem(number: 270)[
  Let $K$ be complete with respect to a discrete nonarchimedean valuation $| dot |_K$ with $A$: DVR and let $L/K$ be a finite extension of degree $n$. Then $| dot |_K$ extends uniquely to a discrete valuation $| dot |_L$ on $L$ for which $L$ is complete and whose DVR is the integral closure of $A$ in $L$. Furthermore,
  $
    |x|_L=|op("N")_(L/K)(x)|_K^(1/n), quad text("for all") x in L.
  $

]

#proof[
  Let $B$ be the integral closure of $A$ in $L$ and $frak("p")$ be the maximal ideal of $A$. Then $B$ is a Dedekind domain and the valuations of $L$ extending $| dot |_frak("p")$ correspond to the ideals of $B$ lying over $frak("p")$.\
  Suppose that there are distinct prime ideals $frak("P")_1$ and $frak("P")_2$ in $B$ dividing $frak("p")$, then there exists $b in B$ such that $frak("P")_1 inter A[b] eq.not frak("P")_2 inter A[b]$, (e.g. choose $b in frak("P")_1$ but $b in.not frak("P")_2$). Let $f$ be the minimum polynomial of $b$ over $K$, so that $A[b] equiv A[x]/(f)$. Since $f in A[x]$ is irreducible and $A$ is complete, *Hensel's Lemma* show that $overline(f)$ (the image of $f$ in $k[x], (k=A/frak("p"))$) must be a power of an irreducible polynomial. Then
  $
    A[b]/frak("p")A[b] equiv k[x]/(overline(f))
  $

  is a local ring, which contradicts the fact that $A[b]$ has two prime ideals containing $frak("p")$. Hence $| dot |_frak("p")$ extends uniquely to a valuation $| dot |_L$ on $L$.\
  Clearly, $| dot |_frak("p")$ also extends to the Galois closure $overline(L)$ of $L$. For each $sigma in op("Gal")(L/K)$, consider the map
  $
    L arrow.r.hook bb("C"), b arrow.r.long.bar |sigma(b)|.
  $

  This is again a valuation of $L$, and so the uniqueness implies that $|b|_L=|sigma(b)|$. Now,
  $
    |op("N")_(L/K)(b)|_K=| product sigma(b)|_K= product |sigma(b)|= product |b|_L=|b|_L^n
  $

  implies the required formula.\
  Finally, we have to show that $L$ is complete. Let ${e_i }_(i=1)^n$ be an $A$-basis for $B$ (as an $A$-module), and let $(alpha(m))$ be a Cauchy sequence in $L$. We write $alpha(m) := sum_(i=1)^n a_i(m)e_i, (a_i(m) in K)$, then for each $i, (a_i(m))$ is a Cauchy sequence in $K$. As $K$ is complete, say $a_i := op("lim")_m a_i(m)$, then $alpha := sum_(i=1)^n a_i e_i=op("lim")_m(alpha(m))$, whence $L$ is complete.
]


#remark(number: 271)[
  - _(a)_ If $| dot |_K$ is nonarchimedean, then so is $| dot |_L$.
  - _(b)_ The statement holds for any valuation, whether it is discrete or not, (see [N, II.4.8]).
  - _(c)_ If $| dot |$ is a valuation on $K$, then $| dot |$ extends uniquely to any finite subextension of an algebraic separable extension $L/K$ and thus to a nonarchimedean valuation $| dot |_L$ on $L$. However, $| dot |_L$ need not be discrete, (cf. *Rmk. 248*).

]


#corollary(number: 272)[
  Let $K$ and $L$ be as in *Thm. 270* with DVRs $(A,frak("m"))$ and $(B,frak("n"))$, respectively; then $n=e f$, where $n=[L:K], e$ the ramification index of $frak("m")$, and $f=[B/frak("n"):A/frak("m")]$ the degree of the residue field extension.
]

#proof[
  Consider $frak("p") in op("Spec")A$ and the associated $frak("p")$-adic valuation $| dot |_frak("p")$. If $frak("a")$ is an ideal of $A$, the decomposition $frak("a") := frak("p")_1^(r_1) dots.h.c frak("p")_g^(r_g)$ extends to $frak("a")^e := (frak("p")_1^e)^(r_1) dots.h.c (frak("p")_g^e)^(r_g)$, so that every $frak("P") in op("Spec")B$ which divides $frak("p")$ yields a $frak("P")$-adic valuation on $L$ which extends $| dot |_frak("p")$. By uniqueness of the extension *(270)*, we conclude that there exists precisely one $frak("P")$ dividing $frak("p")$, whence the result of the general formula $n= sum e_i f_i$ follows from *Thm. 158*.
]


#remark(number: 273)[
  In this situation, let $nu_L$ and $nu_K$ denote the induced additive valuations. Since $frak("m")=(pi)$ and $frak("n")=(omega)$, we have $(pi)B=frak("m")B=frak("n")^e=(omega^e)$, we conclude that $nu_K(pi)=nu_L(pi)=e nu_L(omega)$. It follows that $e=(nu_L(L^times ):nu_K(K^times ))$.
]


#definition(number: "274", title: [Ramification])[
  For the case in *Cor. 272*:
  - If $e=n=[L:K]$, i.e. $f=1$ or $frak("m")B=frak("n")^n$, we say that $L$ is *totally ramified*.
  - If $f=n=[L:K]$, i.e. $e=1$, we say that $L$ is *unramified* over $K$.

]


For the rest of this section we assume that:
- $K$ is complete with respect to a discrete valuation $nu$ with the associated DVR $(A,frak("m"))$.
- $K$ and the residue field $A/frak("m")$ are perfect. In particular, any algebraic extension of these fields is separable.

These assumptions hold, for instance, for a $p$-adic number field which is sufficient for our purpose. Moreover, we have already seen that the valuation $| dot |$ of $K$ can extend uniquely to a (not necessarily discrete) valuation on $L$ if $L/K$ is a (possibly infinite) algebraic extension, (cf. *Rmk. 271*). In particular, we get the valuation ring $(B,frak("n"))$:
$
  B={x in L:nu_L(x) <= 1} quad text("and") quad frak("n")={x in B:nu_L(x)<1}
$

and the residue field $kappa(L) := B/frak("n")$ of $L$.

#proposition(number: 275)[
  Let $L/K$ be an algebraic extension and write $ell =kappa(L)$ the residue field of $L$. The assignment $K' mapsto k'=kappa(K)'$ sending an unramified extension $K'$ of $K$ contained in $L$ to its residue field $k'$ yields a 1-1 correspondence between the sets:
  $
    {K' subset L:text("finite and unramified over") K} arrow.l.r.long {k' subset ell :text("finite over") k}.
  $

  Moreover, this correspondence preserves the following properties:
  - _(a)_ *(Inclusion).* $K' subset K'' arrow.l.r.double kappa(K') subset kappa(K'')$.
  - _(b)_ *(Normality).* $K'$ is Galois over $K arrow.l.r.double k'=kappa(K')$ is Galois over $k$. In this case we have the canonical isomorphism $op("Gal")(K'/K) equiv op("Gal")(k'/k)$.

]

#proof[
  claim 1. The map is surjective. Let $k' subset ell$ be a finite extension of $k$, we may write $k' := k(a), (a in L)$ since $k$ is perfect. Let $f_0$ be the minimum polynomial of $a$ over $k$ and $f$ be any lifting of $f_0$ to $A[x]$, i.e. $overline(f)=f_0$. As $a$ is a simple root of $f_0$, there exists a unique $alpha in L$ such that $f(alpha)=0$ and $alpha equiv a op("mod") frak("n")$. Hence $K' := K(alpha) subset L$ has residue field $k'$.\
  claim 2. The map is injective. Suppose that $K'$ and $K''$ are unramified extensions of $K$ in $L$ with the same residue field $k'$. Then the compositum $K' dot K''$ (the smallest subfield of $L$ containing $K'$ and $K''$) is an unramified extension of $K$ with residue field $k'$. Hence
  $
    [K' dot K'':K]=[k':k]=[K'=K],
  $

  whence $K''=K'$, i.e. the map is 1-1.\
  (a) We have just seen that if $K'arrow.r.twohead k'=kappa(K')$, then there exists $alpha' in B'$ (where $(B',frak("n")')$ the valuation ring of $K'$) such that $K'=K(alpha')$ and $k'=k(overline(alpha)')$ where $overline(alpha)' equiv alpha' op("mod") frak("n")'$. The assertion is then obvious. \
  (b) We assume that $K'$ is Galois over $K$, then $op("Gal")(K'/K)$ preserves $A'$ (the valuation ring in $K'$) and its maximal ideal, thus we get a map $op("Gal")(K'/K) -> op("Aut")(k'/k)$. Write $k'=k(a)$ and let $g in A[x]$ be such that $overline(g) in k[x]$ is the minimum polynomial of $a$. Let $alpha in A'$ be the unique root of $g$ such that $overline(alpha)=a$ (as above). Since $K'$ is Galois over $K$, $g$ splits in $A'[x]$ and this implies that $overline(g)$ splits in $k[x]$, whence $k'$ is Galois over $k$. Now let $r=[k':k]=[K':K]$ and $alpha_1, dots.h.c ,alpha_r$ be the roots of $g$. Then
  $
    {alpha_1, dots.h.c ,alpha_r } = {sigma(alpha):op("Gal")(L/K)}.
  $

  As $overline(g)$ is separable, the $alpha_i$'s are distinct modulo $frak("n")$, which shows that the image of the map $op("Gal")(K'/K) -> op("Gal")(k'/k)$ has order $r$, and hence is an isomorphism. Conversely, suppose that $k'/k$ is Galois. Again we write $k'=k(a)$ and $alpha in A'$ lifts $a$. It follows from *Hensel's Lemma* that $A'$ contains the conjugates of $alpha$, whence $K'$ is Galois over $K$.
]


#example(number: 276)[
  Let $K$ be a $p$-adic number field. As we will see in *Prop. 278*, its residue field $k$ is finite, say of order $q$. From the theory of finite fields, we find for each $n in bb("N")$ an extension field $k_n$ of $k$ of degree $n$ which is just the splitting field of $x^(q^n)-x$ (up to $k$-isomorphism). The Galois group is $op("Gal")(k_n/k) equiv bb("Z")/n bb("Z")$, which is generated by the Frobenius morphism $x mapsto x^q$.\ It follows that for all $n in bb("N")$, there exists an unramified extension field $K_n$ of $K$ of degree $n$ with the associated DVR $(B_n,frak("P")_n)$ which is unique up to $K$-isomorphism. The Galois group $op("Gal")(k_n/k) equiv bb("Z")/n bb("Z")$ is thus generated by the map $sigma_n:K_n -> K_n$ determined by the property
  $
    sigma_n(a) equiv a^q op("mod") frak("P")_n, quad text("for all") a in B_n.
  $

]


#corollary(number: "277", title: [Largest Unramified Extension])[
  \ Let $K_0 subset L$ be the compositum of all unramified extensions of $K$ in $L$. If $k$ is finite, then $K_0$ is obtained from $K$ by adjoining all roots of $1$ in $L$ of order prime to $op("char") k$. It carries a discrete valuation $| dot |_0$ with $nu_0(K_0^times )=nu(K)$. Its residue field is the separable closure of $k$. The field $K_0$ is called the *largest unramified extension* of $K$ in $L$. \ In particular, the largest unramified extension $K_(n r)$ ("non-ramifi\'{e}e") of $K$ is the largest unramified extension in its algebraic closure $overline(K)$ and its residue field is $overline(k)$, the algebraic closure of $k$.
]

#proof[
  Let $k_0$ denote the residue field $kappa(K_0)$ and $a in ell$ be separable over $k$. We need to show that $a in k$. Let $overline(g) in k[x]$ be the minimal polynomial of $a$ such that $overline(g) equiv g op("mod") frak("m")$ for some $g in A[x]$. By *Hensel*, there is a root $alpha in L$ with $alpha equiv a op("mod") frak("n")$, (note that the roots of $overline(g)$ are simple). But then
  $
    [K(alpha):K]=op("deg") g=op("deg") overline(g)=[k(a):k],
  $

  i.e. $K(alpha)$ is unramified over $K$. Hence we have $K(alpha) subset K_0, alpha in K_0$ and so $overline(alpha)=a in k_0$, which follows that $k_0$ is a separable element of $k$. \ Since every element of $K_0$ is contained in some finite extension field $K'$ with $K subset K' subset K_0$, we may assume that $K_0/K$ is finite. Then
  $
    [K_0:K] >= e f=(nu_(K_0)(K_0^times ):nu_K(K^times ))[k_0:k] =(nu_(K_0)(K_0^times ):nu_K(K^times ))[K_0:K],
  $

  whence $(nu_(K_0)(K_0^times ):nu_K(K^times ))=1$, i.e. $nu_(K_0)(K_0^times )=nu_K(K^times )$.\
  If $k$ is finite with $p=op("char") k$, then $f_m := x^m-1$ is separable if $p divides.not m$. Since $f_m(1)=0$ and $k_0$ is the separable closure of $k$, it follows that $k_0$ contains all the roots of $f_m$. By *Hensel's Lemma*, these lift to $K_0$. Since these roots of unity generate any finite extension of $k$ and thus any finite extension of $K$, they also generate $K_0$ since $K_0$ is exhausted by finite field extensions.\ Finally, consider the algebraic closure $overline(K)$ of $K$. If $overline(f) in k[x]$ with $f in A[x]$ and $overline(f) equiv f op("mod") frak("m")$, then $f in overline(K)[x]$ and thus splits completely in $overline(K)$, further, in $kappa(overline(K))[x]$. Since $kappa(overline(K))$ is algebraic over $k$, we have $kappa(overline(K))=k$.
]
