#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Discrete Valuation and Dedekind Rings


#motivation(number: "115")[
  Our next goal is to understand the ring of integers $cal("O")_K$ of an algebraic number field as a ring. In particular, we want to understand which of the good properties of $bb("Z")$ survive. This is a nontrivial question as the subsequent proposition and remark show.
]


#proposition(number: 116)[
  Every nonzero nonunit element of a Noetherian integral domain can be written as a product of irreducible elements (but not necessarily a unique way as for a UFD).
]

#proof[
  Recall that if $A$ is an integral domain, then $(a) subset (b) arrow.l.r.double b|a$. And the equality holds iff $a := b dot u$, for some $u in A^times$. We assume to the contrary that there exists $a in A$ which cannot be written as a product so that the set of ideals\
  $Sigma := {(a):a in A text("cannot be written as a product")} eq.not nothing$. \ $because A$ is Noetherian. $therefore exists$ maximal element $(a) in Sigma$. In particular, $a$ cannot be irreducible and so $a=b dot c$ for some nonunits $b,c in A$. Hence $(a) subset.not.eq (b)$, so that by maximality of $(a)$, $b$ admits a decomposition into irreducibles. Interchanging the roles of $b$ and $c$ yields a decomposition of $c$. Thus $a$ is a product of irreducible elements, a contradiction.
]


#remark(number: 117)[
  The *Prop. 116* fails for instance for the ring $cal("O")_(overline(bb("Q")))$ of algebraic integers in the algebraic closure of $bb("Q")$ in $bb("C")$. Indeed, an algebraic integer $alpha in cal("O")_(overline(bb("Q")))$ cannot be irreducible for $sqrt(alpha)$ is also in $cal("O")_(overline(bb("Q")))$ and $alpha=sqrt(alpha) dot sqrt(alpha)$. In particular, $cal("O")_(overline(bb("Q")))$ is neither a UFD nor Noetherian.
]


However, we will see that $cal("O")_K$ is a Dedekind ring and as such it still retains certain factorisation properties.

#proposition(number: "118", title: [Discrete Valuation Ring])[
  Let $A$ be a PID. Then T.F.A.E.:
  - _(a)_ $A$ has exactly one nonzero prime ideal.
  - _(b)_ Up to multiplying with units, $A$ has exactly one prime element.
  - _(c)_ $A$ is local and not a field.

  A PID satisfying one and thus all of these conditions is called a *discrete valuation ring (DVR)*.
]


#example(number: 119)[
  The localisation $bb("Z")_((p)) := {frac(m, n) in bb("Q"):p divides.not n}$ is a DVR with $(p)^e$ as its unique nonzero prime ideal. Up to multiplying with units, $p$ is the unique prime element. Any other element in $bb("Z")_((p))$ is of the form $p^k dot frac(m, n)$ with $p divides.not m,n$. The group of units is given by $bb("Z")^times_((p))={frac(m, n) in bb("Q"):p divides.not m,n}$, that is, the element of $bb("Z")_((p))$ with vanishing exponent $k$.
]


#proposition(number: 120)[
  An integral domain $A$ is a DVR iff $A$ is \ (i) Noetherian, (ii) integrally closed, and (iii) has exactly one nonzero prime ideal.
]

#proof[
  "$arrow.r.double$"\ is obvious. "$arrow.l.double$"\ Suppose $A$ is an integral domain satisfying (i)-(iii). We must show that every ideal in $A$ is principal. Note: (iii) implies that $A$ is a local ring.\
  *Step 1.* The nonzero prime ideal is principal.\ proof.
  Choose a nonunit element $0 eq.not c in A$ and consider the $A$-module $M := A/(c)$. For each $0 eq.not m in M$, note that
  $
    op("Ann")(m) := {a in A:a m=0} lt.closed.not A.
  $

  $because A$ is Noetherian. $therefore$ We may choose an $m in M$ so that $op("Ann")(m)$ is maximal among these ideals. Write $m := b+(c)$ and $frak("p") := op("Ann") (b+(c))$. Note that $c in frak("p")$, thus
  $
    frak("p")={a in A: c|a b } eq.not 0.
  $

  *Claim 1.* $frak("p")$ is prime. If not, there exist elements $x,y in A without frak("p")$ such that $x y in frak("p")$. Then $y b+(c) eq.not 0+(c)$ in $M$ since $y in.not frak("p")$. Consider $op("Ann")(y b+(c))$, which obviously contains $frak("p")$ and $x$, but this contradicts the maximality of $frak("p")$ among ideals of the form $op("Ann")(m)$. Hence $frak("p")$ is prime, thus maximal by (iii).\
  *Claim 2.* $frac(b, c) in.not A$. Otherwise $b=c dot frac(b, c) in (c)$, and $m=0$ in $M$.\
  *Claim 3.* $frac(c, b) in A$ and $frak("p")=(frac(c, b))$. By definition, $frak("p")b subset (c)$, and so $frak("p") dot frac(b, c) subset A$, thus an ideal in $A$.\ If $frak("p") dot frac(b, c) subset frak("p")$, then $frac(b, c)$ is integral over $A$ by *Prop. 93*. Thus, by (ii), $frac(b, c) in A$, which contradicts to the previous Claim. Thus, by (iii), $frak("p") dot frac(b, c)=A. because A$ is local.  $therefore A without frak("p")=A^times . arrow.r.double frak("p")= (frac(c, b))$.\
  *Step 2.* Every proper ideal $frak("a") lt.closed.not A$ is principal.\ proof.
  Put $pi := frac(c, b)$ so that $frak("p")=(pi)$. Consider the sequence
  $
    frak("a") subset frak("a")pi^(-1) subset frak("a")pi^(-2) subset dots.h.c .
  $

  If $frak("a")pi^(-r)=frak("a")pi^(-r-1)$ for some $r$, then $pi^(-1)(frak("a")pi^(-r))=frak("a")pi^(-r)$, it follows that $pi^(-1)$ is integral over $A$ by *Prop. 93*. Again by (ii), $pi^(-1) in A$, but this contradicts to *Claim. 2*. Therefore the sequence is strictly increasing, and it can't be contained in $A$, since $A$ is Noetherian.\
  Let $m in bb("N")$ be the smallest integer such that $frak("a")pi^(-m) subset A$ but $frak("a")pi^(-m-1) subset.not A$. Then  $frak("a")pi^(-m) subset.not frak("p")$, (otherwise  $frak("a")pi^(-m-1) subset A$). $because A$ is local. $therefore frak("a")pi^(-m)=A. arrow.r.double frak("a") =(pi^m)$ is principal.
]


#definition(number: "121", title: [Dedekind Domain])[
  A *Dedekind domain* is an integral domain $A$, not equal to a field such that $A$ is \ (i) Noetherian, (ii) integrally closed, and (iii) every nonzero prime ideal is maximal.\
  It follows that a local integral domain is Dedekind iff it is a DVR.
]


#example(number: 122)[
  The algebraic integers $cal("O")_K$ of a number field form a Dedekind domain. (cf. *Cor. 135.*)
]


#proposition(number: 123)[
  Let $A$ be a Dedekind domain and $S$ be a multiplicative subset of $A$. Then $S^(-1)A$ is either a Dedekind domain or a field.
]

#proof[
  Note: the prime ideals of $S^(-1)A$ correspond to those of $A$ which have empty intersection with $S$. Hence, localisation preserves condition (iii). It also preserves conditions (i) and (ii) as noted in *Chapter 1*.
]


#proposition(number: 124)[
  For any nonzero prime ideal $frak("p") eq.not 0$ in a Dedekind domain $A$, the localisation $A_frak("p")$ is a DVR.
]

#proof[
  Note: $A_frak("p")$ is local. Moreover, $A_frak("p")$ is integrally closed and Noetherian by *Prop. 114* and [AM, 7.4], respectively.
]


#theorem(number: 125)[
  Let $A$ be a Dedekind domain. Every proper nonzero ideal $frak("a") lt.closed A$ can be written in the form
  $
    frak("a") := frak("p")_1^(r_1) dots.h.c frak("p")_n^(r_n)
  $

  with uniquely determined distinct prime ideals $frak("p")_i lt.closed A$ and $r_i>0$. Furthermore, \ $r_i>0 quad arrow.l.r.double quad frak("a")A_(frak("p")_i) subset.not.eq A_(frak("p")_i) quad arrow.l.r.double quad frak("a") subset frak("p")_i$.
]


The proof will require the following lemmas:

#lemma(number: 126)[
  Let $A$ be a Noetherian ring. Then every ideal $frak("a") lt.closed A$ contains a product of nonzero prime ideals.
]

#proof[
  Suppose not, and choose a maximal counterexample $frak("a") lt.closed A$, (since $A$ is Noetherian). Then $frak("a")$ itself cannot be prime, and so there exist $x,y in A without frak("a")$ such that $x y in frak("a")$. Now, the ideals $frak("a")+(x)$ and $frak("a")+(y)$ strictly contain $frak("a")$, but their product is contained in $frak("a")$. By maximality of $frak("a")$, each of $frak("a")+(x)$ and $frak("a")+(y)$ contains a product of prime ideals, thus, so does $frak("a"). ( -> arrow.l )$
]


#lemma(number: 127)[
  Let $A$ be a ring, and $frak("a"), frak("b")$ be relatively prime ideals in $A$. Then for any $m,m in bb("N")$, the ideals $frak("a")^m$ and $frak("b")^n$ are relatively prime.
]

#proof[
  If $frak("a")^m$ and $frak("b")^n$ are not relatively prime, then they are both contained in some prime (even maximal) ideal $frak("p")$, i.e. $frak("a")^m+frak("b")^n subset frak("p")$. Now, both $frak("a")^m, frak("b")^n subset frak("p")$, it follows that both $frak("a"), frak("b") subset frak("p")$. But this contradicts that $frak("a")$ and $frak("b")$ are relatively prime, (i.e. $frak("a")+ frak("b") =A$).
]


#lemma(number: 128)[
  Let $frak("p")$ be a maximal ideal of a ring $A$, and $frak("q") := frak("p")A_frak("p")$ be the maximal ideal of the localisation $A_frak("p")$. Then the map
  $
    A/frak("p")^m arrow.r.long A_frak("p")/frak("q")^m, a+frak("p")^m arrow.r.long.bar a+frak("q")^m
  $

  is an isomorphism.
]

#proof[
  *Claim 1.* The map is 1-1. It suffices to show that $frak("q")^m inter A=frak("p")^m$. \ proof.
  $because frak("q")^m=S^(-1) frak("p")^m, text("where") S := A without frak("p"). therefore$ We have to show that $frak("p")^m=(S^(-1) frak("p")^m) inter A$. \ "$subset$"\ is clear since $a=frac(a, 1) in (S^(-1) frak("p")^m) inter A$ for any $a in frak("p")^m$. "$supset$"\ Let $a := frac(b, s) in (S^(-1) frak("p")^m) inter A, text("where")\ b in frak("p")^m, s in S, a in A. because s a=b in frak("p")^m. therefore overline(s a)=overline(0)$ in $A/frak("p")^m$. Note: The only maximal ideal containing $frak("p")^m$ is $frak("p")$ (since $frak("m") supset frak("p")^m text("implies") frak("m") supset frak("p")$), so the only maximal ideal in $A/frak("p")^m$ is $frak("p")/frak("p")^m$; in fact, $A/frak("p")^m$ is a local ring. $because s in S=A without frak("p"). therefore overline(s)=s+frak("p")^m in.not frak("p")/frak("p")^m. arrow.r.double overline(s) in (A/frak("p")^m)^times .\ arrow.r.double overline(a)=overline(s)^(-1) dot overline(s a)=overline(s)^(-1) dot overline(0)=overline(0)$ in $A/frak("p")^m. arrow.r.double a in frak("p")^m$.\
  *Claim 2.* The map is surjective. \ proof.
  Let $overline(frac(a, s)) in A_frak("p")/frak("q")^m$, where $a in A, s in S. because s in.not frak("p")$ and $frak("p")$ is maximal. $therefore (s)+frak("p")=A$, i.e. $(s)$ and $frak("p")$ are relatively prime. By *Lemma. 127*, $(s)$ and $frak("p")^m$ are also relatively prime. $arrow.r.double exists b in A, q in frak("p")^m$ such that $b s+q=1. arrow.r.double 1+frak("p")^m=b s+frak("p")^m mapsto overline(b s)=overline(1)$ in $A_frak("p")/frak("q")^m.\ arrow.r.double b+frak("p")^m mapsto overline(b)=frac(1, overline(s))$. Thus, $b a+frak("p")^m mapsto overline(b a)=overline(b) dot overline(a)=frac(1, overline(s)) dot overline(a)= overline(frac(a, s))$.
]


#proofthm(number: "125")[
  We now prove that a nonzero ideal $0 eq.not frak("a") lt.closed A$ can be factorised into a product of prime ideals. By *Lemma 126*, $frak("a")$ contains a product of nonzero prime ideals $frak("b") := frak("p")_1^(s_1) dots.h.c frak("p")_n^(s_n)$.
  We may suppose that the $frak("p")_i$'s are distinct. Then,
  $
    A/frak("b") tilde.equiv A/frak("p")_1^(s_1) times dots.h.c times A/frak("p")_n^(s_n) tilde.equiv A_(frak("p")_1)/frak("q")_1^(s_1) times dots.h.c times A_(frak("p")_n)/frak("q")_1^(s_n),
  $

  where $frak("q")_i := frak("p")_i A_(frak("p")_i)$ is the maximal ideal of $A_(frak("p")_i)$. Here, the 1st isomorphism gives by the *CRT* and *Lemma 127* and the 2nd gives by *Lemma 128*. Under this isomorphism, there is a correspondence
  $
    frak("a")/frak("b") arrow.l.r.long frak("q")_1^(r_1)/frak("q")_1^(s_1) times dots.h.c times frak("q")_n^(r_n)/frak("q")_1^(s_n)
  $

  for some $r_i <= s_i$ (recall that each $A_(frak("p")_i)$ is a DVR by *Prop. 124*). Since this ideal is also the image of $frak("p")_1^(r_1) dots.h.c frak("p")_n^(r_n)$ under the isomorphism, we see that
  $
    frak("a")= frak("p")_1^(r_1) dots.h.c frak("p")_n^(r_n) text("in") A/frak("b").
  $

  Both of these ideals contain $frak("b")$, which follows from the *Correspondence Thm.* that
  $
    frak("a")= frak("p")_1^(r_1) dots.h.c frak("p")_n^(r_n) text("in") A.
  $

  Moreover, this factorisation is unique since each $r_i$ is uniquely determined by the condition\ $frak("a") A_(frak("p")_i)=frak("q")_i^(r_i), text("where") frak("q")_i lt.closed A_(frak("p")_i)$ maximal ideal.
]


#corollary(number: "129", title: [Local Criterion for Equality])[
  Let $frak("a"),frak("b")$ be ideals in $A$. Then
  $
    frak("a") subset frak("b") quad arrow.l.r.double.long quad frak("a")A_frak("p") subset frak("b")A_frak("p"), forall 0 eq.not frak("p") lt.closed A text("prime ideals").
  $

  In particular, $frak("a")=frak("b")$ iff $frak("a")A_frak("p")= frak("b")A_frak("p")$.
]

#proof[
  "$arrow.r.double$"\ is obvious. "$arrow.l.double$"\ Factor $frak("a")$ and $frak("b")$ into
  $
    frak("a") := frak("p")_1^(r_1) dots.h.c frak("p")_n^(r_n), quad frak("b") := frak("p")_1^(s_1) dots.h.c frak("p")_n^(s_n), quad (r_i,s_i >= 0).
  $

  Then
  $
    frak("a")A_frak("p") subset frak("b")A_frak("p") quad arrow.l.r.double.long quad r_i >= s_i text("for all") i,
  $

  (recall that $A_(frak("p")_i)$ is a DVR) and $r_i >= s_i$ implies that $frak("a") subset frak("b")$.
]


#corollary(number: 130)[
  Let $A$ be an integral domain with only finitely many prime ideals. Then $A$ is a Dedekind domain iff it is a PID.
]

#proof[
  Assume $A$ is a Dedekind domain. By *Thm. 125*, it suffices to show that the prime ideals are principal. Let $frak("p")_1, dots.h.c , frak("p")_m$ be all prime ideals in $A$. We consider the element $x in frak("p")_1 without frak("p")_1^2$. By *CRT*, there is an element $x in A$ such that
  $
    x equiv x_1 (op("mod") frak("p")_1^2) quad text("and") quad x equiv 1 (op("mod") frak("p")_i), forall i eq.not 1.
  $

  Now, the ideals $frak("p")_1$ and $(x)$ generate the same ideals in $A_(frak("p")_i)$ for all $i$. Hence, by *Cor. 129*, we obtain  $frak("p")_1=(x)$ in $A$.
]


#corollary(number: 131)[
  Let $0 eq.not frak("a") subset frak("b")$ be two ideals in a Dedekind domain $A$, then $frak("b") := frak("a")+(a)$, for some $a in A$. In particular, if $0 eq.not a in frak("b")$, then there exists $b in frak("b")$ such that $frak("b")= (a,b)$.
]

#proof[
  Let $frak("a") := frak("p")_1^(r_1) dots.h.c frak("p")_n^(r_n), frak("b") := frak("p")_1^(s_1) dots.h.c frak("p")_n^(s_n), (r_i,s_i >= 0). because frak("a") subset frak("b"). therefore s_i <= r_i, forall i$. Now, for each $1 <= i <= m, exists x_i in A$ such that $x_i in frak("p")_i^(s_i)$ but $x_i in.not frak("p")_i^(s_i+1)$. By *CRT*, $exists a in A$ such that $a equiv x_i (op("mod") frak("p")_i^(r_i)), forall i$. Now one sees that $frak("b")+(a)=frak("a")$ by looking at the ideals they generated in $A_(frak("p")),$ for all prime ideal $frak("p") lt.closed A$. Apply the first part to $0 eq.not (a) subset frak("b")$, we get the last sentence.
]


#corollary(number: 132)[
  Let $frak("a")$ be a nonzero ideal in a Dedekind domain $A$. Then there exists a nonzero ideal $frak("a")^ast lt.closed A$ such that $frak("a") dot frak("a")^ast$ is principal. Moreover, $frak("a")^ast$ can be chosen to be either relatively prime to any particular ideal $frak("b") lt.closed A$, or it can be chosen so that $frak("a") dot frak("a")^ast =(a)$ with $a$ any particular element of $frak("a")$ (but not both).
]

#proof[
  Let $0 eq.not a in frak("a")$, then $(a) subset frak("a")$. By *Thm. 125*, we have
  $
    (a) := frak("p")_1^(r_1) dots.h.c frak("p")_n^(r_n), text("and") frak("a") := frak("p")_1^(s_1) dots.h.c frak("p")_n^(s_n), quad (s_i <= r_i).
  $

  If $frak("a")^ast := frak("p")_1^(r_1-s_1) dots.h.c frak("p")_n^(r_n-s_n)$, then $frak("a") frak("a")^ast =(a)$.\
  We now show that $frak("a")^ast$ can be chosen to be prime to $frak("b")$. We have $frak("a") supset frak("a") frak("b")$, so by *Cor. 131*, $exists a in frak("a")$ such that $frak("a")=frak("a") frak("b")+(a)$. As $frak("a") subset (a)$, we have $(a)=frak("a") dot frak("a")^ast$ for some ideal $frak("a")^ast lt.closed A$ (by the above argument); now, $because frak("a") frak("b")+frak("a") frak("a")^ast =frak("a"). therefore frak("b")+frak("a")^ast =A$. (Otherwise $frak("b")+frak("a")^ast subset frak("p")$ for some prime ideal $frak("p") lt.closed A. arrow.r.double frak("a") frak("b")+frak("a") frak("a")^ast =frak("a") (frak("b")+frak("a")^ast ) subset frak("a") frak("p") eq.not frak("a")$.)
]


#lemma(number: 133)[
  Let $A subset B$ be an integral ring extension of integral domains. Then\ $A$ is a field $quad arrow.l.r.double.long quad B$ is a field. [AM, 5.7]
]

#proof[
  "$arrow.r.double$"\ Suppose $A$ is a field. Let $0 eq.not x in B$, we claim: $x^(-1)$ exists and $x^(-1) in B$.\
  $because x in B$ and $B$ is integral over $A. therefore x$ satisfies  $x^n+a_1 x^(n-1)+ dots.h.c +a_n=0$ in $B$, for some $a_i in A$, where $n in bb("N")$ may be chosen to be the smallest possible degree. Note that if $a_n=0, because B$ is an ID. $therefore$ Either $x=0$ or $x^(n-1)+a_1 x^(n-2)+ dots.h.c +a_(n-1)= 0$. But $x in B$ is chosen to be nonzero and $n in bb("N")$ is chosen to be the smallest. $( -> arrow.l )$. Thus, $a_n eq.not 0$ in $A. because A$ is a field. $therefore a_n^(-1)$ exists in $A$. Hence $x^(-1) := -a_n^(-1)(x^(n-1)+a_1 x^(n-2)+ dots.h.c +a_(n-1))$ exists in $B$.\
  "$arrow.l.double$"\ Suppose $B$ is a field. Let $0 eq.not x in A subset B$, then $exists x^(-1) in B$. We claim: $x^(-1) in A$. \
  $because B$ is integral over $A. therefore x^(-1)$ satisfies $x^(-m)+a_1 x^(-m+1)+ dots.h.c +a_(m-1)x^(-1)+a_m=0$ in $B text("where") a_i in A$. Multiplying $x^(m-1)$, we have $x^(-1)+a_1+a_2 x+ dots.h.c +a_m x^(m-1)=0$ in $B$. Hence, we obtain  $x^(-1)=-(a_1+a_2 x+ dots.h.c +a_m x^(m-1)) in A$.
]


#theorem(number: "134", title: [Special Case of Akizuki-Krull])[
  Let $A$ be a Dedekind domain with $K := op("Quot")(A)$ and $B$ be the integral closure of $A$ in a finite separable extension $L$ of $K$. Then $B$ is a Dedekind domain. [AM, 5.17]
]

#proof[
  We check the 3 conditions of *Def. 121*.
  - (_$B$_ is Noetherian). $because A$ is Noetherian. $therefore$ By *Prop. 112*, $B$ is contained in a finitely generated $A$-module. It follows that every ideal in $B$ is finitely generated as an $A$-module (being a submodule of a Noetherian $A$-module), and a fortiori as an ideal (i.e. $B$-module). Thus, $B$ is Noetherian.
  - (_$B$_ is integrally closed). $overline(B)=overline(overline(A)) =overline(A)=B$.
  - (Every nonzero prime ideal $0 eq.not frak("q") lt.closed B$ is maximal).\ Let $0 eq.not b in frak("q"), because B$ is integral over $A. therefore b$ satisfies $b^n+a_1 b^(n-1)+ dots.h.c +a_n=0$, for some $a_i in A$, where $n in bb("N")$ may be chosen to be the smallest possible degree. Then $a_n eq.not 0$, which comes from the proof in *Lemma 133*. $because a_n in (b) inter A. therefore frak("p") := frak("q") inter A eq.not (0)$. Moreover, $frak("p")$ is a prime ideal of $A. because A$ is local. $therefore frak("p")$ must be maximal. $arrow.r.double A/frak("p")$ is a field. Note that the inclusion $A arrow.r.hook B$ extends to an integral extension
  $
    A/frak("p") arrow.r.hook B/frak("q"), quad a+frak("p") arrow.r.long.bar a+frak("q")
  $

  of IDs. $because A/frak("p")$ is a field, so is $B/frak("q")$ by *Lemma 133*, and hence $frak("q") lt.closed B$ is maximal.

  Therefore, $B$ is a Dedekind domain.
]


#corollary(number: 135)[
  The ring of integers $cal("O")_K$ of an algebraic number field $K$ is a Dedekind domain. [AM, 9.5]
]
