#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Ramification

For the remainder of this section, let $A$ be a Dedekind domain, $K=op("Quot")A$, and $B$ be the integral closure of $A$ in a finite separable extension $L$ of $K$. Then $B$ is also Dedekind. The prototype of this setup will be $A=bb("Z"), K=bb("Q")$ with $B=bb("Z")[i]$ in $L=bb("Q")(i)$.

#definition(number: "155", title: [Ramification])[
  We first extend a prime ideal $frak("p") lt.closed A$ to $B$, where it factorises into
  $
    frak("p")^e=frak("p")B := frak("P")_1^(e_1) dots.h.c frak("P")_g^(e_g), (e_1 >= 1).
  $

  - If there is $i$ with $e_i>1$, we say that $frak("p")$ *ramifies* in $B$ (or $L$). The number $e_i$ is called the *ramification index* at $frak("P")_i$.
  - We say that $frak("P")$ *divides* $frak("p")$ if $frak("P")$ occurs in the factorisation of $frak("p")$ in $B$. We then write $frak("P")_i|frak("p")$ and $e_i=e(frak("P")_i/frak("p"))$ for the ramification index.
  - The *residue class degree* $f_i=f(frak("P")_i/frak("p"))$ is defined to be $[B/frak("P")_i:A/frak("p")]$.
  - A prime $frak("p")$ is said to *split* in $L$ if $e=f=1$ for all $i$; and is said to be *inert* in $L$ if $frak("p")B$ is a prime ideal in $B$, (i.e. $e=g=1$.)

]


#lemma(number: 157)[
  A prime ideal $frak("P") lt.closed B$ divides a prime ideal $frak("p") lt.closed A$ iff $frak("p")=frak("P") inter K$. In particular, $frak("P")$ divides at most one prime ideal.
]

#proof[
  "$arrow.r.double$"\ Since $frak("p")B subset frak("P")$, we have $frak("p") subset frak("P") inter K subset.not.eq A$. Otherwise, if $frak("P") inter K=A$, then $1 in frak("P"). ( -> arrow.l )$. As $frak("p")$ is maximal, this implies that $frak("p")=frak("P") inter K$.\ "$arrow.l.double$"\ $because frak("p")=frak("P") inter K. therefore frak("p")B subset frak("P")$. Thus, by *Thm. 125*, $frak("P")$ occurs in the factorisation of $frak("p")B$.
]


#theorem(number: 158)[
  Let $m := [L:K]$ and let $frak("P")_1, dots.h.c ,frak("P")_g lt.closed B$ be the prime ideals dividing the prime ideal $frak("p") lt.closed A$. Then $sum_(i=1)^g e_i f_i=m$.\
  Moreover, if $L/K$ is Galois, then all the ramification indices and residue class degrees are equal, whence $e f g=m$.
]

#proof[
  We divide the proof into two parts.\
  claim 1. To prove $sum_(i=1)^g e_i f_i=m$, we show that both sides equal $[B/frak("p")B:A/frak("p")]$.\
  (lhs): Note that from *CRT*, $B/frak("p")B=B/ product frak("P")_i^(e_i) tilde.equiv product (B/frak("P")_i^(e_i))$, thus it suffices to show that each $[B/frak("P")_i^(e_i):A/frak("p")]= e_i f_i$. From the definition of $f_i$, we know that $B/frak("P")_i$ is a field of degree $f_i$ over $A/frak("p")$. For each $r_i, frak("P")_i^(r_i)/frak("P")_i^(r_i+1)$ is a $B/frak("P")_i$-module (thus, vector space). Since there is no ideal $frak("b") lt.closed B$ such that $frak("P")_i^(r_i+1) subset.not.eq frak("b") subset.not.eq frak("P")_i$,  it must have dimension $1$ as a $B/frak("P")_i$-vector space, and hence dimension $f_i$ as an $A/frak("p")$-vector space. Therefore each quotient in the chain
  $
    B supset frak("P")_i supset frak("P")_i^2 supset dots.h.c supset frak("P")_i^(e^i)
  $

  has dimension $f_i$ over $A/frak("p")$. Thus $[B/frak("P")_i^(e_i):A/frak("p")]= e_i f_i$.\
  (rhs): We first assume that $A$ is a PID, by *Rmk. 113* $B$ admits an integral basis which is a $K$-basis over for $L$, hence $B equiv A^m$. Consider the exact sequence $0 -> A^m attach(arrow.r.long, t: tilde) B -> 0$, and apply the (right) exact functor $- times.o_A A/frak("p")$, which yields that
  $
    0 arrow.r.long A^m times.o_A(A/frak("p")) arrow.r.long B times.o_A(A/frak("p")) arrow.r.long 0.
  $

  Moreover, $A^m times.o_A(A/frak("p")) equiv (A times.o_A(A/frak("p")))^m equiv (A/frak("p"))^m$ as an $A$-module, thus as an $A/frak("p")$-module. Further, the short exact sequence $0 -> frak("p") arrow.r.hook A arrow.r.twohead A/frak("p") -> 0$ applying the functor $B times.o_A-$ gives
  $
    B times.o_A frak("p") arrow.r.long B times.o_A A equiv B arrow.r.twohead B times.o_A A/frak("p") arrow.r.long 0.
  $

  This induces that $B/frak("p")B equiv B times.o_A A/frak("p")$ (the image of $B times.o_A frak("p") -> B, b times.o a mapsto a dot b$ is just $frak("p")B$), whence $B/frak("p")B equiv (A/frak("p"))^m$ is free and thus $[B/frak("p")B:A/frak("p")]=m$.\
  Now, if $A$ is not a PID, we let $S$ be a multiplicative subset of $A$ disjoint from $frak("p")$ such that $S^(-1)A$ is principal (the localisation of a Dedekind ring), (e.g. $S=A without frak("p")$). Write $A' := S^(-1)A$ and $B' := S^(-1)B$, then, by *Rmk. 141*, we have $frak("p")B'= product (frak("P")_i B')^(e_i)$. It follows that $sum_(i=1)^g e_i f_i=[B'/frak("p")B':A'/frak("p")A']$ since $B'$ is a free $A'$-module; but $A'$ is also principal, thus $[B'/frak("p")B':A'/frak("p")A']=m$.\
  claim 2. Now assume that $L/K$ is Galois. We note that
  - $sigma in op("Gal")(L/K)$ maps $B$ isomorphically to itself, since an integral relation $x^n+ sum a_i x^i=0$ for $x in L$ is mapped to an integral relation $sigma(x)^n+ sum a_i sigma(x)^i=0$, whence $sigma(n) in B$.
  - In particular, if $frak("P") lt.closed B$ is a prime ideal, then so is $op("sigmafrak")("P") subset B$.
  - If $frak("P")|frak("p")$, it follows from *Lemma 157* that $frak("p")=op("sigmafrak")("P") inter K$ (since $sigma|_K=1_K$), so that $op("sigmafrak")("P")|frak("p")$.
  - Since $sigma|_B$ is a ring isomorphism, we have $e(sigma frak("P")/frak("p"))=e(frak("P")/frak("p"))$ and $f(op("sigmafrak")("P")/frak("p"))=f(frak("P")/frak("p"))$

  Thus, it remains to show that $op("Gal")(L/K)$ acts transitively on the prime ideals of $B$ dividing $frak("p")$.\
  Suppose $frak("Q")$ also divides $frak("p")$ but is not conjugate to $frak("P")$, i.e. $op("sigmafrak")("P") eq.not frak("Q"), forall sigma in op("Gal")(L/K)$. By *CRT* we can choose $b in B$ with $b equiv 0 (op("mod") frak("Q"))$ and $b equiv 1 (op("mod") op("sigmafrak")("Q")), forall sigma in op("Gal")(L/K)$ so that $b in frak("Q")$ but $b in.not op("sigmafrak")("P")$, and thus $sigma(b) in.not frak("P"), forall sigma in op("Gal")(L/K)$. By integrality of $b$, we have $a := op("N")_(L/K)(b)= product sigma (b) in A$. Since $a=b dot product_(sigma eq.not epsilon)sigma(b) in frak("Q")$, we have $a in frak("Q") inter A=frak("p")$. On the other hand, for each $sigma in op("Gal")(L/K), sigma(b) in.not frak("P")$ and $a= product sigma(b) in frak("p") subset frak("P")$ contradicts the primality of $frak("P"). ( -> arrow.l )$
]


#remark(number: 159)[
  This theorem has a very nice geometric interpretation in terms of ramified coverings of curves provided $f_i=1$ for all $i$, for instance, if the fields $A/frak("p")$ are algebraically closed as for $A=k[x], (k: text("algebraically closed"))$.
]


#theorem(number: 160)[
  Let $A$ be a Dedekind domain, $K := op("Quot")A$, $L/K$ a finite field extension and $B$ be the integral closure of $A$ in $L$. Assume that $B tilde.equiv A^m$ (e.g. if $A$: PID). Then a prime ideal $frak("p") lt.closed A$ ramifies in $L$ iff $frak("p")|op("disc")(B/A)$. In particular, only finitely many prime ideals ramify.
]


Recall *Def. 107* for the definition of discriminant. We subdivide the proof into several lemmas:
#lemma(number: 161)[
  Let $A subset B$ be a ring extension such that $B equiv A^m$ with finite $A$-basis ${e_1, dots.h.c ,e_m }$. For any ideal $frak("a") lt.closed A, {overline(e_1), dots.h.c ,overline(e_m)}$ is an $A/frak("a")$-basis for $B/frak("a")B$ and \
  $D(overline(e_1), dots.h.c ,overline(e_m)) equiv D(e_1, dots.h.c ,e_m) quad (op("mod") frak("a"))$.
]

#proof[
  As in the proof of *Thm. 158*, the isomorphism gives
  $
    A^m arrow.r.long B, quad (a_1, dots.h.c ,a_m) arrow.r.long.bar sum a_i e_i
  $

  gives, when applying the right exact functor $- times.o_A(A/frak("a"))$, an isomorphism
  $
    (A/frak("a"))^m arrow.r.long B/frak("a"), quad (a_1, dots.h.c ,a_m) arrow.r.long.bar sum a_i overline(e_i)
  $

  which shows that ${overline(e_1), dots.h.c ,overline(e_m)}$ is an $A/frak("a")$-basis for $B/frak("a")B$. Note that moding out $frak("a")B$ gives
  $
    op("det(Tr")_((B/frak("a")B)/(A/frak("a")))(overline(e_i) dot overline(e_j)))=overline(op("det(Tr")_(B/A)(e_i dot e_j))),
  $

  whence the second result.
]


#lemma(number: 162)[
  Let $A subset B_1, dots.h.c ,B_g$ be the ring extensions such that each $B_i$ is a free $A$-module of finite rank. Then\
  $op("disc")(( product B_i)/A) = product op("disc") (B_i/A)$.
]

#proof[
  For each $1 <= i <= g$, choose an $A$-basis $beta_i={e_(i j)}_(j=1)^(m_i)$ for $B_i equiv A^(m_i)$. Then the matrix $[op("Tr")_(( product B_i)/A)(e_(i_j) dot e_(i_k))]_(1 <= j,k <= m_i)$ has the block form
  $mat(
    op("Tr")_(B_1/A)(e_(1_j)e_(1_k)), O, dots.h.c, O;
    O, dots.down, dots.down, dots.v;
    dots.v, dots.down, dots.down, O;
    O, dots.h.c, O, op("Tr")_(B_g/A)(e_(g_j)e_(g_k))
  )$
  and the result follows from the standard properties of the determinant.
]


#lemma(number: 163)[
  Let $k$ be a perfect field and $B$ be a $k$-algebra of finite dimension. Then\  $B$ is reduced $arrow.l.r.double.long op("disc")(B/k) eq.not 0$.
]

*Recall.* A ring is reduced if it has no nonzero nilpotents.
#proof[
  "$arrow.l.double$"\ We suppose to the contrary. Let $0 eq.not beta in B$ be nilpotent and choose a $k$-basis ${e_1=beta,e_2, dots.h.c ,e_m }$ for $B$. Then $beta e_i$ is nilpotent for all $i$, and so the $k$-linear map
  $
    B arrow.r.long B, quad x arrow.r.long.bar beta e_i x
  $

  is nilpotent. Its matrix is also nilpotent, but a nilpotent matrix has trace $0$ -- its minimum polynomial (and hence characteristic polynomial) is of the form $X^r$ -- and so the first row of the matrix $[op("Tr")(e_i e_j)]$ vanishes. Therefore its determinant (the generator of $op("disc")(B/k)$) is $0. ( -> arrow.l )$\
  "$arrow.r.double$"\ Suppose $B$ is reduced. We first show that the intersection $frak("N")$ of the prime ideals of $B$ is $0$, i.e. the *nilradical* $frak("N")= inter.big {frak("p") lt.closed B: text("prime")}={0}$.  This, in fact, is true for any reduced Noetherian ring, cf. [AM, 7.15]. Now let $frak("p") lt.closed B$ be a prime ideal, then the inclusion $k subset B/frak("p")$ descends to an integral ring extension since $B$ is of finite type over $k$, thus $B/frak("p")$ is a field by *Lemma 133*. Therefore $frak("p")$ is maximal. Now, let $frak("p")_1, dots.h.c ,frak("p")_r lt.closed B$ be prime (thus, maximal) ideals, then they are pairwise relatively prime. By *CRT*, we have $B/( inter.big frak("p")_i) equiv product (B/frak("p")_i)$. Note that
  $
    [B:k] >= [B/( inter.big frak("p")_i):k]= sum [B/frak("p")_i:k] >= r.
  $

  Therefore $B$ has only finitely many prime ideals, say $frak("p")_1, dots.h.c , frak("p")_g$ where $g <= [B:k]$ and $inter.big_(i=1)^g frak("p")_i=0$ (since $B$ is reduced). Again by *CRT*, we have $B equiv product_(i=1)^g (B/frak("p")_i)$.\
  For each $i$, since $B/frak("p")_i supset k$ is a finite extension and $k$ is perfect, it is also separable extension. Hence $op("disc")((B/ frak("p")_i)/k) eq.not 0$ by *Prop. 110*. Applt *Lemma 162*, we deduce that $op("disc")(B/k) eq.not 0$.
]


#proofthm(number: 160)[
  The idea is that a prime ideal $frak("p")$ that ramifies in $B$ gives rise to a non-reduced ring $B/frak("p")^r$, and this can be detected via the discriminant. From *Lemma 161*, we see that
  $
    op("disc")(B/A) (op("mod") frak("p")) = op("disc")((B/frak("p")B)/(A/frak("p"))),
  $

  and from *Lemma 163* that
  $
    op("disc")((B/frak("p")B)/(A/frak("p")))=0 arrow.l.r.double.long B/frak("p")B text("is not reduced").
  $

  Now let $frak("p")B := product frak("P")_i^(e_i)$. Then $B/frak("p")B tilde.equiv product (B/frak("P")_i^(e_i))$ and
  $
    product (B/frak("P")_i^(e_i)) text("is reduced") arrow.l.r.double.long B/frak("P")_i^(e_i) text("is reduced"), forall i arrow.l.r.double.long e_i=1, forall i.
  $

]


Next we want to compute some explicit examples.
#proposition(number: 164)[
  Let $A$ be a Dedekind domain, $K := op("Quot")A$, $L/K$ a finite separable extension and $B$ be the integral closure of $A$ in $L$. Furthermore, assume that $B=A[alpha]$. Let $f=f_alpha$ be the minimum polynomial of $alpha$ over $K$ and $frak("p") lt.closed A$ a prime ideal. Choose monic polynomials $g_1, dots.h.c ,g_r in A[x]$ that are distinct and irreducible modulo $frak("p")$, and such that $f equiv product g_i^(e_i) (op("mod") frak("p"))$. Then
  $
    frak("p")B = product (frak("p"),g_i(alpha))^(e_i)
  $

  is the factorisation of $frak("p")B$ into a product of distinct prime ideals. The residue field is
  $
    B/(frak("p"),g_i(alpha)) equiv (A/frak("p"))[x]/(overline(g)_i),
  $

  hence the residue class degree is $f_i=op("deg") g_i$.
]

#proof[
  Note that $f in A[x]$ since $alpha$ is integral over $A$, thus our assumption on $B$ gives the isomorphism
  $
    A[x]/(f) attach(arrow.r.long, t: equiv) A[alpha]=B, quad x arrow.r.long.bar alpha.
  $

  Tensoring with the field $k=A/frak("p")$ yields the isomorphism
  $
    k[x]/(overline(f)) attach(arrow.r.long, t: equiv) B/frak("p")B, quad x arrow.r.long.bar alpha.
  $

  Since $k[x]$ is a PID, the maximal ideals of $k[x]/(overline(f))$ are given by $(overline(g)_i), (1 <= i <= r)$, which correspond to the ideals $(g_i(alpha))+frak("p")B$ in $B/frak("p")B$, and these correspond to the ideals $frak("P")_i := (frak("p"),g_i(alpha))$ in $B$. Thus ${frak("P")_i }_(i=1)^r$ is the complete set of prime ideals containing $frak("p")B$, and hence is the complete set of prime divisors of $frak("p")$ by *Thm. 125*.\
  The decomposition $frak("p")B= product frak("P")_i^(r_i)$ means that $frak("p")B$ contains $product frak("P")_i^(r_i)$ but does not contain the product when any $r_i$ is replaced with a smaller value. Since $frak("p")B$ corresponds to $(overline(f))$ in $k[x]$ and that $f equiv product g_i^(e_i) (op("mod") frak("p"))$, we have $overline(f)= product overline(g)_i^(e_i)$, and thus $frak("p")B= product frak("P")_i^(e_i)$.\
  Now, observe the residue field
  $
    B/frak("P")_i equiv frac(B/frak("p")B, frak("P")_i/frak("p")B) equiv frac(B/frak("p")B, (g_i(alpha))+frak("p")B) equiv frac(k[x]/(overline(f)), (overline(g)_i)) = k[x]/(overline(g)_i).
  $

  Note that the leading coefficient of $f$ and thus $g_i$ is a unit, hence we have
  $
    f_i=[B/frak("p")_i:k]=[k[x]/(overline(g)_i):k]=op("deg") overline(g)_i=op("deg") g_i.
  $

]


#example(number: 165)[
  For a square-free integer $m eq.not 1$ factorise $p in bb("Z")$ in $bb("Q")[sqrt(m)]$. *Prop. 164* allows us to characterise the following three possibilities:
  - _(i)_ $(p)^e=frak("P")^2$: $(p)$ ramifies and $e=2, f=1, g=1$.
  - _(ii)_ $(p)^e=frak("P")$: $(p)$ stays prime and $e=1, f=2, g=1$.
  - _(iii)_ $(p)^e=frak("P")_1 frak("P")_2$: $(p)$ splits and $e=1, f=1, g=2$.

]
