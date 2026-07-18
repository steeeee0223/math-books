#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Exercises

#exercise(number: "1", title: [Prime ideals avoiding multiplicative subsets])[
  Let $S$ be a multiplicative subset of an integral domain $A$ and $frak("a") lt.closed A$ an ideal with $frak("a") inter S= nothing$. Then $frak("a")$ is contained in a prime ideal $frak("p") lt.closed A$ with $frak("p") inter A= nothing$.
]

#proof[
  We consider the set
  $
    Sigma := {frak("q") lt.closed A:frak("q") supset frak("a") text("and") frak("q") inter S= nothing }
  $

  partially ordered by set inclusion. Then $Sigma$ is nonempty since it contains $frak("a")$, and it is bounded above by $A$. Thus the *Zorn's Lemma* (cf. [G,2.16-17]) gives the existence of such an ideal $frak("p") in Sigma$ which is maximal.
  *Claim.* $frak("p") lt.closed A$ is prime. If not, then there exist $a,b in.not frak("p")$ with $a b in frak("p")$. By maximality of $frak("p")$, the ideals $frak("p")+(a)$ and $frak("p")+(b)$ must intersect $S$. We let $p+r a$ and $q+s b$ be the elements in the intersections, respectively, where $p,q in frak("p"), r,s in A$. Since $S$ is multiplicative, we have
  $
    p'+(r s) a b := (p q+p dot s b+q dot r a)+(r s) a b=(p+r a)(q+s b) in S.
  $

  Now that $p'=p q+(s b)p+(r a)q in frak("p")$ and $(r s)a b in frak("p")$ by assumption, we have $p'+(r s) a b in frak("p")$, i.e. $frak("p") inter S eq.not nothing . ( -> arrow.l )$. Hence $frak("p") lt.closed A$ must be prime.
]


#exercise(number: "2", title: [The Zariski Topology])[
  Let $A$ be a general ring. Then
  - _(a)_ $cal("V")((0))=op("Spec")A$ and $cal("V")(A)= nothing$.
  - _(a\*)_ If the ideals $frak("a") subset frak("b")$, then $cal("V")(frak("a")) supset cal("V")(frak("b"))$.
  - _(b)_ If ${frak("a")_i }_(i in I)$ is any family of ideals of $A$, then $cal("V")( sum_(i in I) frak("a")_i)= inter.big_(i in I) cal("V")(frak("a")_i)$.
  - _(c)_ $cal("V")(frak("a") inter frak("b"))=cal("V")(frak("a") dot frak("b"))=cal("V")(frak("a")) union cal("V")(frak("b"))$ for any two ideals $frak("a"),frak("b") lt.closed A$.
  - _(d)_ $op("Spec")(A/frak("a")) equiv cal("V")(frak("a"))$ and $op("Spec")(S^(-1)A)={frak("p") in op("Spec")A:frak("p") inter S= nothing }$. (For the last assertion assume that $A$ is an integral domain).

]

#proof[
  (a) $cal("V")((0))={frak("p") in op("Spec")A:frak("p") supset (0)}=op("Spec")A$ and $cal("V")(A)={frak("p") in op("Spec")A:frak("p") supset A}= nothing$.\
  (a\*) Clearly, if $q in cal("V")(frak("b"))$, then $frak("q") supset frak("b") supset frak("a")$, whence $frak("q") in cal("V")(frak("a"))$.\
  (b) We have
  $
    frak("p") in cal("V")( sum_(i in I) frak("a")_i) arrow.l.r.double.long frak("p") supset frak("a")_i, forall i in I arrow.l.r.double.long frak("p") in inter.big_(i in I) cal("V")(frak("a")_i).
  $

  (c) First, we note that $frak("a") dot frak("b") subset frak("a") inter frak("b")$, by (a\*), we have $cal("V")(frak("a")) union cal("V")(frak("b")) subset cal("V")(frak("a") dot frak("b")) subset cal("V")(frak("a") inter frak("b"))$. Moreover, since $frak("p") lt.closed A$ is a prime, $frak("p") supset frak("a") inter frak("b")$ implies either $frak("p") supset frak("a")$ or $frak("p") supset frak("b")$ by *Lemma 22*. Hence, we have
  $
    cal("V")(frak("a")) union cal("V")(frak("b")) subset cal("V")(frak("a") dot frak("b")) subset cal("V")(frak("a") inter frak("b")) subset cal("V")(frak("a")) union cal("V")(frak("b")).
  $

  (d) The first part $op("Spec")(A/frak("a")) equiv {frak("p") in op("Spec")A:frak("p") supset frak("a")}=cal("V")(frak("a"))$ follows from the *Comparison Lemma 16*. The second part follows from *Prop. 27* under the natural map $op("Spec")(S^(-1)A) -> op("Spec")A, frak("q") mapsto frak("q")^c$ induced by the inclusion $A arrow.r.hook S^(-1)A$.
]


#exercise(number: "3", title: [Closed Points])[
  Let $X subset op("Spec")A$. Show that $cal("V")(cal("I")(X))=overline(X)$ and conclude that $overline({frak("p")})=cal("V")(frak("p"))$ for any $frak("p") in op("Spec")A$. In particular, $frak("p")$ is a closed point iff $frak("p")$ is maximal.
]

#proof[
  (i)"$supset$"\ If $frak("p") in X$, then $frak("p") supset inter.big_(frak("q") in X) frak("q")=cal("I")(X)$, whence $frak("p") in cal("V")(cal("I")(X))$. Hence $X subset cal("V")(cal("I")(X))$. Moreover, since $cal("V")(cal("I")(X))$ is closed, we have $overline(X) subset cal("V")(cal("I")(X))$.\
  "$subset$"\ Let $Y subset op("Spec")A$ be any closed set containing $X$, then $Y=cal("V")(frak("a")) supset X$ for some $frak("a") lt.closed A$. If $frak("p") in X subset Y$, then $cal("I")(X)= inter.big_(frak("q") in X) frak("q") supset inter.big_(frak("q") in Y) frak("q")=cal("I")(Y) supset frak("a")$. By *Ex. 2(a\*)*, we have $cal("V")(cal("I")(X)) subset cal("V")(frak("a"))=Y$. Thus, by definition of "closure", $Y=overline(X)$.\
  (ii) Since $cal("I")({frak("p")})=frak("p")$, from the previous part, we have $cal("V")(frak("p"))=cal("V(I")({frak("p")})=overline({frak("p")})$.
]


#exercise(number: "4", title: [Basic Open Sets for the Zariski Topology])[
  For each $a in A$, let $X_a$ denote the complement of $cal("V")(a) := cal("V")((a))$ in $X=op("Spec")A$. In particular, $X_a$ is open and defines the so-called *basic open set*. Show that
  - _(a)_ ${X_a }_(a in A)$ forms a basis of open sets for the Zariski topology, i.e. any open set is a union of open sets of the form $X_a$.
  - _(b)_ $X_a inter X_b=X_(a b)$.
  - _(c)_ $X_a= nothing . arrow.l.r.double.long a$ is nilpotent.
  - _(d)_ $X_a=op("Spec")A. arrow.l.r.double.long a$ is a unit.
  - _(e)_ $X_a=X_b. arrow.l.r.double.long sqrt((a))=sqrt((b))$.
  - _(f)_ $X$ is quasi-compact, i.e. every open covering of $X$ has a finite subcovering.

  *Remark.* In addition to "quasi-compact", "compact" spaces are usually required to be Hausdorff.
]

#proof[
  note. By definition, $X_a=X without cal("V")(a)={frak("p") in op("Spec")A:f in.not frak("p")}$.\ (a) It follows from $cal("V")(frak("a"))= inter.big_(a in frak("a")) cal("V")(a)$ by taking complements.\ (b) $because cal("V")(a) union cal("V")(b)attach(=, t: text(\"text("E x.2(c)")\")) cal("V")(a b). therefore X_a inter X_b=X without [cal("V")(a) union cal("V")(b)]=X without cal("V")(a b)=X_(a b)$.\
  (c) recall. $frak("N") :=$ set of all nilpotents of $A$, is an ideal called the *nilradical* of $A$. Then,
  $
    X_a= nothing arrow.l.r.double cal("V")(f)=X arrow.l.r.double f in frak("p"), forall frak("p") in X arrow.l.r.double f in inter.big_(frak("p") in X) frak("p")attach(=, t: text(\"text("[A M, 1.8]")\")) frak("N").
  $

  (d) We have
  $
    X_f=X arrow.l.r.double cal("V")(f)= nothing arrow.l.r.double f in.not frak("p"), forall frak("p") in X. attach(arrow.l.r.double.long, t: ast) f in A^times .
  $

  proof of $ast$. "$arrow.r.double$"\ Assume $f in.not A^times$. By [AM, 1.5], $exists frak("m") lt.closed A$ maximal with $f in frak("m"). ( -> arrow.l )$. \ "$arrow.l.double$"\ Assume $exists frak("p") in X$ with $f in frak("p"). because f in A^times . therefore frak("p")=A. ( -> arrow.l )$.\
  (e) We have
  $
    X_a=X_b arrow.l.r.double cal("V")(a)=cal("V")(b) attach(arrow.l.r.double.long, t: ast) sqrt((a))=sqrt((b)).
  $

  proof of $ast$. "$arrow.r.double$"\ Clearly, by *Prop. 170*, $sqrt((a))=cal("I")(cal("V")(a)))=cal("I")(cal("V")(b)))=sqrt((b))$.\ "$arrow.l.double$"\ Assume that there is a prime $frak("p") lt.closed A$ with $(a) subset frak("p") subset sqrt((a))$. If $x in sqrt((a))$, then $x^n in (a) supset frak("p")$ for some $n in bb("N")_( >= 1)$, whence $x in frak("p")$. It follows that $frak("p")=sqrt((a))$. By [AM, Ex.1.15i], we have $cal("V")(a)=cal("V")(sqrt((a)))=cal("V")(sqrt((b)))=cal("V")(b)$.\
  (f) claim. $X_a$ is quasi-compact, for any $a in A$. Given an open cover ${X_(a_i)}_(i in I)$ of $X_a$. For each $i, frak("a")_i := (a_i)$, then
  $
    X_a subset union.big_i X_(a_i) , arrow.l.r.double cal("V")( sum_i frak("a")_i)= inter.big_i cal("V")(frak("a")_i) subset cal("V")(f) attach(arrow.l.r.double.long, t: text("(e)")) sqrt((a)) subset sqrt(sum_i frak("a")_i); , attach(arrow.l.r.double.long, t: text("Def.")) exists m >= 1: a^m in sum_i frak("a")_i attach(arrow.l.r.double.long, t: text("finite sum")) exists m >= 1: a^m := sum_(j in J)r_j a_j, |J|< oo .
  $

  If there is a prime $frak("p") in op("Spec")A$ with $a_j in frak("p"), forall j in J$, then $a^m in frak("p"). because frak("p") lt.closed A$ is prime. $therefore a in frak("p")$. Equivalently, if $a in.not frak("p")$, then $a_j in.not frak("p")$ for some $j in J$, whence $X_f subset union.big_(j in J)X_(a_i)$. Hence $X_a$ is quasi-compact. We take $a=1$, then $X=X_1$ is quasi-compact.
]


#exercise(number: "5", title: [The Spectrum of $A_f$])[
  Let $f in A$ and $S_f := {f^n }_(n >= 0)$ the multiplicative system. We denote $A_f := S_f^(-1)A$ and $X=op("Spec")A$. Show that
  - _(a)_ $X_f$ is homeomorphic to $op("Spec")A_f$, that is, the basic open sets have the same topology as affine schemes.
  - _(b)_ $cal("O")_X(X_f)=A_f$. Conclude that $cal("O")_X(X)=A$.

  *Remark.* In fact, $X_f$ is a basic example of a scheme for which one can show that it is not only homeomorphic, but isomorphic as a scheme to $op("Spec")A_f$.
]

#proof[
  (a) Consider the natural map $phi:A -> A_f, a mapsto frac(a, 1)$. Then the associated map
  $
    phi^ast :op("Spec")A_f arrow.r.long op("Spec")A, frak("q") arrow.r.long.bar frak("q")^c
  $

  is injective and has image $X_f={frak("p") in op("Spec")A:f in.not frak("p")}$. Now, the map
  $
    psi:X_f arrow.r.long op("Spec")A_f, frak("p") arrow.r.long.bar frak("p")^e=frak("p")A_f
  $

  is the inverse to $phi^ast$. It remains to show that $psi$ is continuous. Let $cal("V")(frak("a")) subset op("Spec")A_f$ be a closed set, then
  $
    psi^(-1)(cal("V")(frak("a")))={frak("p") in X_f:frak("p") supset frak("a")^c }=X_f inter cal("V")(frak("a")^c),
  $

  i.e. $psi^(-1)(cal("V")(frak("a")))$ is closed in $X_f$, whence $psi$ is continuous.\ Indeed, if $phi(frak("p")) in cal("V")(frak("a"))$ for some $f in.not frak("p")$, then $frak("a") subset frak("p")^e$, whence $frak("a")^c subset frak("p")^(e c)=frak("p")$. Conversely, if $frak("a")^c subset frak("p")$ for some $f in.not frak("p")$, then $psi(frak("p"))=frak("p")^e supset frak("a")^(c e)=frak("a")$.\
  (b) "$supset$"\ Note that for any $frak("p") in X_f$, we have $frac(a, f^n) in A_frak("p")$, whence $frac(a, f^n) in inter.big_(frak("p") in X_f)A_frak("p")=cal("O")_X(X_f)$.\ "$subset$"\ Suppose that $F in cal("O")_X(X_f)= inter.big_(f in.not frak("p"))A_frak("p")$, and consider the ideal $frak("a") := {a in A:a F in A}$. Let $frak("p") in X_f$, then $F := frac(a, s) in A_frak("p"), (a in A, s in.not frak("p"))$, whence $b F=a$, i.e. $b in frak("a")$. It follows that if $f in.not frak("p")$, then $frak("p") supset.not frak("a")$, which means $cal("V")(frak("a")) subset cal("V")(f)$. By *Ex. 2(e)*, we have $sqrt((f)) subset sqrt(frak("a")). arrow.r.double f^n in frak("a")$ for some $n$, hence $F in A_f$. By taking $f=1$, we obtain $X=X_1$ and $A=A_1$, thus the result follows.
]


#exercise(number: "6", title: [The Spectrum of $bb("Z")[i]$])[
  Compute explicitly the continuous map $f:op("Spec") bb("Z")[i] -> op("Spec") bb("Z")$ from the scheme morphism $F=(f,f^ast )$ induced by the inclusion $bb("Z") arrow.r.hook bb("Z")[i]$.
]


#exercise(number: "7", title: [The Associated Map with an Integral Extension])[
  Let $iota:A arrow.r.hook B$ be an integral ring extension (considering $iota$ as an inclusion). Then the associated map
  $
    iota^ast :op("Spec")B arrow.r.long op("Spec")A, frak("p") arrow.r.long.bar frak("p") inter A
  $

  is a closed map, i.e. it maps closed sets to closed sets.
]


#exercise(number: "8", title: [Scheme Morphisms])[
  Let $B$ be a $k$-algebra of finite type with $n=op("dim") B$. Then there exists a scheme morphism $F=(f,f^ast )$ such that $f$ is a closed surjective map.
]


#exercise(number: "9", title: [Inserting Prime Ideals into Chains])[
  Let $A subset B$ be an integral extension where $A$ is a finitely generated $k$-algebra. Assume there are given prime ideals $frak("q")_0$ and $frak("q")_2$ of $B$ and let $frak("p")_0 := frak("q")_0 inter A$ and $frak("p")_2 := frak("q")_2 inter A$. If $frak("p")_1$ is a prime ideal of $A$ with $frak("p")_0 subset.not.eq frak("p")_1 subset.not.eq frak("p")_2$, then there exists a prime ideal $frak("q")_1$ in $B$ with $frak("q")_0 subset.not.eq frak("q")_1 subset.not.eq frak("q")_2$.
]


#exercise(number: "10", title: [Modifying Chains of Prime Ideals])[
  Let $n >= 1$ and $frak("p")_0 subset.not.eq frak("p")_1 subset.not.eq dots.h.c subset.not.eq frak("p")_n$ be a chain of prime ideals in a Noetherian ring $A$. If $a in frak("p")_n$, then there exists a chain of prime ideals $frak("p")'_0 subset.not.eq frak("p")'_1 subset.not.eq dots.h.c subset.not.eq frak("p")'_(n-1) subset.not.eq frak("p")_n$ with $a in frak("p")'_1$.
]


#exercise(number: "11", title: [Codimension & Generators])[
  Let $A$ be Noetherian and $a_1, dots.h.c ,a_n in A$. Then every minimal prime ideal $frak("p")$ over $(a_1, dots.h.c ,a_n)$ satisfies $op("height") frak("p") <= n$.
]
