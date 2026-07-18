#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge

== Dimension

As Figure suggests we should think of the spectrum of a Dedekind ring as a smooth, $1$-dimensional object. We set out to make these notions rigourous.
#definition(number: "182", title: [Height & Dimension])[
  Let $frak("p") in op("Spec")A$. \ Its *height* (or *codimension*) is defined by
  $
    op("height") frak("p") := op("sup")_(r >= 0) {frak("p")_0 subset.not.eq frak("p")_1 subset.not.eq dots.h.c subset.not.eq frak("p")_r=frak("p"):frak("p")_i in op("Spec")A}.
  $

  The *(Krull) dimension* $op("dim")A$ of $A$ is
  $
    op("dim") A := op("sup")_(frak("p") in op("Spec")A) op("height") frak("p").
  $

]


#remark(number: 183)[
  Since a maximal chain necessarily ends with a maximal ideal, it sufices to take the supremum over heights of maximal ideals:
  $
    op("dim") A=op("sup")_(frak("m") subset A text("maximal")) op("height") frak("m").
  $

]


#example(number: 184)[
  - *Fields.* If $k$ is a field, then $op("dim") k=0$.
  - *PIDs.* If $A$ is a PID, then $op("dim") A=1$.
  - *Dedekind Rings.* Since any prime is maximal in a Dedekind ring, we have $op("dim") A=1$.
  - *Local Rings.* By *Rmk. 183*, we have
  $
    op("dim") A_frak("p")=op("height") frak("p")A_frak("p")=op("height") frak("p").
  $

  - *Noetherian Rings.* Finite dimension is not related to the Noetherian property. In [R, §9.4(3)] an example of a Noetherian ring with $op("dim") A= oo$ is discussed. Conversely, the ring $A := k[x_1,x_2, dots.h.c ]/lr(chevron.l x_i x_j:1 <= i <= j< oo chevron.r)$ is not a Noetherian, but $(overline(x_1), dots.h.c ,overline(x_n))$ is the only prime ideal, whence $op("dim") A=0$.

]


#remark(number: 185)[
  Since $op("dim") bb("Z")=1$ but $op("dim") bb("Q")=0$, we cannot conclude that $op("dim") A <= op("dim") B$ if $A subset B$. For rings the notion of dimension can thus be quite pathological.
]


#proposition(number: 186)[
  The dimension is local in the sense that
  $
    op("dim") A=op("sup")_(frak("p") in op("Spec")A) op("dim") A_frak("p")=op("sup")_(frak("m") subset A text("max.")) op("dim") A_frak("m").
  $

]

#proof[
  For any prime ideal $frak("p") lt.closed A, A_frak("p")$ is local with maximal ideal $frak("p")A_frak("p")$, and from *Ex. 4(d)* we have
  $
    op("Spec")A_frak("p")={frak("q") in op("Spec")A:frak("q") inter (A without frak("p"))= nothing }={frak("q") in op("Spec")A:frak("q") subset frak("p")}.
  $

  Hence, it follows that
  $
    op("dim") A & attach(=, t: text("Def.")) op("sup")_(frak("p") in op("Spec")A) op("height") frak("p") \
                & attach(=, t: text("(184)")) op("sup")_(frak("p") in op("Spec")A) op("dim") A_frak("p") \
                & attach(=, t: text("(183)")) op("sup")_(frak("m") subset A text("maximal")) op("dim") A_frak("m").
  $

]


#proposition(number: 187)[
  Let $A$ be a ring of finite dimension in which all maximal chains of prime ideals have the same length, and let $frak("p") in op("Spec")A$. Then $A/frak("p")$ is also a ring of finite dimension whose maximal chains of prime ideal have the same length, and
  $
    op("dim") A=op("height") frak("p")+op("dim") A/frak("p")=op("dim") A_frak("p")+op("dim") A/frak("p").
  $

  In particular, $op("dim") A=op("dim") A_frak("p")$ if $frak("p")$ is maximal.
]

#proof[
  From *Ex. 2(d)* we have $op("Spec")(A/frak("p")) equiv cal("V")(frak("p"))$. In particular, any increasing chain $overline(0)=overline(frak("p")_0) subset.not.eq overline(frak("p")_1) subset.not.eq dots.h.c subset.not.eq overline(frak("p")_r)=overline(frak("q"))$ of prime ideals in $A/frak("p")$ corresponds to the chain $frak("p")=frak("p")_0 subset.not.eq frak("p")_1 subset.not.eq dots.h.c subset.not.eq frak("p")_r=frak("q")$ of prime ideals in $A$. Completing $frak("q")$ into a maximal chain
  $
    0=frak("r")_0 subset.not.eq frak("r")_1 subset.not.eq dots.h.c subset.not.eq frak("r")_s=frak("p")=frak("p")_0 subset.not.eq frak("p")_1 subset.not.eq dots.h.c subset.not.eq frak("p")_r=frak("q")
  $

  shows that $op("dim") A=s+r$ (since all maximal chains have equal length), where $op("height") frak("p")=s$ (otherwise we can still insert some $frak("r")_j$) and $op("dim") A/frak("p")=r$ (otherwise we can still insert some $frak("q")_i$; in particular, all maximal chains have same length in $a/frak("p")$). Finally, if $frak("p")$ is maximal, then $A/frak("p")$ is a field, whence $op("dim") A/frak("p")=0$ by *Example 184*.
]


#example(number: 188)[
  The assumptions hold for instance for Dedekind rings or polynomial rings over a field, see *Prop. 197*.
]


We wish to show that for a field $k, op("dim") k[x_1, dots.h.c ,x_n]=n$. For this we need the following going-up and -down theorems which generalise the corresponding statements for Dedekind respectively $1$-dimensional ring extensions to higher dimensional ring extensions.

#proposition(number: "189", title: [Lying-Over])[
  Let $A subset B$ be an integral ring extension.
  - _(a)_ Let $frak("q") in op("Spec")B$, then $frak("p") := frak("q") inter A$ is maximal iff $frak("q")$ is maximal. [AM, 5.8]
  - _(b)_ Let $frak("q") subset frak("q")'$ in $op("Spec")B$ such that $frak("q") inter A=frak("q")' inter A := frak("p")$, then $frak("q")=frak("q")'$. [AM, 5.9]
  - _(c)_ Let $frak("p") in op("Spec")A$, then there exists $frak("q") in op("Spec")B$ such that $frak("p")=frak("q") inter A$. [AM, 5.10]

]

#proof[
  (a) Note that from *Lemma 96(a)* $B/frak("q")$ is integral over $A/frak("p"). because frak("p")$ and $frak("q")$ are both prime ideal of $A$ and $B$, respectively. $therefore$ Both $A/frak("p")$ and $B/frak("q")$ are integral domains. Thus
  $
    frak("p") text("is maximal"). arrow.l.r.double.long A/frak("p") text("is a field"). attach(arrow.l.r.double.long, t: text("(133)")) B/frak("q") text("is a field"). arrow.l.r.double.long frak("q") text("is maximal").
  $

  (b) By *Lemma 96(b)*, $B_frak("p")$ is integral over $A_frak("p")$. Let $frak("m")$ be the extension of $frak("p")$ in $A_frak("p")$ and $frak("n"), frak("n")'$ be the extension of $frak("q")$ of $frak("q"), frak("q")'$ in $B_frak("p")$, respectively. Then $frak("m")$ is the maximal ideal of $A_frak("p")$; $frak("n") subset frak("n")'$; and $frak("n")^c=frak("n")'^c=frak("m")$. It follows from (a) that both $frak("n"), frak("n")'$ are maximal, hence $frak("n")=frak("n")'$, hence $frak("q")=frak("q")'$ by [AM, 3.11iv].\
  (c) Note that $B_frak("p")$ is integral over $A_frak("p")$, thus the diagram
  #align(center)[#diagram(
    cell-size: 18mm,
    $
      A edge("r", text("integral"), arrow.r.hook) edge("d", alpha, ->) & B edge("d", beta, ->) \
                 A_frak("p") edge("r", text("integral"), arrow.r.hook) & B_frak("p")
    $,
  )]
  is commutative. Let $frak("n") lt.closed B_frak("p")$ be a maximal ideal, then $frak("m") := frak("n") inter A_frak("p") lt.closed A_frak("p")$ is maximal by (a). Note: $A_frak("p")$ is local, hence $frak("m")$ is the unique maximal ideal. Now, take $frak("q") := beta^(-1)(frak("n"))$, then $frak("q") lt.closed B$ is prime and $frak("q") inter A=alpha^(-1)(frak("m"))=frak("p")$.
  #align(center)[#diagram(
    cell-size: 16mm,
    $
      A edge("r", arrow.r.hook) edge("d", alpha, ->) & B edge("d", beta, ->)
      & frak("p")=alpha^(-1)(frak("m")) edge("r", mapsto) & frak("q")=beta^(-1)(frak("n")) \
      A_frak("p") edge("r", arrow.r.hook) & B_frak("p")
      & exists frak("m") edge("r", text("(a)"), mapsto) & frak("n")
    $,
  )]
]


#proposition(number: "190", title: [Incompatibility])[
  Let $A subset B$ be an integral ring extension. Suppose $frak("q"),frak("q")' in op("Spec")B$ satisfy $frak("q") inter A=frak("q")' inter A$ but $frak("q") eq.not frak("q")'$. Then $frak("q") subset.not frak("q")'$ and $frak("q")' subset.not frak("q")$. [AM, 5.9]
]


#proposition(number: "191", title: [Going-Up])[
  Let $A subset B$ be an integral ring extension. Suppose that  $frak("p")_1,frak("p")_2 in op("Spec")A$ and $frak("q")_1 in op("Spec")B$ such that $frak("q")_1 inter A=frak("p")_1$. Then there exists $frak("q")_2 in op("Spec")B$ with $frak("q")_1 subset frak("q")_2$ such that $frak("q")_2 inter A=frak("p")_2$. [AM, 5.11]
  #align(center)[#diagram(
    cell-size: 17mm,
    $
      frak("q")_1 edge("r", subset, arrow.r.hook) edge("d", ->)
      & frak("q")_2 edge("r", lt.closed, arrow.r.hook) edge("d", ->) & B edge("d", text("integral"), arrow.l.hook) \
      frak("p")_1 edge("r", subset, arrow.r.hook) & frak("p")_2 edge("r", lt.closed, arrow.r.hook) & A
    $,
  )]
]

#proof[
  Consider the map $phi:A arrow.r.hook B arrow.r.twohead B/frak("q")_1$ with its kernel $op("ker")phi=frak("q")_1 inter A=frak("p")_1$, then we have the inclusion $A/frak("p")_1 arrow.r.hook B/frak("q")_1$. Note that by *Example 96(a)*, $A/frak("p")_1 subset B/frak("q")_1$ is integral. From *Prop. 190*, we may assume that $frak("p")_1 subset.not.eq frak("p")_2$ and we consider
  #align(center)[#diagram(
    cell-size: 15mm,
    $
      frak("q")_1 edge("r", subset.not.eq, arrow.r.hook) edge("d", mapsto)
      & pi^(-1)(frak("P")) edge("r", lt.closed, arrow.r.hook) edge("d", mapsto) & B edge("ddd", pi, arrow.r.twohead) \
      frak("p")_1 edge("r", subset.not.eq, arrow.r.hook) edge("d", mapsto)
      & frak("p")_2 edge("r", lt.closed, arrow.r.hook) edge("d", mapsto) & A edge("u", text("integral"), arrow.r.hook) edge("d", arrow.r.twohead) \
      overline(0) edge("r", subset.not.eq, arrow.r.hook) & overline(frak("p")_2) edge("r", lt.closed, arrow.r.hook) & A/frak("p")_1 \
      & frak("P") edge("r", lt.closed, arrow.r.hook) edge("u", mapsto) & B/frak("q")_1 edge("u", text("integral"), arrow.l.hook)
    $,
  )]
  where the existence of $frak("P") in op("Spec")(B/frak("q")_1)$ satisfying $frak("P") inter (A/frak("p")_1)=overline(frak("p")_2)$ follows from *Lying-Over Thm*. We take $frak("q")_2 := pi^(-1)(frak("P")) in op("Spec")B$, then clearly, $frak("q")_2 supset.not.eq frak("q")_1$. Moreover, one can show that $frak("P")=overline(frak("q")_2)={y+frak("q")_1:y in frak("q")_2 }$, and hence $frak("q")_2 inter A=frak("p")_2$.
]


#proposition(number: "192", title: [Going-Down])[
  Let $A subset B$ be an integral ring extension with $A$ integrally closed and $B$ an integral domain. Suppose that  $frak("p")_1,frak("p")_2 in op("Spec")A$ and $frak("q")_2 in op("Spec")B$ such that $frak("q")_2 inter A=frak("p")_2$. Then there exists $frak("q")_1 in op("Spec")B$ with $frak("q")_1 subset frak("q")_2$ such that $frak("q")_1 inter A=frak("p")_1$. [AM, 5.16]
  #align(center)[#diagram(
    cell-size: 17mm,
    $
      frak("q")_1 edge("r", subset, arrow.r.hook) edge("d", ->)
      & frak("q")_2 edge("r", lt.closed, arrow.r.hook) edge("d", ->) & B edge("d", text("integral"), arrow.l.hook) \
      frak("p")_1 edge("r", subset, arrow.r.hook) & frak("p")_2 edge("r", lt.closed, arrow.r.hook) & A
    $,
  )]
]

#proof[
  *(Sketch of Proof)*.
  Consider the local ring $(B_(frak("q")_2), frak("q")_2 B_(frak("q")_2))$. The idea is to find $frak("P") in op("Spec")B_(frak("q")_2)$ such that
  $
    frak("P") subset frak("q")_2 B_(frak("q")_2) quad text("and") quad frak("P") inter A=frak("p")_1.
  $

  We may choose $frak("P") := frak("p")_1 B_(frak("q")_2) subset frak("p_2")B_(frak("q")_2)$. Then we pick $frak("q")_1 := frak("P") inter B$.
  #align(center)[#diagram(
    cell-size: 15mm,
    $
      & frak("P") edge("r", subset, arrow.r.hook) edge("dd", ->) & frak("q")_2 B_(frak("q")_2) edge("r", lt.closed, arrow.r.hook) edge("d", ->) & B_(frak("q")_2) edge("d", arrow.l.hook) \
      frak("P") inter A edge("rr", subset, arrow.r.hook) & & frak("q")_2 edge("r", lt.closed, arrow.r.hook) edge("d", ->) & B edge("d", arrow.l.hook) \
      & frak("p")_1 edge("r", subset, arrow.r.hook) & frak("p")_2 edge("r", lt.closed, arrow.r.hook) & A
    $,
  )]
  Now, we obtain
  $
    frak("q")_1 inter A attach(=, t: text("Def.")) (frak("P") inter B) inter A =frak("P") inter A=frak("p")_1
  $

  Thus, it remains to show: $frak("p")_1$ is a contracted prime ideal of the prime ideal $frak("P") lt.closed B_(frak("q")_2)$. By [AM, 3.16], it is equivalent to show that $frak("p")_2^(e c)=frak("p")_2$.
]


#corollary(number: 193)[
  For any integral ring extension $A subset B$ we have $op("dim") A=op("dim") B$.
]

#proof[
  "$<=$"\ Let $frak("p")_0 subset.not.eq frak("p")_1 subset.not.eq dots.h.c subset.not.eq frak("p")_n$ be a strict chain of prime ideals in $A$. Apply *Lying-Over* to $frak("p")_0$, there is a prime ideal $frak("q")_0 lt.closed B$ with $frak("q")_0 inter A=frak("p")_0$. Now, by applying *Going-Up* we obtain a strict chain of prime ideals in $B$.
  #align(center)[#diagram(
    cell-size: 15mm,
    $
      frak("q")_0 edge("r", subset, arrow.r.hook) & frak("q")_1 edge("rrr", lt.closed, arrow.r.hook) edge("d", text("Going-Up"), ->) & & & B edge("d", text("integral"), arrow.l.hook) \
      frak("p")_0 edge("r", subset, arrow.r.hook) edge("u", text("Lying-Over"), arrow.l)
      & frak("p")_1 edge("r", subset, arrow.r.hook) & dots.h.c edge("r", subset, arrow.r.hook) & frak("p")_n edge("r", lt.closed, arrow.r.hook) & A
    $,
  )]
  "$>=$"\ Let $frak("q")_0 subset.not.eq frak("q")_1 subset.not.eq dots.h.c subset.not.eq frak("q")_n$ be a strict chain of prime ideals in $B$. Taking "contraction" under $A$ yields a chain of prime ideals in $A$ which is strict by "incompatibility".
]
