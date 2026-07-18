#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Finiteness

#definition(number: "54", title: [Finite Modules & Finite Type])[
  - It is common to call an $A$-module $M$ *finite* over $A$ if $M$ is a finitely generated $A$-module.
  - An $A$-algebra $B$ is of *finite type* over $A$ if $B$ is a finitely generated $A$-algebra.

  Now, we have the following:
  $
    ,bullet M text("finite over") A. ,, arrow.l.r.double.long phi:A^n arrow.r.twohead M text("$A$-linear").; , ,, arrow.l.r.double.long M={ sum a_i phi(e_i):a_i in A}=(phi(e_1), dots.h.c ,phi(e_n)).; ,bullet B text("finite type over") A. ,, arrow.l.r.double.long phi:A[x_1, dots.h.c ,x_n] arrow.r.twohead B text("$A$-algebra homomorphism").; , ,, arrow.l.r.double.long B={ sum a_alpha phi b^alpha:a_alpha in A}=A[b_1, dots.h.c ,b_n], (b_i := phi(e_i)).
  $

]


#remark(number: 55)[
  An $A$-algebra $B$ which is finite as an $A$-module is also of finite type, but the converse is false in general. It holds in special situations such as $A subset B$ is an integral ring extensions. (cf. *Rmk.* after *Def. 94*)
]


#definition(number: "56", title: [Noetherian Rings & Modules])[
  Let $M$ be an $A$-module. Then $M$ is called *Noetherian* if every $A$-submodule of $M$ is finitely generated. In particular, $A$ is called a *Noetherian ring* if it is Noetherian as an $A$-module over itself.
]


#theorem(number: "57", title: [Hilbert's Basissatz])[
  If $A$ is Noetherian, then so is $A[x]$. [AM, 7.5]
]


#proposition(number: 58)[
  - _(a)_ Submodules and quotient modules of Noetherian modules are Noetherian. [AM, 6.3]
  - _(b)_ Let $N subset M$ be $A$-modules, then $M$ is Noetherian $arrow.l.r.double.long$ $N$ and $M/N$ are Noetherian.
  - _(c)_ Let $M$ be an $A$-module, then T.F.A.E.:
    - _(i)_ $M$ is Noetherian.
    - _(ii)_ Every ascending chain of $A$-submodules $M_1 subset M_2 subset dots.h.c subset M_k subset dots.h.c$ becomes stationary.
    - _(iii)_ Every non-empty set of $A$-submodules of $M$ has a maximal element with respect to inclusion. [AM, 6.1]

  - _(d)_ Let $A$ be a Noetherian ring and $M$ be a finitely generated $A$-module, then $M$ is a Noetherian $A$-module. [AM, 6.5]

]
