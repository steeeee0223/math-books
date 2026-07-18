#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Exercises

#exercise(number: "6", title: [Integral Closure of Localisations])[
  Let $A subset B$ be a ring extension and $S$ be a multiplicative subset of $A$. Then $S^(-1) overline(A)$ is the integral closure of $S^(-1)A$ in $S^(-1)B$.
]

#proof[
  We claim that $overline(S^(-1)A)=S^(-1) overline(A)$. "$supset$"\ is clear by *96(b)* that $S^(-1) overline(A)$ is integral over $S^(-1)A$.\
  "$subset$"\ Suppose $frac(b, s) in S^(-1)B, (b in B, s in S)$ is integral over $S^(-1)A$, then $frac(b, s)$ satisfies
  $
    (frac(b, s))^n+(frac(a_1, s_1))(frac(b, s))^(n-1)+ dots.h.c +frac(a_n, s_n)=0 text("in") S^(-1)B, quad (a_i in A, s_i in S).
  $

  Take $t := s_1 dots.h.c s_n$ and multiply the above equation by $(s t)^n$, then
  $
    (b t)^n+c_1(b t)^(n-1)+ dots.h.c +c_n=0 text("in") B, quad (c_i := frac(a_i, s_i)(s t)^i in A).
  $

  Thus, $b t in B$ is integral over $A$, i.e. $b t in overline(A)$. It follows that $frac(b, s)=frac(b t, s t) in S^(-1) overline(A)$.
]


#exercise(number: "7", title: [Characterisation of Integral Elements inside Fields])[
  Let $A subset K$ be a ring extension with $K$ a field. Then $alpha in K$ is integral over $A$ iff there exists a finitely generated $A$-module $M eq.not 0$ inside $K$ with $alpha M subset M$.
]


#exercise(number: "8", title: [Normality is a Local Property])[
  T.F.A.E. for an integral domain $A$:
  - _(i)_ $A$ is normal.
  - _(ii)_ $A_frak("p")$ is normal for each prime ideal $frak("p") lt.closed A$.
  - _(iii)_ $A_frak("m")$ is normal for each maximal ideal $frak("m") lt.closed A$.

]

#proof[
  We use the fact in [AM, 3.9] that an injective (so is a surjective) $A$-linear map is a local property. Let $K=op("Quot")A$ and $f:A arrow.r.hook overline(A)$ be the identity map. Then, by *Ex. 6*, we have
  $
    A text("is normal") , arrow.l.r.double f text("is surjective") arrow.l.r.double f_frak("p") text("(resp. $f_ frak(\"m\")$) is surjective"); , arrow.l.r.double A_frak("p") text("(resp. $A_ frak(\"m\")$) is normal"),
  $

  for each prime ideal $frak("p")$ (resp. maximal ideal $frak("m")$) of $A$.
]


#exercise(number: "9", title: [Normal Rings in Number Theory])[
  Let $d eq.not 0,1$ be a square-free integer, (i.e. no square divides $d$ in $bb("Z")$). Then the integral closure of $bb("Z")$ in $bb("Q")(sqrt(d))={a+b sqrt(d):a,b in bb("Q")} subset bb("C")$ is given by
  $
    overline(bb("Z"))=cal("O")_(bb("Q")(sqrt(d)))= {a+b sqrt(d):a,b in bb("Q"), -2a in bb("Z"), a^2-d b^2 in bb("Z")}.
  $

]
