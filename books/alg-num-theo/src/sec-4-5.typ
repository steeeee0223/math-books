#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Exercises

#exercise(number: "1", title: [Computing Expansions])[
  Compute the $5$-adic expansion of $frac(1, 3), frac(2, 3)$ and $-frac(2, 3)$.
]
#proof[

]


#exercise(number: "2", title: [Units in $bb("Z")_p$])[
  A $p$-adic integer $a := a_0+a_1 p+a_2 p^2+ dots.h.c$ is a unit in $bb("Z")_p$ iff $a_0 eq.not 0$.
]

#proof[
  "$arrow.l.double$"\ Suppose $a_0 eq.not 0$. First, we consider the sequence $(s_n)$, where $s_n= sum_(i=0)^(n-1)a_i p^i$, then $s_n in bb("Z") subset bb("Z")_p$, thus it suffices to show that $p divides.not s_n$. But $s_n=a_0+p dot b, (b in bb("Z"))$, we have $p|s_n arrow.l.r.double p|a_0 arrow.l.r.double a_0=0$. By assumption, $p divides.not s_n$, so $nu_p(x_n)=0$, whence $s_n in bb("Z")_p^times$ by *(249)*.\
  Now, the element $a in bb("Z")_p$ is given by the Cauchy sequence $(s_n)$. As each $s_n in bb("Z")_p^times$, we may consider the sequence $(s_n^(-1))$. Note that $s_n s_(n+1)(s_n^(-1)-s_(n+1)^(-1))=s_n s_(n+1)$ and that $s_n s_(n+1)$ is a unit, it follows that $s_n^(-1)-s_(n+1)^(-1) in (p^n)$ so that $(s_n^(-1))$ converges with respect to the $(p)$-adic topology. Moreover, we have $a^(-1) := op("lim")_n s_n^(-1) in bb("Z")_p$, i.e. $a$ is a unit in $bb("Z")_p$.\
  "$arrow.r.double$"\ Suppose $a$ is a unit in $bb("Z")_p$. We now think of as an inverse system by considering the Cauchy sequence $(s_n op("mod") p^n)$. Note that the multiplication of $bb("Z")_p$ is induced by the product ring $product_(n in bb("N")) bb("Z")/p^(n+1) bb("Z")$, thus $s_1=a_0 in bb("Z")/p bb("Z")$ must be a unit. As $bb("Z")/p bb("Z")$ is a field, we obtain the required result $a_0 eq.not 0$.
]


#exercise(number: "3", title: [$p$-Adic Integers & Formal Power Series])[
  There is a canonical ring isomorphism $bb("Z")_p equiv bb("Z") ⟦x⟧/(x-p)$.
]


#exercise(number: "4", title: [Solving Quadratic Equations in $bb("Z")_p$])[
  - _(a)_ The equation $x^2=2$ admits a solution in $bb("Z")_7$.
  - _(b)_ If $b in bb("Z")_2^times$ with $b equiv a^2 op("mod") (2) bb("Z")_2$, then $f=x^2-b$ has a root in $bb("Z")_2$.

]
