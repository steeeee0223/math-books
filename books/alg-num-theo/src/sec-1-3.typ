#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Ring of Integers


Now we generalise the ring extension $bb("Z")[i] subset bb("Q")(i)$ as follows:

#definition(number: "99", title: [Ring of Integers])[
  An *algebraic number field* $L$ is a finite extension field of $bb("Q")$, i.e. $[L:bb("Q")]< oo$. In particular, $op("char")L=0$ so that $bb("Z") subset L$. The integral closure of $bb("Z")$ in $L$ defines the *ring of integers* $cal("O")_L$.
]


#lemma(number: 100)[
  Let $K := op("Quot")(A)$ be the field of fractions of an integral domain $A$, and let $L/K$ be a field extension. If $x in L$ is algebraic over $K$, then there exists $d in A$ such that $d dot x$ is integral over $A$.
]

#proof[
  $because x in L$ is algebraic over $K. therefore x$ satisfies $x^n+ c_(n-1)x^(n-1)+ dots.h.c +c_1 x+c_0=0, (c_i in K)$. Let $d$ be the common denominator for the $c_i$'s so that $d dot c_i in A, forall i$. Now, multiply the equation by $d^n$, we have\  $d^n x^n+ c_(n-1)d^n x^(n-1)+ dots.h.c +c_1 d^n x+c_0 d^n=0$.\ Rewrite as \ $(d dot x)^n+(c_(n-1)d)(d dot x)^(n-1)+ dots.h.c +(c_1 d^(n-1))(d dot x)+c_0 d^n=0$. \ $because c_i dot d^(n-i) in A, forall i. therefore d dot x$ is integral over $A$.
]


#corollary(number: 101)[
  Let $A$ be an integral domain, $K := op("Quot")(A)$ and $L/K$ an algebraic field extension. If $overline(A)$ is the integral closure of $A$ in $L$, then $L=op("Quot")(overline(A))$. In particular, $L=op("Quot")(cal("O")_L)$ for any algebraic number field $L$.
]

#proof[
  If $x in L. because L/K$ is algebraic. $therefore$ By *Prop. 100*, $exists d in A$ such that $b := d dot x in A subset overline(A).\ arrow.r.double x=frac(b, d) in op("Quot")(overline(A))$.
]


#definition(number: "102", title: [Integrally Closed])[
  An integral domain $A$ is called *integrally closed* or *normal* if $A$ is integrally closed in its quotient field.
]


#example(number: 103)[
  - Every UFD is normal by *Example. 92*.
  - The ring of integers $cal("O")_K$ of an algebraic number field is integrally closed.\ (cf. *Prop. 95*).
  - $A := k[x,y]/(y^2-x^3)$ is an integral domain with $op("Quot")(A) equiv k(t)$. \
    Indeed, the map $k(t) -> op("Quot")(A), (frac(f, g))(t) mapsto (frac(f, g))(frac(overline(y), overline(x)))$ is an isomorphism. Since $k[t]$ is a UFD, it is integrally closed. However, $A$ is not. ($tau=frac(overline(y), overline(x)) in.not A$, but $tau^2-overline(x)=0$.)

]



#proposition(number: 104)[
  Let $A$ be an integral domain. Then T.F.A.E.:
  - _(a)_ $A$ is normal.
  - _(b)_ $A_frak("p")$ is normal for each prime ideal $frak("p") lt.closed A$.
  - _(c)_ $A_frak("m")$ is normal for each maximal ideal $frak("m") lt.closed A$.

  In view of the second item, we also say that normality is a *local property*. [Exercise][AM, 5.13]
]


#proposition(number: 105)[
  Let $A$ be integrally closed, $K := op("Quot")(A)$ and $L/K$ a finite field extension. Then an element of $L$ is integral over $A$ iff its minimum polynomial over $K$ has coefficients in $A$.
]

#proof[
  "$arrow.l.double$"\ Obvious. "$arrow.r.double$"\ Suppose $u in L$ is integral over $A$, then $u$ satisfies \  $u^n+a_(n-1)u^(n-1)+ dots.h.c +a_1 u+a_0=0, (a_i in A)$.\ Let $f$ be the minimum polynomial of $u$ over $K$. For any root $v$ of $f(x)=0$, the fields $K[u]$ and $K[v]$ are both stem fields for $f$, and so there exists a $K$-isomorphism $sigma:K[u] -> K[v], sigma u mapsto v$; On applying $sigma$ to the above equation, we obtain the equation \ $v^n+a_(n-1)v^(n-1)+ dots.h.c +a_1 v+a_0=0$, \ which shows that $v$ is integral over $A$. Hence all the roots of $f$ are integral over $A$, and it follows that the coefficients of $f$ are all integral over $A$. Thus, they lie in $K$, but $A$ is integrally closed, so they lie in $A$.
]


#example(number: 106)[
  Consider the simple field extension $bb("Q") subset bb("Q")(tau), tau=frac(1+sqrt(5), 2)$. The associated $bb("Q")$-linear map $op("T")_tau(x)=tau dot x$ (cf. *Def. 78*) maps $1 mapsto tau$ and $tau mapsto 1+tau$. By *Rmk. 80*, the coefficients of the minimal polynomial of $tau$ are given by the trace and the norm of $tau$ which is $1$ and $-1$, respectively. Hence $bb("Z") subset bb("Z")[tau]$ is integral. On the other hand, $tau' := frac(1+sqrt(3), 2)$ is not integral (its norm is $-frac(1, 2)$).
]
