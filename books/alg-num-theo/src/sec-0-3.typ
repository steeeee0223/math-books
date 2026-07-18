#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

== Algebras

#definition(number: "48", title: [Algebras])[
  - An $A$-*algebra* is a ring $B$ which contains the ring $A$ as a subring. In particular, $B$ is an $A$-module by restricting multiplication to $A$.
  - Let $B$ and $C$ be two $A$-algebras. A ring homomorphism $phi:B -> C$ is called an $A$-*algebra homomorphism* if $phi(a)=a, forall a in A$, i.e. $phi|_A=1_A$. In particular, an $A$-algebra homomorphism is a ring homomorphism which is also $A$-linear.

]


#remark(number: 49)[
  - _(a)_ $A$-algebras together with $A$-algebra homomorphisms form a category, where isomorphisms are given by bijective $A$-algebra homomorphisms.
  - _(b)_ A ring homomorphism $phi:A -> B$ turns $B$ into a $phi(A)$-algebra which by abuse of language we also call an $A$-algebra.
  - _(c)_ If $B$ and $C$ are $A$-algebras via the ring homomorphisms $phi:A -> B$ and $psi:A -> C$. Then the ring homomorphism $alpha:B -> C$ is an $A$-algebra homomorphism iff $alpha compose phi=psi$.
  - _(d)_ In general, $op("Hom")_(A-text("Alg."))(B,C) subset.not.eq op("Hom")_(text("Ring"))(B,C)$ for $A$-algebras $B$ and $C$.

]


#example(number: 50)[
  Considering $A$ as the constants in the polynomial ring $A[x_1, dots.h.c ,x_n]$, the latter becomes an $A$-algebra in a natural way. Moreover, the natural ring isomorphism $A[x_1, dots.h.c ,x_(n-1)][x_n] equiv A[x_1, dots.h.c ,x_n]$ is actually an $A$-algebra homomorphism.\ On the other hand, $phi:bb("C")[x] -> bb("C")[x], sum lambda_i x^i mapsto sum overline(lambda)_i x^i$ is clearly a ring homomorphism, but not a $bb("C")$-algebra homomorphism.
]


#proposition(number: 51)[
  Let $B$ be an $A$-algebra and $alpha_1, dots.h.c ,alpha_n in B$. Then there exists a unique $A$-algebra homomorphism $phi:A[x_1, dots.h.c ,x_n] -> B$ determined by $phi(x_i)=alpha_i$, the so-called *substitution homomorphism*.
]


#definition(number: "52", title: [Finitely Generated Algebras])[
  An $A$-algebra $B$ is finitely generated if there exists a surjective $A$-algebra homomorphism $phi:A[x_1, dots.h.c ,x_n] arrow.r.twohead B$.\ (cf. *Prop.51*)
]


#remark(number: 53)[
  If $B$ is a finitely generated $A$-algebra, then $B equiv A[x_1, dots.h.c ,x_n]/op("ker")phi$ as $A$-algebras. Setting $b_i := phi(x_i) in B, (1 <= i <= n)$, we have $op("im")phi={ sum a_alpha b^alpha:a_alpha in A}$, where $b^alpha=b_1^(alpha_1) dots.h.c b_n^(alpha_n)$. We also write $B=A[b_1, dots.h.c ,b_n]$ and call it the $A$-*algebra generated* by $b_1, dots.h.c ,b_n in B$.
]
