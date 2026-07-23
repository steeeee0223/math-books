#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *

#show: show-theorion

=== Inverse Limits

An inverse system $(A_n)$ consists of objects $A_n$ and compatible transition
maps $A_(n')->A_n$ for $n'>=n$. Its inverse limit consists of compatible
families. The system satisfies the *Mittag–Leffler condition* if, for each
$n$, the images of $A_(n')->A_n$ are eventually constant as $n'$ increases.

// Hartshorne II.9, Proposition 9.1
#proposition(number: "9.1")[
  Let
  $0 -> (A_n) -> (B_n) -> (C_n) -> 0$
  be a short exact sequence of inverse systems of abelian groups.

  + If $(B_n)$ satisfies Mittag–Leffler, so does $(C_n)$.
  + If $(A_n)$ satisfies Mittag–Leffler, then
    $0 -> op("lim") A_n -> op("lim") B_n -> op("lim") C_n -> 0$
    is exact.
]


// Hartshorne II.9, Proposition 9.2
#proposition(number: "9.2")[
  Inverse limits exist in the category of sheaves of abelian groups on a
  topological space $X$. If $shf.f=op("lim") shf.f_n$, then for every open $U$,
  $Gamma(U, shf.f)=op("lim") Gamma(U, shf.f_n)$.
]


For a ring $A$ and ideal $I$, write
$hat(A)=op("lim") A\/I^n$ for the $I$-adic completion; for an $A$-module $M$,
write $hat(M)=op("lim") M\/I^n M$.

// Hartshorne II.9, Theorem 9.3A
#theorem(number: "9.3A")[
  Let $A$ be noetherian, $I subset.eq A$, and let hats denote $I$-adic
  completion.

  + $hat(I)=op("lim") I\/I^n$ is an ideal of $hat(A)$,
    $hat(I)^n=I^n hat(A)$, and $hat(A)\/hat(I)^n simeq A\/I^n$.
  + For finite $M$, $hat(M) simeq M times.o_A hat(A)$.
  + Completion is exact on finite $A$-modules.
  + $hat(A)$ is noetherian.
  + If finite $A\/I^n$-modules $M_n$ have surjective transitions with kernel
    $I^n M_(n')$, then $M=op("lim") M_n$ is finite over $hat(A)$ and
    $M_n simeq M\/I^n M$.
]
