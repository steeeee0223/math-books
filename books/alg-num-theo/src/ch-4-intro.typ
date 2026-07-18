#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

#motivation(number: "218")[
  Consider a polynomial $f=frac(f, 1) in bb("C")[x]_((x-a))$ given by
  $
    f(x)=a_0+a_1(x-a)+ dots.h.c +a_n(x-a)^n.
  $

  At $frak("p")=(x-a)$ we assign to $f$ the "value" $a_0 equiv f op("mod") frak("p")$. Modding out higher powers $(x-a)^n$ yields the higher order terms of $f$ corresponding to the successive derivatives of $f$ at $frak("p")$. More generally, we can expand a rational function $frac(f, g)$ with $g eq.not 0 op("mod") frak("p")$ into a Laurent series $sum_(i=m)^oo a_i(x-a)^i, (m in bb("Z"))$, (for the moment this notation is purely formal and stands for the sequence $(s_n)$ of partial sums $s_n := sum_(i=0)^n a_i(x-a)^i$).\
  Similarly, consider $f in bb("Z")_((p))={frac(a, b) in bb("Q"):p divides.not b}$ for a prime $p in bb("Z")$. By division algorithm we have,
  $
    f=p f_1+a_0, f_1=p f_2+a_1, dots.h.c , f_n=a_n, quad (0 <= a_i <= p-1)
  $

  gives the $p$-adic expansion $f=a_0+a_1 p+ dots.h.c +a_n p^n$. More generally, we can expand rational numbers into Laurent series, leading eventually to $p$-*adic numbers*.\
  These examples are obtained by a process called *completion*. Morally, this allows us to focus on local information of global data in a sense that we yet have to specify. An informal example is provided by the ring of holomorphic functions $cal("O")(U)$ or the field of meromorphic functions $cal("M")(U)$ on an open subset $U subset bb("C")$. We should think of these as "global" objects. Locally, we can develop these functions into power or Laurent series. This is a powerful tool in the theory of functions which we want to make available in our algebraic context.
]
