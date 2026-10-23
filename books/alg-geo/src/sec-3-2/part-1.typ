#import "@preview/fletcher:0.5.8" as fletcher: *
#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

#proposition(number: "2.1")[
  If $A$ is a ring, then every $A$-module is isomorphic to a submodule of an injective $A$-module. That is, $cat.mod(A)$ has enough injectives.
]
#proof[
  Exercise. // TODO
]

#proposition(number: "2.2")[
  Let $(X, shf.o_X)$ be a ringed space. Then $cat.mod(X)$ has enough injectives.
]
#proof[
  Let $shf.f in cat.mod(X)$. We construct an injective $shf.o_X$-module in the following steps.

  *(I).* Working on stalks
  - For each $x in X$, the stalk $shf.f_x in cat.mod(shf.o_(X,x))$. By _(2.1)_, there is an injection $shf.f_x inclusion(iota_x, "") I_x$, where $I_x$ is an injective $O_(X,x)$-module.

  *(II).* Construct a sheaf

  - For each $x in X$, consider the inclusion ${x} inclusion(j_x, cat.top) X$.
  - We treat $I_x$ as a sheaf on ${x}$, then we obtain the direct image sheaf
    $
      j_(x ast)(I_x) eqBy("Def.") I_(x)(j_x^(-1)(U)) = cases(
        I_x quad "if" x in U,
        0 quad "if" x in.not U,
      )
    $
  - We will then consider the product sheaf $shf.i:= prod(j_(x ast)(I_x), b: x in X)$.

  *(III).* Construct a sheaf morphism $shf.f inclusion("", "") shf.i$.
  - First, we construct $phi_x:shf.f->j_(x ast)(I_x)$ for every $x in X$. For every open $U subset X$, we define
    $
      phi_(x, U):shf.f\(U) & to j_(x ast)(I_x)(U), \
                         s & mapsto.long cases(
                               iota_(x)(s_x) quad "if" x in U,
                               0 quad "if" x in.not U.,
                             )
    $
    By universal property of product, we obtain a unique morphism $phi:shf.f to prod(j_(x ast)(I_x), b: x in X)$.
  - _Claim: $phi$ is injective._ Suppose $s in shf.f\(U)$ satisfies $phi_(U)(s)=0$. This means $iota_(x)(s_x)=0$ for all $x in U$. As $iota_x$ is injective, we have $s_x=0$ for all $x in U$, and hence, $s=0$ by definition of sheaf. Now, every $phi_U$ is injective, and thus, so is $phi$.

  *(IV).* $shf.i$ is an injective sheaf.
  - For any $shf.g in cat.mod(shf.o_X)$, we see that
    $
      ops.hom(shf.g, shf.i, over: shf.o_X) & = prod(ops.hom(shf.g, j_(x ast)(I_x), over: shf.o_X)) & "by def. of product" \
                                           & isoBy("") prod(ops.hom(shf.g_x, I_x, over: O_(X,x)))  &          "(check!)".
    $
  - Now, since $I_x$ is injective, the functor $ops.hom(-, I_x, over: O_(X,x))$ is exact. Also, taking direct product also preserves exactness, so $ops.hom(-, shf.i, over: O_X)$ is also exact. Therefore, $shf.i$ is an injective $shf.o_X$-module.
]

#corollary(number: "2.3")[
  If $X$ is any topological space, then $cat.ab(X)$ has enough injectives.
]
#proof[
  By taking $shf.o_X$ to be the constant sheaf of rings $bb(Z)$, $(X, shf.o_X)$ is a ringed space and $cat.mod(X)=cat.ab(X)$.
]

