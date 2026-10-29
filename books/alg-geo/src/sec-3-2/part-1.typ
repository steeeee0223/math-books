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

#definition(title: "Sheaf Cohomology")[
  Let $X$ be a topological space. The _cohomology groups_ of an abelian
  sheaf $shf.f$ on $X$ are
  $
    H^(q)(X, shf.f) := R^(q) Gamma(X, shf.f), quad q >= 0,
  $
  where the right derived functors are taken in $cat.ab(X)$.
  For an open subset $U subset X$, write
  $H^(q)(U, shf.f)=H^(q)(U, shf.f|_(U))$.
]

Recall the definition of flasque sheaves in _[II.1.16]_. We will use the results in the remaining section:

#definition(title: "Flasque Sheaves")[
  Let $(X, shf.o_X)$ be a ringed space. A sheaf $shf.f in cat.mod(shf.o_X)$ is _flasque_ if
  the restriction map
  $
    Gamma(U, shf.f) to Gamma(V, shf.f)
  $
  is surjective for every inclusion of open subsets $V subset U$ of $X$.
]

// Hartshorne III.2.4.
#lemma(number: "2.4", title: "Injective Sheaves Are Flasque")[
  Let $X$ be a topological space. Every injective object of $cat.mod(shf.o_X)$ is flasque.
]

#remark()[
  Let $(X, shf.o_X)$ be a ringed space.
  - From the results of _(2.2)_ and _(1.Aa)_, every object $shf.f in cat.mod(shf.o_X)$ admits an injective resolution.
  - By _(2.4)_, the result gives rise to a flasque resolution.
  Thus, we can always pick a flasque resolution of an $shf.o_X$-module.
]

// Hartshorne III.2.5 and its acyclic-resolution consequence.
#proposition(number: "2.5", title: "Flasque Resolutions Compute Cohomology")[
  If $shf.f$ is a flasque abelian sheaf on a topological space $X$, then
  $
    H^(q)(U, shf.f)=0 quad (q>0)
  $
  for every open subset $U subset X$.
  Consequently, if $0 to shf.f to sym.cplx(I)$ is a flasque resolution, then
  $
    H^(q)(X, shf.f) simeq sym.coho(Gamma(X, sym.cplx(I)), q)
    quad (q>=0).
  $
]
