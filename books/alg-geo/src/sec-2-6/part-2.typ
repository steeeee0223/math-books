#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Cartier Divisors

// Hartshorne II.6, Definition D8
#definition(title: "Sheaf of Total Quotient Rings")[
  - Given $shf.a in cat.ring_X$. For each $U in shf.t_X$, let $shf.s (U)$ be a
    multiplicatively closed subset of $shf.a (U)$. Then $U mapsto shf.s (U)$ is called
    the *multiplicatively closed subsheaf* of $shf.a$. We denote by
    $shf.s^(-1) shf.a in cat.ring_X$ the sheafification of
    $U mapsto shf.s (U)^(-1) shf.a (U)$. Note that
    $(shf.s^(-1) shf.a)_x simeq (shf.s_x)^(-1) shf.a_x$ for every $x in X$.

  - For $A in cat.ring$, denote by $A_reg$ the set of elements of $A$ which are
    not zero divisors, i.e.
    $
      A_reg := {a in A : s a != 0 text(" for any nonzero ") s in A}.
    $

  - Given $shf.a in cat.ring_X$ and any $U in shf.t_X$, define
    $
      shf.a_reg (U) := {s in shf.a (U) : s_x in (shf.a_x)_reg
        text(" for every ") x in U},
    $
    which is a multiplicatively closed subsheaf of $shf.a$. Note that in general
    $shf.a_reg (U) subset shf.a (U)_reg$. We define the *sheaf of total quotient
    rings* of $shf.a$ by $ops.frac shf.a := (shf.a_reg)^(-1) shf.a$.

  - If $(X, shf.o_X) in cat.sch$, let $shf.k_X := ops.frac shf.o_X$. There is a canonical
    monomorphism $shf.o_X arrow.r.hook shf.k_X$.

  - We denote by $shf.k_X^times in cat.ab_X$ the sheaf
    $U mapsto shf.k_X (U)^times$. Similarly, we can define $shf.o_X^times$. Via the
    canonical monomorphism, we may regard $shf.o_X^times$ as a subsheaf of
    $shf.k_X^times$, and there is an exact sequence in $cat.ab_X$:
    $
      1 -> shf.o_X^times -> shf.k_X^times -> shf.k_X^times \/ shf.o_X^times -> 1.
    $
]

// Hartshorne II.6, Definition D9
#definition(title: "Cartier Divisors")[
  - A *Cartier divisor* on $X in cat.sch$ is a global section
    $f in Gamma(X, shf.k_X^times \/ shf.o_X^times)$. Equivalently, we may represent
    $f$ as ${ (U_i, f_i) }$, where ${U_i}$ is an open cover of $X$ and each
    $f_i in shf.k_X^times (U_i)$ such that
    $f_i / f_j in shf.o_X^times (U_i inter U_j)$ for every $i, j$. We denote the
    group of all Cartier divisors on $X$ by $ops.cdiv (X)$.

  - A Cartier divisor $f in ops.cdiv (X)$ is *principal* if $f$ is in the image of
    $Gamma(X, shf.k_X^times) -> Gamma(X, shf.k_X^times \/ shf.o_X^times)$.

  - Two Cartier divisors $f, g in ops.cdiv (X)$ are *linearly equivalent* if
    $f / g$ is principal.
]

#proposition(number: "6.C")[
  #set enum(numbering: "i)", spacing: 1em)

  + If $X in cat.top$ is irreducible, then the constant presheaf
    $shf.f: U mapsto A$, where $A in cat.ab, cat.ring$ or $cat.mod("")$, is already a sheaf.

  + Suppose $X in cat.top$ is irreducible and has an open cover ${U_i}_(i in I)$.
    If $shf.g in cat.ab_X$ (or $cat.ring_X, cat.mod(X)$ is such that each $shf.g|_(U_i)$ is a
    constant sheaf, then so is $shf.g$.

  + If $X in cat.sch$ is an integral scheme, then $shf.k_X in cat.alg_X$ is the constant
    sheaf of $K = K(X)$.
]

#proof[
  *Proof of (i).* If $X$ is irreducible, then
  $inter_(U in shf.t_X) U = {eta}$, where $eta in X$ is the unique generic point
  by _[2.9]_. Thus, any two nonempty open sets have nonempty intersection.
  Further, if $V subset U$ are nonempty open sets, then
  $shf.f (U) = A = shf.f (V)$, i.e. the restriction map is $ops.id_A$.

  Now, given any $emptyset != U in shf.t_X$ with an open cover ${V_i}$ of $U$:

  - *(S3).* Suppose $s in shf.f (U)$ with $s|_i = 0$ for every $i$. Clearly,
    $s = ops.id_A (s) = s|_i = 0$, since $U inter V_i != emptyset$, i.e.
    $shf.f (U inter V_i) = A$.

  - *(S4).* Suppose we have $s_i in shf.f (V_i)$ such that
    $s_i|_j = s_j|_i$ for every $i, j$. Since
    $U inter V_i inter V_j != emptyset$, we have
    $s_i = ops.id_A (s_i) = s_i|_j = s_j|_i = ops.id_A (s_j) = s_j$ in $A$. So
    $s := s_i$ for every $i$ in $A = shf.f (V_i)$.

  Therefore, $shf.f$ is indeed a sheaf.
]

#proof[
  *Proof of (ii).* For each $i$, say $shf.g|_(U_i) simeq shf.f_i$, where $shf.f_i$
  denotes the constant sheaf of some $A_i$. For any $i, j$, since
  $U_i inter U_j != emptyset$, we have
  $
    A_i simeq shf.f_i (U_i inter U_j) simeq shf.g (U_i inter U_j)
    simeq shf.f_j (U_i inter U_j) simeq A_j.
  $
  Put $A := A_i$ for every $i$, and let $shf.f$ be the constant sheaf of $A$. I
  claim that $shf.g simeq shf.f$.

  Define a morphism $psi: shf.g -> shf.f$ as follows. For each
  $emptyset != U in shf.t_X$, let
  $
    psi_U: shf.g (U) -> shf.g (U inter U_i) isolongto shf.f (U inter U_i) = A = shf.f (U).
  $
  For any $P in X$, say $P in U_i$, then
  $psi_P: shf.g_P = (shf.g|_(U_i))_P isoto A = shf.f_P$ is an isomorphism. Thus,
  $psi$ defines an isomorphism.
]

#proof[
  *Proof of (iii).* Choose an open affine cover ${U_i}$ of $X$, say each
  $U_i = ops.spec A_i$ with $A_i$ an integral domain. Since $X$ is integral,
  $shf.o_(X, x)$ is an integral domain for every $x in X$, whence
  $shf.o_reg (U_i) = A_i - {0}$. It follows that the presheaf total quotient ring
  has value $shf.k (U_i) = ops.frac A_i isoBy("[3.6]") K$ as rings. Now, for any
  $x in U_i$, we have
  $
    K = shf.k (U_i) -> shf.k_x = ops.frac shf.o_(X, x)
    arrow.r.hook_(text("(4.A)")) ops.frac shf.o_(X, eta) = K,
  $
  where the first map is also injective since $K$ is a field. Hence,
  $shf.k|_(U_i)$ before sheafification is the constant presheaf $K$. However,
  $U_i$ is irreducible because $X$ is, so by (i), $shf.k|_(U_i)$ is the constant
  sheaf $K$. Finally, by (ii), $shf.k$ is the constant sheaf of $K$.
]

// Hartshorne II.6, Proposition 6.11
#proposition(number: 6.11)[
  Let $X$ be an integral, separated, Noetherian, *locally factorial* scheme,
  i.e. each local ring $shf.o_(X, x)$ is a UFD. Then the groups $ops.div (X)$ and
  $ops.cdiv (X)$ are isomorphic. Further, the principal Weil divisors correspond to
  the principal Cartier divisors under this isomorphism.
]

#proof[
  Since each stalk $shf.o_x$ is a UFD, it is integrally closed, whence $X$ is
  normal. So $X$ satisfies $(star)$, and we may define Weil divisors on $X$.

  *(I) From Cartier divisors to Weil divisors.*

  - Given ${ (U_i, f_i) } in ops.cdiv (X)$, we construct $D in ops.div (X)$. Note that
    each $f_i in shf.k^times (X) eqBy("(6.C)") K^times$. For each prime divisor
    $Y$ with generic point $xi$, take the coefficient to be
    $c_Y := nu_Y (f_i)$ for any $i$ with $U_i inter Y != emptyset$.

  - *Well-defined.* If there is another $j$ with $U_j inter Y != emptyset$,
    then
    $f_i \/ f_j in shf.o^times (U_i inter U_j) = shf.o (U_i inter U_j)^times
    arrow.r.hook shf.o_xi^times$,
    so $nu_Y (f_i \/ f_j) = 0$, i.e. $nu_Y (f_j) = nu_Y (f_i) = c_Y$.

  - Thus define $D := sum c_Y Y$, which is a finite sum since $X$ is
    Noetherian, we may choose finitely many $U_i$, and apply _(6.1)_.

  *(II) From Weil divisors to Cartier divisors.*

  - Given $D := sum n_i Y_i in ops.div (X)$, we construct a Cartier divisor. Given
    any $x in X$, if $x in Y_i$, we have the following diagram.

    #align(center)[
      #diagram(
        cell-size: 18mm,
        $
          ops.spec (tensor(A_idl.p, A slash idl.q_i, over: A)) edge("r", ->) edge("d", text("(v)"), ->)
          & ops.spec (A slash idl.q_i) edge("r", text("(iii)"), ->) edge("d", ->)
          & U inter Y_i edge("r", text("(3.3)"), ->)
          & U times_X Y_i edge("r", ->) edge("d", text("(ii)"), ->)
          & Y_i edge("d", text("closed"), ->) \
          T_x = ops.spec shf.o_x edge("r", text("(iv)"), ->)
          & ops.spec A edge("rr", text("(i)"), ->)
          & & U edge("r", text("open"), ->)
          & X
        $,
      )
    ]

    Here:

    #set enum(numbering: "i)", spacing: 1em)

    + Choose an open affine neighborhood $U = ops.spec A$ of $x in X$; then $A$ is
      an integral domain.

    + $Y_i$ is a prime divisor with generic point $xi_i$. By _[3.11a]_, the
      map (ii) is a closed immersion.

    + Now, $U inter Y_i arrow.r.hook U$ is a closed subscheme of the integral
      scheme $ops.spec A$, so such $idl.q_i lt.closed A$ determines
      $U inter Y_i$. Further, $U inter Y_i$ is an open subscheme of the
      integral scheme $Y_i$, so $A \/ idl.q_i$ is an integral domain, i.e.
      $idl.q_i in ops.spec A$.

    + Let $x = idl.p in ops.spec A = U$; then the map (iv) is induced by
      $A arrow.r.hook A_idl.p$.

    + Again, as (ii) is a closed immersion, so is the base extension (v) via
      (iv). Further,
      $tensor(A_idl.p, A slash idl.q_i, over: A) simeq A_idl.p \/ idl.q_i A_idl.p$ is an integral
      domain, whence
      $Y_i inter T_x = ops.spec (tensor(A_idl.p, A slash idl.q_i, over: A))$ is a closed
      integral subscheme of $T_x$.

  - Moreover,
    $
      ops.codim(Y_i inter T_x, T_x) & = ops.codim(idl.q_i A_idl.p, A_idl.p)
                                      = ops.codim(A \/ idl.q_i, A)
                                      = ops.codim(U inter Y_i, U) \
                                    & = ops.codim(Y_i, X) = 1.
    $
    Thus $U inter Y_i$ is a prime divisor of $U$ with generic point $idl.q_i$.
    Further, $x in U inter Y_i$, so $Y_i inter T_x$ is also a prime divisor
    of $T_x$. Therefore, $D$ restricts to a local divisor
    $D_x := sum_(x in Y_i) n_i (Y_i inter T_x) in ops.div (T_x)$.

  - Since $X$ is a Noetherian domain, so is $T_x$, and thus $shf.o_x$. Further,
    $shf.o_x$ is a UFD by assumption. It follows from _(6.2)_ that
    $ops.cl (T_x) = 0$. So there exists $f_x in K^times$ such that
    $D_x = ops.dv (f_x)$ in $ops.div (T_x)$.

  - Now, consider $ops.dv (f_x) = sum nu_(Y_i) (f_x) Y_i$ in $ops.div (X)$, which also
    restricts to
    $
      sum_(x in Y_i) nu_(Y_i inter T_x) (f_x) (Y_i inter T_x)
      = sum_(x in Y_i) nu_(Y_i) (f_x) (Y_i inter T_x)
      = D_x quad text("in") ops.div (T_x),
    $
    as the valuations $((A_idl.p)_(idl.q_i), nu_(Y_i inter T_x))$ and
    $(A_(idl.q_i), nu_(Y_i))$ are the same. Therefore, $ops.dv (f_x)$ and $D$ differ
    only on those prime divisors $Y_i$ not containing $x$. Hence, there are
    only finitely many $Y_i$ not containing $x$ for which
    $nu_(Y_i) (f_x) != 0$ or $n_i != 0$.

  - In fact, the space $T_x = inter { U_x : U_x in shf.n_x (X) }$, so we may
    replace $T_x$ by some open neighborhood $U_x$ so that $D$ and $ops.dv (f_x)$
    have the same restriction to $U_x$, e.g. the open affine $U$ chosen above.
    Cover $X$ by these open sets ${U_x}_(x in X)$. Since each
    $f_x in K^times = shf.k^times (U_x)$, we claim that
    ${ (U_x, f_x) }_(x in X)$ gives a well-defined Cartier divisor.

  - *Well-defined.* Suppose $f, f' in K^times$ give the same Weil divisor on
    some open set $U subset X$, i.e. $nu_(Y_i) (f) = nu_(Y_i) (f')$ for every
    $Y_i$ with $Y_i inter U != emptyset$. Then
    $nu_(Y_i) (f \/ f') = 0$, i.e. $f \/ f' in shf.o_(xi_i)^times$.

    - For any open affine subset $V = ops.spec B$ of $X$, say
      $xi_i = idl.q_i in ops.spec B$. Then $shf.o_(xi_i)^times = B_(idl.q_i)^times$ and
      $ops.ht idl.q_i = 1$. Since $B = shf.o (V)$ is a normal Noetherian domain, we have
      $
        f \/ f' in inter_(Y_i inter V != emptyset) shf.o_(xi_i)
        = inter_(ops.ht idl.q_i = 1) B_(idl.q_i) eqBy("(6.3)") B.
      $

    - Let ${V_i}$ be an open affine cover of $U$. Then
      $(f \/ f')|_i in shf.o (V_i)$ for each $i$. Further, for each $i, j$, their
      restrictions to $shf.o (V_i inter V_j)$ agree, so we may glue
      ${(f \/ f')|_i}$ to obtain $s in shf.o (U)$. In fact, $s = f \/ f'$ since
      each $(f \/ f')|_i in ops.frac shf.o (V_i) = shf.k (V_i) = K$. Thus
      $f \/ f' in shf.o (U)$. Similarly, $f' / f in shf.o (U)$, so
      $f \/ f' in shf.o (U)^times = shf.o^times (U)$.

    Replacing $(f, f', U)$ by $(f_x, f_(x'), U_x inter U_(x'))$ gives
    $f_x / f_(x') in shf.o^times (U_x inter U_(x'))$, whence
    ${ (U_x, f_x) } in ops.cdiv (X)$. If there is another
    ${ (V_i, f'_i) }$ representing this Cartier divisor, replacing
    $(f, f', U)$ by $(f_x, f'_i, U_x inter V_i)$ shows that
    $f_x \/ f'_i in shf.o^times (U_x inter V_i)$. Thus, such Cartier divisor is
    independent of the choice of the open cover.

  *(III) The two constructions are inverse to each other.*

  - For any $D in ops.div (X)$,
    $
      D = sum n_i Y_i & mapsto { (U_x, f_x) } text(" with ") nu_(Y_i) (f_x) = n_i
                        text(" if ") x in Y_i \
                      & mapsto sum c_(Y_i) Y_i text(" with ") c_(Y_i) = nu_(Y_i) (f_x)
                        text(" if ") Y_i inter U_x != emptyset \
                      & = sum n_i Y_i = D.
    $

  - For any $C in ops.cdiv (X)$,
    $
      C = { (U_i, f_i) } & mapsto D = sum c_Y dot Y text(" with ") c_Y = nu_Y (f_i)
                           text(" if ") U_i inter Y != emptyset \
                         & mapsto { (U_x, f_x) } text(" with ") nu_Y (f_x) = n_i = c_Y
                           text(" if ") x in Y.
    $
    If $Y inter (U_i inter U_x) != emptyset$, then
    $nu_Y (f_x) = c_Y = nu_Y (f_i)$, whence $nu_Y (f_x / f_i) = 0$, i.e.
    $f_x / f_i in shf.o^times (U_i inter U_x)$. Therefore,
    ${ (U_x, f_x) } = { (U_i, f_i) } = C$.
]

// Hartshorne II.6, Remark 6.11.1A
#remark(title: "6.11.1A")[
  - *(Regular Schemes).* A scheme $X$ is *regular* if each stalk
    $shf.o_(X, x)$ is a regular local ring.

  - Recall that a regular local ring is a UFD, whence _(6.11)_ also applies to
    any regular integral separated Noetherian scheme.
]

// Hartshorne II.6, Remark 6.11.2
#remark(title: "6.11.2")[
  - $D in ops.div (X)$ is a *locally principal* Weil divisor if $X$ has an open
    cover ${U_i}$ such that each restriction $D|_(U_i) in ops.div (U_i)$ is
    principal.

  - If $X$ is a normal scheme, not necessarily locally factorial, then the
    proof in _(6.11)_ shows that the Cartier divisors are the same as locally
    principal Weil divisors. Thus, in this case, the map
    $ops.cdiv (X) -> ops.div (X)$ is injective.
]
