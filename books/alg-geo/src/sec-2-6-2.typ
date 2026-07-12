#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

=== Cartier Divisors

#definition(title: "Sheaf of Total Quotient Rings")[
  - Given $Aa in Ring_X$. For each $U in TT_X$, let $Ss(U)$ be a
    multiplicatively closed subset of $Aa(U)$. Then $U mapsto Ss(U)$ is called
    the *multiplicatively closed subsheaf* of $Aa$. We denote by
    $Ss^(-1) Aa in Ring_X$ the sheafification of
    $U mapsto Ss(U)^(-1) Aa(U)$. Note that
    $(Ss^(-1) Aa)_x simeq (Ss_x)^(-1) Aa_x$ for every $x in X$.

  - For $A in Ring$, denote by $A_reg$ the set of elements of $A$ which are
    not zero divisors, i.e.
    $
      A_reg := {a in A : s a != 0 text(" for any nonzero ") s in A}.
    $

  - Given $Aa in Ring_X$ and any $U in TT_X$, define
    $
      Aa_reg(U) := {s in Aa(U) : s_x in (Aa_x)_reg
        text(" for every ") x in U},
    $
    which is a multiplicatively closed subsheaf of $Aa$. Note that in general
    $Aa_reg(U) subset Aa(U)_reg$. We define the *sheaf of total quotient
    rings* of $Aa$ by $Frac Aa := (Aa_reg)^(-1) Aa$.

  - If $(X, OO_X) in Sch$, let $KK_X := Frac OO_X$. There is a canonical
    monomorphism $OO_X arrow.r.hook KK_X$.

  - We denote by $KK_X^times in Ab_X$ the sheaf
    $U mapsto KK_X (U)^times$. Similarly, we can define $OO_X^times$. Via the
    canonical monomorphism, we may regard $OO_X^times$ as a subsheaf of
    $KK_X^times$, and there is an exact sequence in $Ab_X$:
    $
      1 -> OO_X^times -> KK_X^times -> KK_X^times \/ OO_X^times -> 1.
    $
]

#definition(title: "Cartier Divisors")[
  - A *Cartier divisor* on $X in Sch$ is a global section
    $f in Gamma(X, KK_X^times \/ OO_X^times)$. Equivalently, we may represent
    $f$ as ${ (U_i, f_i) }$, where ${U_i}$ is an open cover of $X$ and each
    $f_i in KK_X^times (U_i)$ such that
    $f_i / f_j in OO_X^times (U_i inter U_j)$ for every $i, j$. We denote the
    group of all Cartier divisors on $X$ by $CDiv(X)$.

  - A Cartier divisor $f in CDiv(X)$ is *principal* if $f$ is in the image of
    $Gamma(X, KK_X^times) -> Gamma(X, KK_X^times \/ OO_X^times)$.

  - Two Cartier divisors $f, g in CDiv(X)$ are *linearly equivalent* if
    $f / g$ is principal.
]

#proposition(number: "6.C")[
  #set enum(numbering: "i)", spacing: 1em)

  + If $X in Top$ is irreducible, then the constant presheaf
    $FF: U mapsto A$, where $A in Ab, Ring$ or $MOD("")$, is already a sheaf.

  + Suppose $X in Top$ is irreducible and has an open cover ${U_i}_(i in I)$.
    If $GG in Ab_X$ (or $Ring_X, MOD(X)$ is such that each $GG|_(U_i)$ is a
    constant sheaf, then so is $GG$.

  + If $X in Sch$ is an integral scheme, then $KK_X in ALG_X$ is the constant
    sheaf of $K = K(X)$.
]

#proof[
  *Proof of (i).* If $X$ is irreducible, then
  $inter_(U in TT_X) U = {eta}$, where $eta in X$ is the unique generic point
  by _[2.9]_. Thus, any two nonempty open sets have nonempty intersection.
  Further, if $V subset U$ are nonempty open sets, then
  $FF(U) = A = FF(V)$, i.e. the restriction map is $id_A$.

  Now, given any $emptyset != U in TT_X$ with an open cover ${V_i}$ of $U$:

  - *(S3).* Suppose $s in FF(U)$ with $s|_i = 0$ for every $i$. Clearly,
    $s = id_A(s) = s|_i = 0$, since $U inter V_i != emptyset$, i.e.
    $FF(U inter V_i) = A$.

  - *(S4).* Suppose we have $s_i in FF(V_i)$ such that
    $s_i|_j = s_j|_i$ for every $i, j$. Since
    $U inter V_i inter V_j != emptyset$, we have
    $s_i = id_A(s_i) = s_i|_j = s_j|_i = id_A(s_j) = s_j$ in $A$. So
    $s := s_i$ for every $i$ in $A = FF(V_i)$.

  Therefore, $FF$ is indeed a sheaf.
]

#proof[
  *Proof of (ii).* For each $i$, say $GG|_(U_i) simeq FF_i$, where $FF_i$
  denotes the constant sheaf of some $A_i$. For any $i, j$, since
  $U_i inter U_j != emptyset$, we have
  $
    A_i simeq FF_i(U_i inter U_j) simeq GG(U_i inter U_j)
    simeq FF_j(U_i inter U_j) simeq A_j.
  $
  Put $A := A_i$ for every $i$, and let $FF$ be the constant sheaf of $A$. I
  claim that $GG simeq FF$.

  Define a morphism $psi: GG -> FF$ as follows. For each
  $emptyset != U in TT_X$, let
  $
    psi_U: GG(U) -> GG(U inter U_i) isolongto FF(U inter U_i) = A = FF(U).
  $
  For any $P in X$, say $P in U_i$, then
  $psi_P: GG_P = (GG|_(U_i))_P isoto A = FF_P$ is an isomorphism. Thus,
  $psi$ defines an isomorphism.
]

#proof[
  *Proof of (iii).* Choose an open affine cover ${U_i}$ of $X$, say each
  $U_i = Spec A_i$ with $A_i$ an integral domain. Since $X$ is integral,
  $OO_(X, x)$ is an integral domain for every $x in X$, whence
  $OO_reg(U_i) = A_i - {0}$. It follows that the presheaf total quotient ring
  has value $KK(U_i) = Frac A_i isoBy("[3.6]") K$ as rings. Now, for any
  $x in U_i$, we have
  $
    K = KK(U_i) -> KK_x = Frac OO_(X, x)
    arrow.r.hook_(text("(4.A)")) Frac OO_(X, eta) = K,
  $
  where the first map is also injective since $K$ is a field. Hence,
  $KK|_(U_i)$ before sheafification is the constant presheaf $K$. However,
  $U_i$ is irreducible because $X$ is, so by (i), $KK|_(U_i)$ is the constant
  sheaf $K$. Finally, by (ii), $KK$ is the constant sheaf of $K$.
]

#proposition(number: 6.11)[
  Let $X$ be an integral, separated, Noetherian, *locally factorial* scheme,
  i.e. each local ring $OO_(X, x)$ is a UFD. Then the groups $Div(X)$ and
  $CDiv(X)$ are isomorphic. Further, the principal Weil divisors correspond to
  the principal Cartier divisors under this isomorphism.
]

#proof[
  Since each stalk $OO_x$ is a UFD, it is integrally closed, whence $X$ is
  normal. So $X$ satisfies $(star)$, and we may define Weil divisors on $X$.

  *(I) From Cartier divisors to Weil divisors.*

  - Given ${ (U_i, f_i) } in CDiv(X)$, we construct $D in Div(X)$. Note that
    each $f_i in KK^times (X) eqBy("(6.C)") K^times$. For each prime divisor
    $Y$ with generic point $xi$, take the coefficient to be
    $c_Y := nu_Y (f_i)$ for any $i$ with $U_i inter Y != emptyset$.

  - *Well-defined.* If there is another $j$ with $U_j inter Y != emptyset$,
    then
    $f_i \/ f_j in OO^times (U_i inter U_j) = OO(U_i inter U_j)^times
    arrow.r.hook OO_xi^times$,
    so $nu_Y (f_i \/ f_j) = 0$, i.e. $nu_Y (f_j) = nu_Y (f_i) = c_Y$.

  - Thus define $D := sum c_Y Y$, which is a finite sum since $X$ is
    Noetherian, we may choose finitely many $U_i$, and apply _(6.1)_.

  *(II) From Weil divisors to Cartier divisors.*

  - Given $D := sum n_i Y_i in Div(X)$, we construct a Cartier divisor. Given
    any $x in X$, if $x in Y_i$, we have the following diagram.

    #align(center)[
      #diagram(
        cell-size: 18mm,
        $
          Spec(tensor(A_pp, A slash qq_i, A)) edge("r", ->) edge("d", text("(v)"), ->)
          & Spec(A slash qq_i) edge("r", text("(iii)"), ->) edge("d", ->)
          & U inter Y_i edge("r", text("(3.3)"), ->)
          & U times_X Y_i edge("r", ->) edge("d", text("(ii)"), ->)
          & Y_i edge("d", text("closed"), ->) \
          T_x = Spec OO_x edge("r", text("(iv)"), ->)
          & Spec A edge("rr", text("(i)"), ->)
          & & U edge("r", text("open"), ->)
          & X
        $,
      )
    ]

    Here:

    #set enum(numbering: "i)", spacing: 1em)

    + Choose an open affine neighborhood $U = Spec A$ of $x in X$; then $A$ is
      an integral domain.

    + $Y_i$ is a prime divisor with generic point $xi_i$. By _[3.11a]_, the
      map (ii) is a closed immersion.

    + Now, $U inter Y_i arrow.r.hook U$ is a closed subscheme of the integral
      scheme $Spec A$, so such $qq_i lt.closed A$ determines
      $U inter Y_i$. Further, $U inter Y_i$ is an open subscheme of the
      integral scheme $Y_i$, so $A \/ qq_i$ is an integral domain, i.e.
      $qq_i in Spec A$.

    + Let $x = pp in Spec A = U$; then the map (iv) is induced by
      $A arrow.r.hook A_pp$.

    + Again, as (ii) is a closed immersion, so is the base extension (v) via
      (iv). Further,
      $tensor(A_pp, A slash qq_i, A) simeq A_pp \/ qq_i A_pp$ is an integral
      domain, whence
      $Y_i inter T_x = Spec(tensor(A_pp, A slash qq_i, A))$ is a closed
      integral subscheme of $T_x$.

  - Moreover,
    $
      codim(Y_i inter T_x, T_x) & = codim(qq_i A_pp, A_pp)
                                  = codim(A \/ qq_i, A)
                                  = codim(U inter Y_i, U) \
                                & = codim(Y_i, X) = 1.
    $
    Thus $U inter Y_i$ is a prime divisor of $U$ with generic point $qq_i$.
    Further, $x in U inter Y_i$, so $Y_i inter T_x$ is also a prime divisor
    of $T_x$. Therefore, $D$ restricts to a local divisor
    $D_x := sum_(x in Y_i) n_i (Y_i inter T_x) in Div(T_x)$.

  - Since $X$ is a Noetherian domain, so is $T_x$, and thus $OO_x$. Further,
    $OO_x$ is a UFD by assumption. It follows from _(6.2)_ that
    $Cl(T_x) = 0$. So there exists $f_x in K^times$ such that
    $D_x = dv(f_x)$ in $Div(T_x)$.

  - Now, consider $dv(f_x) = sum nu_(Y_i)(f_x) Y_i$ in $Div(X)$, which also
    restricts to
    $
      sum_(x in Y_i) nu_(Y_i inter T_x)(f_x) (Y_i inter T_x)
      = sum_(x in Y_i) nu_(Y_i)(f_x) (Y_i inter T_x)
      = D_x quad text("in") Div(T_x),
    $
    as the valuations $((A_pp)_(qq_i), nu_(Y_i inter T_x))$ and
    $(A_(qq_i), nu_(Y_i))$ are the same. Therefore, $dv(f_x)$ and $D$ differ
    only on those prime divisors $Y_i$ not containing $x$. Hence, there are
    only finitely many $Y_i$ not containing $x$ for which
    $nu_(Y_i)(f_x) != 0$ or $n_i != 0$.

  - In fact, the space $T_x = inter { U_x : U_x in NN_x(X) }$, so we may
    replace $T_x$ by some open neighborhood $U_x$ so that $D$ and $dv(f_x)$
    have the same restriction to $U_x$, e.g. the open affine $U$ chosen above.
    Cover $X$ by these open sets ${U_x}_(x in X)$. Since each
    $f_x in K^times = KK^times (U_x)$, we claim that
    ${ (U_x, f_x) }_(x in X)$ gives a well-defined Cartier divisor.

  - *Well-defined.* Suppose $f, f' in K^times$ give the same Weil divisor on
    some open set $U subset X$, i.e. $nu_(Y_i)(f) = nu_(Y_i)(f')$ for every
    $Y_i$ with $Y_i inter U != emptyset$. Then
    $nu_(Y_i)(f \/ f') = 0$, i.e. $f \/ f' in OO_(xi_i)^times$.

    - For any open affine subset $V = Spec B$ of $X$, say
      $xi_i = qq_i in Spec B$. Then $OO_(xi_i)^times = B_(qq_i)^times$ and
      $Ht qq_i = 1$. Since $B = OO(V)$ is a normal Noetherian domain, we have
      $
        f \/ f' in inter_(Y_i inter V != emptyset) OO_(xi_i)
        = inter_(Ht qq_i = 1) B_(qq_i) eqBy("(6.3)") B.
      $

    - Let ${V_i}$ be an open affine cover of $U$. Then
      $(f \/ f')|_i in OO(V_i)$ for each $i$. Further, for each $i, j$, their
      restrictions to $OO(V_i inter V_j)$ agree, so we may glue
      ${(f \/ f')|_i}$ to obtain $s in OO(U)$. In fact, $s = f \/ f'$ since
      each $(f \/ f')|_i in Frac OO(V_i) = KK(V_i) = K$. Thus
      $f \/ f' in OO(U)$. Similarly, $f' / f in OO(U)$, so
      $f \/ f' in OO(U)^times = OO^times (U)$.

    Replacing $(f, f', U)$ by $(f_x, f_(x'), U_x inter U_(x'))$ gives
    $f_x / f_(x') in OO^times (U_x inter U_(x'))$, whence
    ${ (U_x, f_x) } in CDiv(X)$. If there is another
    ${ (V_i, f'_i) }$ representing this Cartier divisor, replacing
    $(f, f', U)$ by $(f_x, f'_i, U_x inter V_i)$ shows that
    $f_x \/ f'_i in OO^times (U_x inter V_i)$. Thus, such Cartier divisor is
    independent of the choice of the open cover.

  *(III) The two constructions are inverse to each other.*

  - For any $D in Div(X)$,
    $
      D = sum n_i Y_i & mapsto { (U_x, f_x) } text(" with ") nu_(Y_i)(f_x) = n_i
                        text(" if ") x in Y_i \
                      & mapsto sum c_(Y_i) Y_i text(" with ") c_(Y_i) = nu_(Y_i)(f_x)
                        text(" if ") Y_i inter U_x != emptyset \
                      & = sum n_i Y_i = D.
    $

  - For any $C in CDiv(X)$,
    $
      C = { (U_i, f_i) } & mapsto D = sum c_Y dot Y text(" with ") c_Y = nu_Y (f_i)
                           text(" if ") U_i inter Y != emptyset \
                         & mapsto { (U_x, f_x) } text(" with ") nu_Y (f_x) = n_i = c_Y
                           text(" if ") x in Y.
    $
    If $Y inter (U_i inter U_x) != emptyset$, then
    $nu_Y (f_x) = c_Y = nu_Y (f_i)$, whence $nu_Y (f_x / f_i) = 0$, i.e.
    $f_x / f_i in OO^times (U_i inter U_x)$. Therefore,
    ${ (U_x, f_x) } = { (U_i, f_i) } = C$.
]

#remark(title: "6.11.1")[
  - *(Regular Schemes).* A scheme $X$ is *regular* if each stalk
    $OO_(X, x)$ is a regular local ring.

  - Recall that a regular local ring is a UFD, whence _(6.11)_ also applies to
    any regular integral separated Noetherian scheme.
]

#remark(title: "6.11.2")[
  - $D in Div(X)$ is a *locally principal* Weil divisor if $X$ has an open
    cover ${U_i}$ such that each restriction $D|_(U_i) in Div(U_i)$ is
    principal.

  - If $X$ is a normal scheme, not necessarily locally factorial, then the
    proof in _(6.11)_ shows that the Cartier divisors are the same as locally
    principal Weil divisors. Thus, in this case, the map
    $CDiv(X) -> Div(X)$ is injective.
]
