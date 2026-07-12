#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *
#let notation(body) = note-box(title: "Notation", body)

== Sheaves of Modules

#definition(
  number: none,
  title: "Sheaves of Modules",
)[
  - Let $(X,OO_X)$ be a ringed space. A *sheaf of $OO_X$-modules* (or simply an *$OO_X$-module*) is a sheaf $FF$ on $X$, such that for each open set $U subset X$, the group $FF(U)$ is an $OO_X (U)$-module, and for each inclusion of open sets $V subset U$, the restriction homomorphism $FF(U)->FF(V)$ is compatible with the module structures via the ring homomorphism $OO_X (U)->OO_X (V)$.
  - A *morphism* $FF -> GG$ of sheaves of $OO_X$-module is a morphism of sheaves, such that for each open set $U subset X$, the map $FF(U) -> GG(U)$ is an $OO_X (U)$-module homomorphism.
]

#definition(
  number: none,
  title: "Associated Sheaf on Spec A",
)[
  \
  Fix a ring $A$ and a graded $A$-module $M$. We define the _sheaf associated_ to $M$ on $Spec A$, denoted by $tildeOf(M)$, as follows. For any open subset $U subset Spec A$, define

  $ tildeOf(M)(U):={s:U -> product.co_(pp in U)M_(pp) | s text("is locally a fraction") m/f med (m in M, f in A)}. $
  This make $tildeOf(M)$ into a sheaf with obvious restriction maps.

]

#proposition(number: 5.1)[
  Let $tildeOf(M)$ be the sheaf on $X=Spec A$ associated to $M in MOD(A)$. Then,

  #set enum(numbering: "a)", spacing: 1em)

  + $tildeOf(M)$ is an $OO_X$-module.
  + For each $pp in X$, we have $(tildeOf(M))_pp simeq M_pp$.
  + For any $f in A$, we have $tildeOf(M)(D(f)) simeq M_f$ as $A_f$-modules.
  + In particular, $Gamma(X, tildeOf(M))=M$.
]

#proposition(
  number: 5.2,
)[
  Given $A morph(phi, Ring) B$ and its corresponding morphism $Y=Spec B morph(f, Sch) Spec A=X$. Then,

  #set enum(numbering: "a)", spacing: 1em)

  + The map $M mapsto tildeOf(M)$ gives an exact, fully faithful functor $MOD(A) ->MOD(OO_X)$.
  + If $M,N in MOD(A)$, then $(tensor(M, N, A))^tilde simeq tensor(tildeOf(M), tildeOf(N), OO_X)$.
  + If $M_i in MOD(A) med (i in I)$, then $(bigOPlus(M_i, i in I))^tilde simeq bigOPlus(tildeOf(M_i), i in I)$.
  + For any $N in MOD(B)$, $f_ast (tildeOf(N)) simeq attach(tildeOf(N), bl: A)$ as $OO_X$-modules, where $N= attach(N, bl: A) in MOD(A)$.
  + For any $M in MOD(A)$, $f^ast (tildeOf(M)) simeq (tensor(M, B, A))^tilde$ as $OO_Y$-modules.
]

#proof[

  #set enum(numbering: "a)", spacing: 1em)

  + Proof
    - *(Exactness).* Given a short exact sequence $0 -> M' -> M -> M'' ->0$ of $A$-modules. Since localization is an exact functor, by _(5.1b)_, we have

    #align(center)[
      #diagram(
        cell-size: 15mm,
        $
          0 edge(->)
          & M'_pp edge(->) edge("d", simeq, ->)
          & M_pp edge(->) edge("d", simeq, ->)
          & M''_pp edge(->) edge("d", simeq, ->)
          & 0 \
          0 edge(->)
          & tildeOf(M)'_pp edge(->)
          & tildeOf(M)_pp edge(->)
          & tildeOf(M)''_pp edge(->)
          & 0
        $,
      )
    ]

    for every $pp in Spec A$. Therefore, _[1.2c]_ implies that the sequence $0 ->tildeOf(M)' -> tildeOf(M) ->tildeOf(M)'' ->0$ of $OO_X$-modules is exact.

    - *(Full Faithfulness).* We claim that $Hom(M, N, MOD(A)) simeq Hom(tildeOf(M), tildeOf(N), MOD(OO_X))$.
    Clearly, a homomorphism $M morph(tildeOf(phi), MOD(A)) N$ induces the morphism $tildeOf(M) morph(tildeOf(f), MOD(OO_X)) tildeOf(N)$. Conversely, if we have a morphism $tildeOf(M) morph(tildeOf(f), MOD(OO_X)) tildeOf(N)$, by definition with $U=X$, we have $tildeOf(f) :M= tildeOf(M)(X) morph(#none, MOD(A)) tildeOf(N)(X)=N$.

  + For each $pp in Spec A$, we have the isomorphisms
    $
      (tensor(M, N, A))^tilde_pp isoBy("(5.1b)")
      (tensor(M, N, A))_pp isoBy("AM")
      tensor(M_pp, N_pp, A_pp) isoBy("(5.1b)")
      tensor(tildeOf(M)_pp, tildeOf(N)_pp, OO_(X,pp)) isoBy("Def.")
      (tensor(M, N, A))^tilde_pp
    $
    as stalks. Thus, _(1.1)_ implies that $(tensor(M, N, A))^tilde simeq tensor(tildeOf(M), tildeOf(N), OO_X)$ as sheaves.

  + For each $pp in Spec A$, we have the isomorphisms

    $
      (bigOPlus(M_i, i in I))^tilde_pp
      attach(simeq, b: "(5.1b)")
      (bigOPlus(M_i, i in I))_pp
      simeq bigOPlus((M_i)_pp, i in I)
      \ attach(simeq, b: "(5.1b)")
      bigOPlus((tildeOf(M_i))_pp, i in I)
      attach(simeq, b: "Def.")
      (bigOPlus(tildeOf(M_i), i in I))_pp
    $

    as stalks. Thus, $(bigOPlus(M_i, i in I))^tilde simeq bigOPlus(tildeOf(M_i), i in I)$ as sheaves.

  + Note that $tildeOf(A) = OO_(Spec A) = OO_X$ for any ring $A$.
    Also, $tildeOf(dot)$ is a fully faithful functor by _(a)_, which gives the correspondence diagrams:

    #align(center)[
      #diagram(
        cell-size: 15mm,
        $
          A edge("d", phi, ->) edge("r", alpha, ->) & attach(N, bl: A) edge("d", tildeOf(phi), ->) \
                              B edge("r", beta, ->) & N
        $,
      )
      $quad$
      and
      $quad$
      #diagram(
        cell-size: 15mm,
        $
          OO_X edge("d", f^sharp, ->) edge("r", tildeOf(alpha), ->) & attach(tildeOf(N), bl: A) edge("d", tildeOf(f)^sharp, -->) \
                              f_* OO_Y edge("r", tildeOf(beta), ->) & f_* tildeOf(N)
        $,
      )
    ]

    where the action $alpha$ is defined by $(a,n) mapsto beta(phi(a), n) = phi(a) dot n$.

    Further, for each $qq in Spec B = Y$, diagram (i) induces the commutative diagram:

    #align(center)[
      #diagram(
        cell-size: 15mm,
        $
          A_(phi^(-1)(qq)) edge("r", ->) edge("d", phi_qq, ->) & attach(N, bl: A)_(phi^(-1)(qq)) edge("d", tilde(phi)_qq, ->) \
                                            B_qq edge("r", ->) & N_qq
        $,
      )
    ]

    Now, for every open set $U subset X$, define the sheaf map

    $
      tilde(f)^sharp_U : attach(tildeOf(N), bl: A)(U) -> f_* tildeOf(N)(U) = tildeOf(N)(f^(-1) U), quad
      s mapsto tilde(phi)_bullet compose s compose f.
    $

    This makes diagram (ii) commutative. For each $qq in Spec B$, the map
    $
      tilde(f)^sharp_qq :
      attach(tildeOf(N), bl: A)_(f(qq)) simeq attach(N, bl: A)_(phi^-1(qq))
      -> N_qq simeq (tildeOf(N))_qq
    $
    is a natural isomorphism of stalks. Hence, $tilde(f)^sharp$ gives an isomorphism $f_* (tildeOf(N)) simeq attach(tildeOf(N), bl: A)$ of $OO_X$-modules.

  + Note that $f^(-1) OO_X = coprod(OO_(X, f(y)), y in Y) in Shf(Y)$; and recall that
    $f^* FF = tensor(f^(-1) FF, OO_Y, f^(-1) OO_X)$ if $FF in MOD(OO_X)$.

    Now, for each $qq in Spec B = Y$, we see that

    $
      (f^* tildeOf(M))_qq eqBy("Def.")
      tensor(M_(phi^(-1)(qq)), B_qq, A_(phi^(-1)(qq)))
      simeq tensor((tensor(M_(phi^(-1)(qq)), A_(phi^(-1)(qq)), A)), B_qq, A_(phi^(-1)(qq))) \
      simeq tensor((tensor(M, B, A)), B_qq, B)
      simeq tensor(M, B_qq, A) \
      simeq (tensor(M, B, A))_qq
      isoBy("(5.1b)")
      (tensor(M, B, A))^tilde_qq
    $

    Therefore, $f^* tildeOf(M) simeq (tensor(M, B, A))^tilde$ as $OO_Y$-modules.
]

#definition(number: none)[
  Fix a scheme $(X, OO_X)$.

  + (Quasi-Coherent Sheaves) A *quasi-coherent sheaf* on $X$ is a sheaf
    $FF in MOD(OO_X)$ such that $X$ can be covered by open affine subsets
    $U_i = Spec A_i$ where for each $i$,
    $FF|_(U_i) simeq tildeOf(M)_i$ for some $M_i in MOD(A_i)$.

  + (Coherent Sheaves) A *coherent sheaf* on $X$ is a quasi-coherent sheaf
    on $X$ with the additional assumption that each $M_i in MOD(A_i)$
    is finitely generated.
]

#lemma(number: 5.3)[
  Let $FF$ be a quasi-coherent sheaf on $X = Spec A$ and let $f in A$.

  #set enum(numbering: "a)", spacing: 1em)

  + If the global section $s in Gamma(X, FF)$ satisfies
    $s|_(D(f)) = 0$ in $FF(D(f))$, then $f^n s = 0$ for some $n > 0$.

  + Given $t in FF(D(f))$, then $f^n t$ extends to a global section
    in $Gamma(X, FF)$ for some $n > 0$.
]

#proof[
  - Some settings:

    - Since $FF$ is quasi-coherent on $X$, cover $X$ by open affine subsets
      $V = Spec B$ such that $FF|_V simeq tildeOf(M)$ for some $M in MOD(B)$.

    - ${D(g)}_(g in A)$ forms a base for $TT_X$.
      Cover $V$ by some $D(g)$’s. Then the inclusion
      $Spec A_g = D(g) inclusion(#none, Sch) V = Spec B$ induces
      $B morph(#none, Ring) A_g$.
      By _(5.2e)_,
      $
        FF|_(D(g)) = i^* (FF|_V)
        isoBy("(5.2e)") i^* tildeOf(M)
        isoBy("Def.") tildeOf(M tensor(B, A_g, B)).
      $

    - Since $FF$ is quasi-coherent on $X$, $X$ can be covered by $D(g_i)$’s
      such that $FF|_(D(g_i)) simeq tildeOf(M)_i$ for some
      $M_i in MOD(A_(g_i))$.
      But $X = Spec A$ is quasi-compact, so we may choose finitely many $i$'s,
      say $1 lt.eq i lt.eq r$.

  - Proof of (a):
    For each $i$, set
    $s_i := s|_(D(g_i)) in FF(D(g_i)) = Gamma(D(g_i), tildeOf(M)_i) simeq M_i$.
    On the intersection $D(f) inter D(g_i) = D(f g_i)$, we have
    $
      s_i|_(D(f)) = s|_(D(f g_i)) = 0
      text("in") (FF|_(D(g_i)))(D(f))
      simeq tildeOf(M)_i(D(f))
      simeq (M_i)_f.
    $
    So $f^(n_i) s = 0$ in $M_i = FF(D(g_i))$ for some $n_i > 0$.
    Since there are only finitely many $i$'s, pick
    $n >= max{ n_i : 1 lt.eq i lt.eq r }$ such that $f^n s_i = 0$ for all $i$.
    As the $D(g_i)$’s cover $X$, we get $f^n s = 0$.

  - Proof of (b):
    - Let $t in FF(D(f))$. For each $i$, set
      $t_i := t|_(D(g_i)) in FF(D(f g_i)) simeq (M_i)_f$.
      By localization, there exists
      $tildeOf(t)_i in M_i simeq FF(D(g_i))$ such that
      $tildeOf(t)_i|_(D(f)) = f^(n_i) t_i$ on $D(f g_i)$ for some $n_i > 0$.
      Again, pick $n >= max{ n_i : 1 lt.eq i lt.eq r }$ such that
      $tildeOf(t)_i|_(D(f)) = f^n t_i$ for every $i$.

    - On $D(f) inter D(g_i g_j) = D(f g_i g_j)$, we have
      $
        tildeOf(t)_i|_(D(f g_i g_j))
        = f^n t_i|_(D(g_j))
        = f^n t|_(D(g_i g_j))
        = f^n t_j|_(D(g_i))
        = tildeOf(t)_j|_(D(f g_i g_j)).
      $

      Define $s_(i j) := (tildeOf(t)_i - tildeOf(t)_j)|_(D(g_i g_j))
      in FF(D(g_i g_j))$ with $s|_(D(f)) = 0$.
      By (a), there exists $m_(i j) > 0$ such that
      $f^(m_(i j)) s_(i j) = 0$ on $D(g_i g_j)$.
      Pick $m >= max{ m_(i j) : 1 lt.eq i,j lt.eq r }$ such that
      $f^m s_(i j) = 0$, i.e. $f^m tildeOf(t)_i = f^m tildeOf(t)_j$
      on $D(g_i g_j)$.

      Now glue the sections ${ f^m tildeOf(t)_i }_(i=1)^r$ on
      ${ D(g_i) }_(i=1)^r$, obtaining
      $s in FF(X)$ with $s|_(D(f)) = f^(n+m) t$.

      Indeed, on each $D(f g_i)$:
      $ s = f^m tildeOf(t)_i = f^(n+m) t_i = f^(n+m) t, $
      and on each $D(f g_i g_j)$:
      $ f^(n+m) t_i = f^m tildeOf(t)_i = f^m tildeOf(t)_j = f^(n+m) t_j. $
]

#proposition(
  number: 5.4,
)[
  Let $(X,OO_X)$ be a scheme. Then

  #set enum(numbering: "a)", spacing: 1em)

  + $FF in MOD(OO_X)$ is quasi-coherent $arrow.l.r.double.long$ For every open affine subset $U=Spec A subset X$, we have $FF|_U simeq tildeOf(M)$ for some $M in MOD(A)$.
  + If $X$ is Noetherian. Then $FF$ is coherent $arrow.l.r.double.long$ The same is true, with the extra condition that $M in MOD(A)$ is finitely generated.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)
  + $(Leftarrow)$. Clear. $(Rightarrow)$. Given an open affine subset $U=Spec A subset X$.

    - By _(5.3I)_, we may cover $X$ by $D(g_i)$ where $g_i in B_i$ such that $FF|_(D(g_i)) simeq tildeOf(M)_i$ for some $M_i in MOD((B_i)_(g_i))$. Since we may cover $U$ by some $D(g_i) subset U$, it follows that $FF_U$ is quasi-coherent. Thus, we may reduce to consider the affine case $X=Spec A$.
    - Consider $M := Gamma(X, FF)$. By _[5.3]_, there is a natural map $alpha: tildeOf(M) to FF$. Since $FF$ is quasi-coherent on $X=Spec A$, we may cover $X$ by $D(g_i) simeq Spec A_(g_i)$ such that $FF|_(D(g_i)) simeq tildeOf(M)_i$ for some $M_i in MOD(A_(g_i))$. Now,
    $
      M_i eqBy("(5.1d)") Gamma(D(g_i), tildeOf(M)_i) simeq Gamma(D(g_i), FF|_(D(g_i)))=FF(D(g_i)) isoBy("(5.3)") M_(g_i}).
    $
    Thus,
    $
      alpha_(D(g_i)): tildeOf(M)(D(g_i)) isoBy("(5.1c)") M_i morph(tilde, #none) M_(g_i) simeq FF(D(g_i))
    $
    is an isomorphism for each $i$, and hence, $alpha: tildeOf(M) morph(tilde, #none) FF$ is an isomorphism of $OO_X$-modules.

  + $(Leftarrow)$. Clear. $(Rightarrow)$. In addition to (i), $M_i=M_{g_i} in MOD(A_(g_i))$ is finitely generated for each $i$. Now, since $Spec A$ is Noetherian, $A$ is a Noetherian ring by _(3.2)_, whence so is $A_(g_i)$ for each $i$ by _(AM, 7.3)_. Further, $M_(g_i) in MOD(A_(g_i))$ is Noetherian for each $i$ by _(AM, 6.5)_, and thus, $M in MOD(A)$ is Noetherian as $A=(g_1,\cdots,g_n)$. Therefore, by _(AM, 6.2)_, $M in MOD(A)$ is finitely generated.

]

#remark[
  Note that being _finitely generated_ is actually a _local property_. Thus, there is no need to assume $X$ is Noetherian in (ii).
]

#corollary(
  number: 5.5,
)[
  Let $X=Spec A$.

  #set enum(numbering: "a)", spacing: 1em)

  + The functor $M mapsto tildeOf(M)$ gives an equivalence of categories between the category $MOD(A)$ of $A$-modules and the category $qcoh(X)$ of quasi-coherent $OO_X$-modules. Its inversre is the functor $Gamma(X, dot)$.

  + If $A$ is Noetherian, the same functor also gives an equivalence of categories between the category $fg(MOD(A))$ of finitely generated $A$-modules and the category $coh(X)$ of coherent $OO_X$-modules.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + We note that
    - For $M in MOD(A)$, we have $tildeOf(M) in qcoh(X)$ by _(5.1)_.
    - For $FF in qcoh(X)$, we have $Gamma(X, FF) in MOD(Gamma(X, OO_X)) = MOD(A)$ by definition.
    - By _(5.1d)_, we have
      $M mapsto.long tildeOf(M) mapsto.long Gamma(X, tildeOf(M)) = M$.
    - By _(5.4i)_, we have
      $FF mapsto.long Gamma(X, FF) mapsto.long Gamma(X, FF)^tilde
      attach(simeq, t: alpha) FF$.

  + Similarly.
]

#proposition(number: 5.6)[
  Let $X$ be an affine scheme, and let
  $0 -> FF' morph(phi, #none) FF morph(psi, #none) FF'' -> 0$
  be an exact sequence of $OO_X$-modules. If $FF' in qcoh(X)$, then
  the sequence
  $
    0 -> Gamma(X, FF') morph(phi_X, #none) Gamma(X, FF)
    morph(psi_X, #none) Gamma(X, FF'') -> 0
  $
  is exact.
]

#notation[
  - For each $k$, denote $U_k := D(f_k)$; for each $i$, similarly,
    $U_i := D(g_i)$. For intersections, set
    $U_(k i) := D(f_k g_i) = D(f_k) inter D(g_i)$, and similarly for
    $U_(i j)$ and $U_(i j k)$.
  - For any $FF in MOD(OO_X)$ and any section $s$, denote the restriction
    $s|_k := s|_(U_k) in FF(U_k)$, and define $s|_(k i)$, $s|_(i j)$,
    and $s|_(i j k)$ similarly.
  - For any morphism $FF morph(phi, MOD(OO_X)) GG$, denote by $phi_k$ the map
    $phi_(U_k): FF(U_k) -> GG(U_k)$, and define $phi_(k i)$, $phi_(i j)$,
    and $phi_(i j k)$ similarly.
]

#proof[
  From _[1.8]_, $Gamma(X, dot)$ is a left exact functor, so it suffices to
  show that $psi_X$ is surjective. Given $s'' in FF''(X)$, since $psi$ is
  surjective, by _[1.3a]_ there exists an open cover ${D(f_k)}$ for $X$ and,
  for each $k$, a section $t_k in FF(U_k)$ such that
  $s''|_k = psi_k(t_k)$. Since $X$ is affine, hence quasi-compact, choose
  finitely many $k$'s, say $1 lt.eq k lt.eq r$.

  *Step I.* For each $k$, there are $n_k > 0$ and
  $hat(t)_k in FF(X)$ such that $psi_X(hat(t)_k) = f_k^(n_k) s''$ in
  $FF''(X)$.

  #set enum(numbering: "i)", spacing: 1em)

  + As $X$ is affine, choose a finite open affine cover ${D(g_i)}_(i=1)^p$
    for $X$ such that $s''|_i = psi_i(t_i)$ for some $t_i in FF(U_i)$.

  + On $U_(k i) = U_k inter U_i$, we have $psi_(i k) = psi_(k i)$, so
    $
      psi_(i k)(t_k|_i) = psi_(k i)(t_k|_i)
      = psi_k(t_k)|_i = s''|_(k i) = s''|_(i k)
      = psi_i(t_i)|_k = psi_(i k)(t_i|_k).
    $
    Hence $t_k|_i - t_i|_k in Ker psi_(i k) = Im phi_(i k)$. By exactness,
    $phi_(i k)(s'_(i k)) = t_k|_i - t_i|_k$ for some
    $s'_(i k) in FF'(U_(i k))$.

  + Since $FF' in qcoh(X)$, by _(5.3b)_ we have
    $f_k^(n_i) s'_(i k) in FF'(U_i)$ for some $n_i > 0$. Take
    $n >= max{ n_i }_(i=1)^p$ such that $f_k^n s'_(i k) in FF'(U_i)$ for
    all $i$. Set
    $u_i := phi_i(f_k^n s'_(i k)) in FF(U_i)$ and
    $tilde(t)_i := f_k^n t_i + u_i in FF(U_i)$. Then
    $
      psi_i(tilde(t)_i)
      = f_k^n psi_i(t_i) + psi_i phi_i(f_k^n s'_(i k))
      = f_k^n s''|_i.
    $

  + For each $i,j$, on $U_(i j)$ we have
    $
      psi_(i j)(tilde(t)_i|_j)
      = psi_i(tilde(t)_i)|_j
      = f_k^n s''|_(i j)
      = f_k^n s''|_(j i)
      = psi_j(tilde(t)_j)|_i
      = psi_(i j)(tilde(t)_j|_i).
    $
    Thus $tilde(t)_i|_j - tilde(t)_j|_i in Ker psi_(i j) = Im phi_(i j)$.
    By exactness, choose $tilde(s)'_(i j) in FF'(U_(i j))$ with
    $phi_(i j)(tilde(s)'_(i j)) = tilde(t)_i|_j - tilde(t)_j|_i$.

  + Note that on $U_(i k)$,
    $
      tilde(t)_i|_k
      = f_k^n t_i|_k + u_i|_k
      = f_k^n t_i|_k + phi_(i k)(f_k^n s'_(i k))
      = f_k^n (t_i|_k + phi_(i k)(s'_(i k)))
      eqBy("(ii)") f_k^n t_k|_i.
    $
    Restricting to $U_(i j k)$ gives
    $
      phi_(i j k)(tilde(s)'_(i j)|_k)
      = phi_(i j)(tilde(s)'_(i j))|_k
      = tilde(t)_i|_(j k) - tilde(t)_j|_(i k)
      = f_k^n t_k|_(i j) - f_k^n t_k|_(j i)
      = 0.
    $
    Since $phi_(i j k)$ is injective, $tilde(s)'_(i j)|_k = 0$ on
    $U_(i j) inter U_k$. Since $FF' in qcoh(X)$, by _(5.3a)_ there is
    $m_(i j) > 0$ such that $f_k^(m_(i j)) tilde(s)'_(i j) = 0$ in
    $FF'(U_(i j))$. Choose
    $m >= max{ m_(i j) : 1 lt.eq i,j lt.eq p }$. Then
    $
      f_k^m (tilde(t)_i|_j - tilde(t)_j|_i)
      = phi_(i j)(f_k^m tilde(s)'_(i j)) = 0,
    $
    so $f_k^m tilde(t)_i|_j = f_k^m tilde(t)_j|_i$ in $FF(U_(i j))$.
    Glue the sections ${f_k^m tilde(t)_i}_(i=1)^p$ on ${U_i}_(i=1)^p$ to
    obtain $hat(t)_k in FF(X)$.

  + For each $i$,
    $
      psi_X(hat(t)_k)|_i
      = psi_i(hat(t)_k|_i)
      = psi_i(f_k^m tilde(t)_i)
      = f_k^m psi_i(tilde(t)_i)
      eqBy("(iii)") f_k^(m+n) s''|_i.
    $
    Hence $psi_X(hat(t)_k) = f_k^(m+n) s''$ on $X$. This $m+n$ is the
    required $n_k$.

  *Step II.* Since there are finitely many $k$'s, choose
  $N >= max{ n_k }_(k=1)^r$ such that
  $psi_X(hat(t)_k) = f_k^N s''$ for all $k$. Further,
  $X = union_(k=1)^r D(f_k) = union_(k=1)^r D(f_k^N)$, so
  $lr(chevron.l f_1^N, dots.c, f_r^N chevron.r) = A$. Thus
  $1 = sum_(k=1)^r a_k f_k^N$ for some $a_k in A$. Set
  $t := sum_(k=1)^r a_k hat(t)_k in FF(X)$. Then
  $
    psi_X(t)
    = sum_(k=1)^r a_k psi_X(hat(t)_k)
    = sum_(k=1)^r a_k f_k^N s''
    = s''.
  $
]

#proposition(number: 5.7)[
  Let $X$ be a scheme.

  #set enum(numbering: "i)", spacing: 1em)

  + The kernel, cokernel, and image of any morphism
    $FF morph(phi, qcoh(X)) GG$ are quasi-coherent.
  + Any extension of quasi-coherent sheaves is quasi-coherent.
  + If $X$ is Noetherian, then (i) and (ii) are true for coherent sheaves.
]

#proof[
  The question is local, so assume $X = Spec A$ is affine.

  #set enum(numbering: "i)", spacing: 1em)

  + By _(5.5)_, $FF = tildeOf(M)$ and $GG = tildeOf(N)$ for some
    $M,N in MOD(A)$. By _(5.2)_, the functor $M mapsto tildeOf(M)$ is exact
    and fully faithful, so $phi$ corresponds to a homomorphism
    $M morph(alpha, MOD(A)) N$. Since
    $0 -> Ker alpha -> M morph(alpha, #none) Im alpha -> 0$ is exact, the
    sequence
    $
      0 -> tildeOf(Ker alpha) -> tildeOf(M) morph(phi, #none)
      tildeOf(Im alpha) -> 0
    $
    is exact, with $tildeOf(Ker alpha) simeq Ker phi$ and
    $tildeOf(Im alpha) simeq Im phi$. Similarly,
    $Coker phi simeq tildeOf(Coker alpha)$. Therefore these sheaves are
    quasi-coherent.

  + *Claim.* If $0 -> FF' -> FF -> FF'' -> 0$ is exact and
    $FF', FF'' in qcoh(X)$, then $FF in qcoh(X)$.

    By _(5.6)_,
    $
      0 -> Gamma(X, FF') -> Gamma(X, FF) -> Gamma(X, FF'') -> 0
    $
    is exact. Write these modules as $M'$, $M$, and $M''$. Applying the exact
    functor $M mapsto tildeOf(M)$ gives the commutative diagram

    #align(center)[
      #diagram(
        cell-size: 15mm,
        $
          0 edge(->)
          & tildeOf(M') edge(->) edge("d", theta', ->)
          & tildeOf(M) edge(->) edge("d", theta, ->)
          & tildeOf(M'') edge(->) edge("d", theta'', ->)
          & 0 \
          0 edge(->)
          & FF' edge(->)
          & FF edge(->)
          & FF'' edge(->)
          & 0
        $,
      )
    ]

    with exact rows. Since $FF', FF'' in qcoh(X)$, the maps $theta'$ and
    $theta''$ are isomorphisms. By the Five Lemma, $theta$ is an isomorphism.
    Thus $FF simeq tildeOf(M) in qcoh(X)$.

  + If $X$ is Noetherian and $FF', FF'' in coh(X)$, then by _(5.5)_,
    $M', M'' in fg(MOD(A))$. Since $0 -> M' -> M -> M'' -> 0$ is exact,
    $M$ is finitely generated, whence $FF = tildeOf(M) in coh(X)$.
]

#proposition(number: 5.8)[
  Let $f: X -> Y$ be a scheme morphism.

  #set enum(numbering: "a)", spacing: 1em)

  + If $GG in qcoh(Y)$, then $f^ast GG in qcoh(X)$.
  + If $X$ and $Y$ are Noetherian, and $GG in coh(Y)$, then
    $f^ast GG in coh(X)$.
  + Assume that either (i) $X$ is Noetherian, or (ii) $f$ is quasi-compact
    and separated. If $FF in qcoh(X)$, then $f_ast FF in qcoh(Y)$.
]

#proof[
  For (a) and (b), the questions are local, so assume
  $X = Spec A morph(f, Sch) Spec B = Y$ is induced by
  $B morph(phi, Ring) A$.

  #set enum(numbering: "a)", spacing: 1em)

  + If $GG in qcoh(Y)$, then by _(5.5)_ $GG = tildeOf(N)$ for some
    $N in MOD(B)$. Hence
    $
      f^ast GG = f^ast tildeOf(N)
      isoBy("(5.2e)") (tensor(N, A, B))^tilde in qcoh(X),
    $
    since $tensor(N, A, B) in MOD(A)$.

  + If $X,Y$ are Noetherian and $GG in coh(Y)$, then in addition to (a) we
    have $N in fg(MOD(B))$. There is an $n > 0$ and a surjection
    $B^n -> N$. Since $- tensor_B A$ is right
    exact,
    $A^n simeq tensor(B^n, A, B) ->
    tensor(N, A, B)$, so $tensor(N, A, B) in fg(MOD(A))$. Thus
    $f^ast GG simeq (tensor(N, A, B))^tilde in coh(X)$ by _(5.5)_.

  + This question is local on $Y$ only.

    - If $V subset Y$ is open affine, then $(f_ast FF)|_V$ depends on the
      restriction of $FF$ to $f^(-1)(V) subset X$. Replacing $Y$ and $X$ by
      $V$ and $f^(-1)(V)$, assume $Y := Spec B$ is affine.
    - In both cases (i) and (ii), $X$ is quasi-compact, so cover $X$ by
      finitely many open affines $U_i$ with $1 lt.eq i lt.eq r$.
    - *Case (ii).* Since $f$ is separated, by _[4.3]_ each
      $U_i inter U_j$ is affine. Denote it by $U_(i j k) := U_i inter U_j$,
      here with $k = 1$.
    - *Case (i).* Since $X$ is Noetherian, each $U_i inter U_j$ is
      quasi-compact. Cover each $U_i inter U_j$ by finitely many open affines
      $U_(i j k)$.
    - *Claim.* If $FF in qcoh(X)$, then $f_ast FF in qcoh(Y)$.

      By the sheaf property, if $V subset Y$ is open, giving
      $s in FF(f^(-1) V)$ is the same as giving sections
      $s_i in FF(f^(-1) V inter U_i)$ whose restrictions agree on
      $f^(-1) V inter U_(i j k)$. Thus we have an exact sequence of
      $OO_Y$-modules
      $
        0 -> f_ast FF -> bigOPlus(f_ast(FF|_(U_i)), i=1, top: r)
        morph(psi, #none) bigOPlus(f_ast(FF|_(U_(i j k))), (i,j,k)).
      $
      Since $FF in qcoh(X)$,
      $
        bigOPlus(f_ast(FF|_(U_i)), i=1, top: r)
        isoBy("Def.") bigOPlus(f_ast(tildeOf(M)_i), i=1, top: r)
        isoBy("(5.2d)") bigOPlus(attach(tildeOf(M)_i, bl: B), i=1, top: r)
        isoBy("(5.2c)") (bigOPlus(attach(M_i, bl: B), i=1, top: r))^tilde
        in qcoh(Y)
      $
      for some $M_i in MOD(A_i)$. Similarly,
      $bigOPlus(f_ast(FF|_(U_(i j k))), (i,j,k)) in qcoh(Y)$. Hence $psi$ is a
      morphism of quasi-coherent sheaves on $Y$, so
      $f_ast FF = Ker psi in qcoh(Y)$ by _(5.7a)_.
]

#definition(
  number: none,
  title: "Ideal Sheaf",
)[
  Let $Y$ be a closed subscheme of $X$ and let $i: Y -> X$ be the inclusion
  morphism. The *ideal sheaf* of $Y$ is
  $II_Y := Ker i^sharp = Ker(OO_X -> i_ast OO_Y)$.
]

#proposition(number: 5.9)[
  Let $X$ be a scheme.

  #set enum(numbering: "i)", spacing: 1em)

  + For any closed subscheme $Y$ of $X$, the ideal sheaf $II_Y$ is a
    quasi-coherent sheaf of ideals on $X$.
  + In addition to (i), if $X$ is Noetherian, then $II_Y$ is coherent.
  + Conversely, if $JJ$ is a quasi-coherent sheaf of ideals on $X$, then
    $JJ = II_Y$ is the ideal sheaf of a uniquely determined closed subscheme
    $Y$ of $X$.
]

#proof[
  #set enum(numbering: "i)", spacing: 1em)

  + The inclusion morphism $i: Y -> X$ is quasi-compact and separated by
    _(4.6a)_ because $i$ is a closed immersion. Since $Y$ is a scheme,
    $OO_Y in qcoh(Y)$, so by _(5.8c)_ $i_ast OO_Y in qcoh(X)$. Hence
    $i^sharp: OO_X -> i_ast OO_Y$ is a morphism in $qcoh(X)$. By _(5.7i)_,
    $II_Y = Ker i^sharp in qcoh(X)$.

  + If $X$ is Noetherian, then for any open affine subset
    $U = Spec A subset X$, the ring $A$ is Noetherian. Thus the ideal
    $I := Gamma(U, II_Y|_U) lt.closed Gamma(U, OO_X|_U) = A$ is finitely
    generated. By _(5.5)_,
    $tildeOf(I) = (Gamma(U, II_Y|_U))^tilde = II_Y|_U$. Thus
    $II_Y in coh(X)$.

  + Given $JJ in qcoh(X)$ with $JJ lt.closed OO_X$, consider
    $Y := Supp(OO_X / JJ)$. We claim that $(Y, OO_X / JJ)$ is the unique
    closed subscheme of $X$ with ideal sheaf $JJ$. Uniqueness is clear.
    The question is local, so assume $X = Spec A$ is affine. Since
    $JJ in qcoh(X)$, $JJ = tildeOf(aa)$ for some ideal $aa lt.closed A$.
    Then
    $
      Y = Supp(OO_X / JJ)
      eqBy("Def.") { P in X : (OO_X / JJ)_P != 0 }
      eqBy("(5.1b)") { pp in X : (A / aa)_pp != 0 }
      = Spec(A / aa) isoBy("homeom.") V(aa).
    $
    Thus $(Y, OO_X / JJ)$ is the closed subscheme of $X$ determined by $aa$
    (cf. _3.2.3_).
]

#corollary(number: 5.10)[
  If $X = Spec A$ is an affine scheme, then:

  #set enum(numbering: "i)", spacing: 1em)

  + There is a 1-1 correspondence between ideals $aa lt.closed A$ and closed
    subschemes $Y subset X$, given by $aa mapsto$ the image of
    $Spec(A / aa)$ in $X$.
  + In particular, every closed subscheme of an affine scheme is affine.
]

#proof[
  By _(5.5)_, the quasi-coherent sheaves of ideals on $X = Spec A$ are in
  one-to-one correspondence with the ideals of $A$.
]

#definition(title: "Associated Sheaf on Proj S")[
  Fix a graded ring $S$ and a graded $S$-module $M$. We define the _sheaf
  associated_ to $M$ on $Proj S$, denoted by $tildeOf(M)$, as follows. For any
  open subset $U subset Proj S$, define
  $
    tildeOf(M)(U) :=
    { s: U -> coprod(M_((pp)), pp in U) |
      s text(" is locally a fraction ") m/f med (m in M, f in A) }.
  $
  This makes $tildeOf(M)$ into a sheaf with obvious restriction maps.
]

#proposition(number: 5.11)[
  Fix a graded ring $S$ and a graded $S$-module $M$. Let $X = Proj S$. Then:

  #set enum(numbering: "a)", spacing: 1em)

  + For any $pp in X$, the stalk $(tildeOf(M))_pp = M_((pp))$.
  + For any homogeneous $f in S_+$,
    $tildeOf(M)|_(D_+(f)) simeq tildeOf(M_((f)))$ via
    $D_+(f) simeq Spec S_((f))$.
  + $tildeOf(M) in qcoh(X)$. If $S$ is Noetherian and $M$ is finitely
    generated, then $tildeOf(M) in coh(X)$.
]

#proposition(number: "5.A")[
  Fix a graded ring $S$ generated by $S_1$ as an $S_0$-algebra, and let
  $X = Proj S$.

  #set enum(numbering: "a)", spacing: 1em)

  + For any $M,N in GR MOD(S)$ and $f in S_1$,
    $(tensor(M, N, S))_((f)) simeq tensor(M_((f)), N_((f)), S_((f)))$.
  + Continuing (a),
    $(tensor(M, N, S))^tilde simeq tensor(tildeOf(M), tildeOf(N), OO_X)$.

  Let $T$ be another graded ring, generated by $T_1$ as a $T_0$-algebra. Let
  $phi: S -> T$ be a graded homomorphism, let $U subset Y = Proj T$, and let
  $f: U -> X$ be determined by $phi$ as in _[2.14]_.

  + For any $M in GR MOD(S)$,
    $f^ast tildeOf(M) simeq (tensor(M, T, S))^tilde|_U$ as $OO_Y$-modules.
  + For any $N in GR MOD(T)$,
    $f_ast(tildeOf(N)|_U) simeq (attach(N, bl: S))^tilde$ as $OO_X$-modules.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + Note that $tensor(M, N, S)$ is a graded $S$-module by
    $(tensor(M, N, S))_d = bigOPlus(tensor(M_(d_1), N_(d_2), S), d_1+d_2=d)$.
    Fix $f in S_1$. The canonical inclusions
    $S_((f)) -> S_f$, $M_((f)) -> M_f$, and $N_((f)) -> N_f$ induce a
    homomorphism
    $tensor(M_((f)), N_((f)), S_((f))) -> tensor(M_f, N_f, S_f)$. The
    canonical isomorphism
    $tensor(M_f, N_f, S_f) -> (tensor(M, N, S))_f$ preserves degrees, yielding
    a map
    $
      phi_f: tensor(M_((f)), N_((f)), S_((f))) ->
      (tensor(M, N, S))_((f)), quad
      m/f^(d_1) times.o n/f^(d_2) mapsto.long (m times.o n)/f^(d_1+d_2)
    $
    for $m in M_(d_1)$ and $n in N_(d_2)$. It remains to show that $phi_f$ is
    an isomorphism.

    - *Surjectivity.* If $(m times.o n)/f^d in (tensor(M, N, S))_((f))$,
      then $deg(m times.o n) = d$, say
      $m times.o n in tensor(M_(d_1), N_(d_2), S)$ with $d_1 + d_2 = d$.
      Then $m/f^(d_1) times.o n/f^(d_2)$ maps to $(m times.o n)/f^d$.
    - *Injectivity.* Suppose $m/f^(d_1) times.o n/f^(d_2)$ maps to $0$.
      Then $f^r (m times.o n) = 0$ in $tensor(M, N, S)$ for some $r > 0$.
      Viewing $S_((f))$ as an $S$-algebra via
      $s in S_d mapsto s/f^d$, we get a canonical homomorphism
      $psi_f: tensor(M, N, S) -> tensor(M_((f)), N_((f)), S_((f)))$. Hence
      $
        m/f^(d_1) times.o n/f^(d_2)
        = (f^r m)/f^(r+d_1) times.o n/f^(d_2)
        = psi_f(f^r m times.o n)
        = 0,
      $
      so $phi_f$ is injective.

  + By _(2.5b)_, $D_+(f) simeq Spec S_((f))$ is affine. It suffices to show
    the desired isomorphism on every $D_+(f)$ with $f in S_+$. Since $S_1$
    generates $S_+$ over $S_0$, it is enough to check $f in S_1$:
    $
      (tensor(M, N, S))^tilde|_(D_+(f))
      isoBy("(5.11b)") ((tensor(M, N, S))_((f)))^tilde
      isoBy("(a)") (tensor(M_((f)), N_((f)), S_((f))))^tilde
      isoBy("(5.2b)") tensor(tildeOf(M_((f))), tildeOf(N_((f))), tildeOf(S_((f))))
      isoBy("(5.11b)") tensor(tildeOf(M)|_(D_+(f)), tildeOf(N)|_(D_+(f)), OO_X|_(D_+(f))).
    $

  + The sets ${D_+(g): g in phi(S_+)}$ form an open affine cover of $U$, and
    $D_+(g) simeq Spec T_((g))$ is affine. For $g := phi(h)$,
    $
      (tensor(M, T, S))^tilde|_(D_+(g))
      isoBy("(5.11b)") ((tensor(M, T, S))_((g)))^tilde
      simeq (tensor(M_((h)), T_((g)), S_((h))))^tilde
      isoBy("(5.2e)") f^ast(tildeOf(M_((h))))
      isoBy("(5.11b)") f^ast(tildeOf(M)|_(D_+(h))).
    $

  + Similarly, for every $h in S_+$,
    $
      f_ast(tildeOf(N)|_U)|_(D_+(h))
      = f_ast(tildeOf(N)|_(D_+(phi(h))))
      isoBy("(5.11b)") f_ast(tildeOf(N_((phi(h)))))
      isoBy("(5.2d)") (attach(N_((phi(h))), bl: S_((h))))^tilde
      = ((attach(N, bl: S))_((h)))^tilde
      isoBy("(5.11b)") (attach(N, bl: S))^tilde|_(D_+(h)).
    $
]

#definition(title: "Twisted Sheaf")[
  Fix a graded ring $S$ and let $X = Proj S$. Suppose $n in ZZ$.

  - The sheaf $OO_X(n) := tildeOf(S(n))$, where
    $S(n) := bigOPlus(S_d, d >= n)$, is called the *twisting sheaf of Serre*
    when $n = 1$.
  - For any $FF in MOD(OO_X)$, denote
    $FF(n) := tensor(FF, OO_X(n), OO_X)$.
]

#proposition(number: 5.12)[
  Fix a graded ring $S$ generated by $S_1$ as an $S_0$-algebra, and let
  $X = Proj S$.

  #set enum(numbering: "a)", spacing: 1em)

  + The sheaf $OO_X(n)$ is an invertible sheaf on $X$ for every
    $n in ZZ$.
  + For any $M in GR MOD(S)$, $tildeOf(M)(n) simeq tildeOf(M(n))$. Further,
    $tensor(OO_X(n), OO_X(m), OO_X) simeq OO_X(n+m)$.
  + Let $T$, $phi$, and $f$ be as in _(5.A)_. Then
    $f^ast(OO_X(n)) simeq OO_Y(n)|_U$ and
    $f_ast(OO_Y(n)|_U) simeq (f_ast(OO_Y|_U))(n)$.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + The sets ${D_+(f): f in S_1}$ cover $X$. Given $f in S_1$,
    $
      OO_X(n)|_(D_+(f))
      = tildeOf(S(n))|_(D_+(f))
      = tildeOf(S(n)_((f))).
    $
    The module $S(n)_((f))$ is free of rank $1$ over $S_((f))$, with canonical
    isomorphism
    $
      S_((f)) isolongto S(n)_((f)), quad
      a/f^d mapsto.long f^(n-d) a in S_(n-d) dot S_d subset S_n = S(n)_0.
    $
    Hence $OO_X(n)|_(D_+(f)) simeq tildeOf(S_((f))) simeq OO_X|_(D_+(f))$ is
    free of rank $1$, so $OO_X(n)$ is locally free of rank $1$, i.e. invertible.

  + For the first isomorphism,
    $
      tildeOf(M)(n)
      eqBy("Def.") tensor(tildeOf(M), OO_X(n), OO_X)
      = tensor(tildeOf(M), tildeOf(S(n)), tildeOf(S))
      isoBy("(5.Ab)") (tensor(M, S(n), S))^tilde
      simeq tildeOf(M(n)).
    $
    For the second,
    $
      tensor(OO_X(n), OO_X(m), OO_X) & simeq tensor(tildeOf(S(n)), tildeOf(S(m)), tildeOf(S))
                                       isoBy("(5.Ab)") (tensor(S(n), S(m), S))^tilde
                                       = tildeOf(S(n+m)) \
                                     & = OO_X(n+m).
    $

  + First,
    $
      f^ast(OO_X(n))
      = f^ast(tildeOf(S(n)))
      isoBy("(5.Ac)") (tensor(S(n), T, S))^tilde|_U
      = tildeOf(T(n))|_U
      eqBy("(b)") OO_Y(n)|_U.
    $
    Also,
    $
      f_ast(OO_Y(n)|_U) & = f_ast(tildeOf(T(n))|_U)
                          isoBy("(5.Ad)") (attach(T(n), bl: S))^tilde
                          eqBy("(b)") tildeOf(attach(T, bl: S))(n)
                          isoBy("(5.Ad)") (f_ast(tildeOf(T)|_U))(n) \
                        & = (f_ast(OO_Y|_U))(n).
    $
]

#proposition(
  number: "5.B",
  // number: 5.B
)[
  The twisting functor $FF mapsto FF(n)$ is exact on $MOD(OO_X)$ for every
  $n in ZZ$, where $X = Proj S$ and $S$ is generated by $S_1$ as an
  $S_0$-algebra.
]

#proof[
  Fix $n in ZZ$. Suppose $0 -> FF' -> FF -> FF'' -> 0$ is a short exact
  sequence of $OO_X$-modules. We show that
  $0 -> FF'(n) -> FF(n) -> FF''(n) -> 0$ is exact.

  - For each $P in X$, the sequence $0 -> FF'_P -> FF_P -> FF''_P -> 0$ of
    stalks is exact. Since
    $- tensor_(OO_(X,P)) OO_X(n)_P$ is right exact, we get the exact
    sequence $FF'(n)_P -> FF(n)_P -> FF''(n)_P -> 0$. Thus
    $FF'(n) -> FF(n) -> FF''(n) -> 0$ is exact.
  - It remains to show $FF'(n) -> FF(n)$ is injective. For each $f in S_1$,
    $OO_X(n)|_(D_+(f)) simeq OO_X|_(D_+(f))$ is free by _(5.12a)_, so
    $OO_X(n)(D_+(f))$ is a flat $OO_X(D_+(f))$-module. Hence
    $
      FF'(n)(D_+(f)) simeq tensor(FF', OO_X(D_+(f)), OO_X)
      -> tensor(FF, OO_X(D_+(f)), OO_X) simeq FF(n)(D_+(f))
    $
    is injective as a presheaf map, hence as a sheaf map by _[1.4a]_. Since
    the $f in S_1$ generate $S$ over $S_0$, this gives the injection
    $FF'(n) -> FF(n)$.
]

#remark[
  The twisting operation above allows us to define a graded $OO_X$-module on
  $X = Proj S$.
]

#definition(number: none)[
  Fix a graded ring $S$, let $X = Proj S$, and let $FF in MOD(OO_X)$. We define
  the _graded $S$-module associated_ to $FF$ as the group
  $Gamma_ast (FF) := bigOPlus(Gamma(X, FF(n)), n in ZZ)$. It has a graded
  $S$-module structure as follows. If $s in S_d$, then $s$ determines a global
  section $s in Gamma(X, OO_X(d))$. For $t in Gamma(X, FF(n))$, define
  $s dot t in Gamma(X, FF(n+d))$ by taking the tensor product
  $s times.o t$ via the natural isomorphism
  $tensor(FF(n), OO_X(d), OO_X) simeq FF(n+d)$.
]

#proposition(number: 5.13)[
  Suppose $S = A[x_0, dots.c, x_r]$ with $r >= 1$, and let
  $X = Proj S = PP_A^r$. Then $Gamma_ast (OO_X) simeq S$.
]

#proof[
  - Cover $X$ by ${D_+(x_i)}_(i=0)^r$. By the sheaf property, giving
    $t in Gamma(X, OO_X(n))$ is equivalent to giving
    $t_i in Gamma(D_+(x_i), OO_X(n))$ such that
    $t_i|_(D_+(x_i x_j)) = t_j|_(D_+(x_i x_j))$ for every $i,j$.
  - If $f in S_d$ with $d > 0$, then
    $S(n d)_((f)) = (S(n d)_f)_0 = (S_f(n))_0 = (S_f)_(n d)$. In particular,
    $S(n)_((x_i)) = (S_(x_i))_n$. Hence
    $OO_X(n)|_(D_+(x_i)) = tildeOf(S(n))|_(D_+(x_i))
    = tildeOf(S(n)_((x_i))) = tildeOf((S_(x_i))_n)$, and
    $
      t_i in Gamma(D_+(x_i), OO_X(n))
      = Gamma(Spec S_((x_i)), tildeOf((S_(x_i))_n))
      eqBy("(5.1d)") (S_(x_i))_n subset S_(x_i).
    $
    Similarly, $t_i|_j in (S_(x_i x_j))_n subset S_(x_i x_j)$.
  - Summing over all $n in ZZ$,
    $
      Gamma_ast (OO_X) & = bigOPlus(Gamma(X, OO_X(n)), n in ZZ) \
                       & = { (t_0, dots.c, t_r) : t_i in S_(x_i) text(" with ")
                           t_i|_j = t_j|_i text(" for every ") i,j }.
    $
  - Since each $x_i$ is not a zero divisor of $S = A[x_0, dots.c, x_r]$, the
    localization maps
    $S -> S_(x_i)$ and $S_(x_i) -> S_(x_i x_j)$ are injective. Thus all these
    rings are subrings of $S' := S_(x_0 dots.c x_r)$, and
    $Gamma_ast (OO_X) = inter_(i=0)^r S_(x_i) subset S'$.
  - Every homogeneous element $g in S'$ can be written as
    $g := x_0^(d_0) dots.c x_r^(d_r) f(x_0, dots.c, x_r)$ for some
    $d_k in ZZ$ and $f in S^h$ with $x_k divides.not f$ for every $k$.
    Then $g in S_(x_i)$ iff $d_k >= 0$ for every $k != i$. Therefore
    $
      g in Gamma_ast (OO_X) & arrow.l.r.double.long g in S_(x_i) text(" for all ") 0 lt.eq i lt.eq r \
                            & arrow.l.r.double.long d_i >= 0 text(" for all ") 0 lt.eq i lt.eq r \
                            & arrow.l.r.double.long g in S.
    $
    Hence $Gamma_ast (OO_X) simeq S$.
]

#lemma(number: 5.14)[
  Fix a scheme $X$, let $LL$ be an invertible sheaf on $X$, let
  $f in Gamma(X, LL)$, let
  $X_f = { x in X : f_x in.not mm_x LL_x }$, and let $FF in qcoh(X)$.

  #set enum(numbering: "a)", spacing: 1em)

  + Suppose $X$ is quasi-compact and $s in Gamma(X, FF)$ has
    $s|_(X_f) = 0$. Then $f^n s = 0$ in
    $Gamma(X, tensor(FF, LL^(times.o n), OO_X))$ for some $n > 0$.
  + Suppose further that $X$ has a finite open affine cover $U_i$ such that
    $LL|_(U_i)$ is free for each $i$ and $U_i inter U_j$ is quasi-compact for
    every $i,j$. Given $t in Gamma(X_f, FF)$, then $f^n t$ extends to a global
    section $s in Gamma(X, tensor(FF, LL^(times.o n), OO_X))$ for some
    $n > 0$.
]

#proof[
  - General settings:

    - Choose a finite open affine cover $U_i = Spec A_i$,
      $1 lt.eq i lt.eq r$, of $X$ such that each $LL|_(U_i)$ is free.
    - Since $LL$ is invertible, let
      $psi_i: LL|_(U_i) isoBy(MOD(OO_X)) OO_X|_(U_i) = OO_(U_i)$.
    - Since $FF in qcoh(X)$, by _(5.4)_ we have
      $FF|_(U_i) simeq tildeOf(M)_i$ for some $M_i in MOD(A_i)$.
    - For each $i$, let
      $g_i := psi_(i,U_i)(f|_i) in Gamma(U_i, OO_(U_i)) = A_i$. Then
      $U_i inter X_f = D(g_i)$ by _[2.16a]_.

  - Proof of (a): For each $i$, consider
    $s|_i in Gamma(U_i, FF) = Gamma(Spec A_i, tildeOf(M)_i) = M_i$. Since
    $(s|_i)|_(X_f) = 0$ on $D(g_i)$, by _(5.3a)_ there is $n_i > 0$ such
    that $g_i^(n_i) s|_i = 0$ in $FF(U_i) = M_i$. Via the isomorphism
    $FF times.o LL^(times.o n)|_(U_i) simeq FF|_(U_i)$ induced by $psi_i$,
    this gives $(f^(n_i) s)|_i = 0$. Choose
    $n >= max{ n_i : 1 lt.eq i lt.eq r }$, so $f^n s = 0$ on $X$.

  - Proof of (b):

    - For each $i$, let $t|_i in FF(X_f inter U_i) = FF(D(g_i)) simeq
      (M_i)_(g_i)$. By localization, there is
      $tilde(t)_i in M_i = FF(U_i)$ such that
      $tilde(t)_i|_(X_f) = g_i^(n_i) t|_i$ for some $n_i > 0$. Choose
      $n >= max{ n_i : 1 lt.eq i lt.eq r }$; under the trivialization by
      $psi_i$, this says
      $tilde(t)_i|_(X_f) = psi_i(f^n|_i) dot t|_i$.
    - On $D(g_i g_j) = (U_i inter U_j) inter X_f$, the two sections
      $tilde(t)_i$ and $tilde(t)_j$ have the same restriction. Thus
      $s_(i j) := tilde(t)_i|_j - tilde(t)_j|_i in FF(U_i inter U_j)$
      satisfies $s_(i j)|_(X_f) = 0$. Since $U_i inter U_j$ is
      quasi-compact, by (a) there is $m_(i j) > 0$ such that
      $f^(m_(i j)) s_(i j) = 0$. Choose
      $m >= max{ m_(i j) : 1 lt.eq i,j lt.eq r }$. Then
      $f^m tilde(t)_i|_j = f^m tilde(t)_j|_i$.
    - Glue the sections ${f^m tilde(t)_i}_(i=1)^r$ on ${U_i}_(i=1)^r$ to
      obtain $s in Gamma(X, tensor(FF, LL^(times.o (n+m)), OO_X))$ with
      $s|_(X_f) = f^(n+m) t$.
]

#proposition(number: 5.15)[
  Fix a graded ring $S$ finitely generated by $S_1$ as an $S_0$-algebra, and
  let $X = Proj S$. If $FF in qcoh(X)$, then there is a natural isomorphism
  $beta: (Gamma_ast (FF))^tilde isolongto FF$.
]

#proof[
  #set enum(numbering: "I)", spacing: 1em)

  + Define $beta: (Gamma_ast (FF))^tilde -> FF$. Since
    $(Gamma_ast (FF))^tilde in qcoh(X)$ and $X$ has an open affine cover
    $D_+(f) simeq Spec S_((f))$ with $f in S_1$, we have
    $
      (Gamma_ast (FF))^tilde|_(D_+(f)) & simeq (Gamma_ast (FF))_((f)) \
                                       & simeq bigOPlus(Gamma(X, FF(n))_((f)), n in ZZ) \
                                       & simeq bigOPlus(Gamma(D_+(f), FF|_(D_+(f))(n))^tilde, n in ZZ) \
                                       & simeq (Gamma_ast (FF|_(D_+(f))))^tilde.
    $
    By _[5.3]_,
    $
      Hom((Gamma_ast (FF|_(D_+(f))))^tilde, FF|_(D_+(f)), MOD(OO_X|_(D_+(f)))) \
      simeq Hom(Gamma_ast (FF|_(D_+(f))), Gamma(D_+(f), FF|_(D_+(f))), MOD(S_((f)))).
    $
    Thus it suffices to define, for every $f in S_1$,
    $
      alpha_f: (Gamma_ast (FF))_((f)) -> Gamma(D_+(f), FF).
    $
    Define
    $m/f^d mapsto.long m times.o f^(-d) in
    Gamma(D_+(f), tensor(FF(d), OO_X(-d), OO_X)) = Gamma(D_+(f), FF)$
    for $d >= 0$ and $m in Gamma(X, FF(d))$.

  + We claim that $alpha_f$ is an $S_((f))$-module isomorphism.

    - Let $LL := OO_X(1)$. Then
      $f in S(1) = Gamma(X, tildeOf(S(1))) = Gamma(X, LL)$.
    - Write $S = S_0[f_0, dots.c, f_r]$ with $f_i in S_1$. Thus $X$ has a
      finite open affine cover $D_+(f_i) simeq Spec S_((f_i))$ for which each
      $LL|_(D_+(f_i))$ is free.
    - The intersections $D_+(f_i) inter D_+(f_j) = D_+(f_i f_j)$ are affine,
      hence quasi-compact.
    - $LL^(times.o n) = OO_X(1)^(times.o n) eqBy("(5.12b)") OO_X(n)$ for
      every $n in ZZ$.
    - *Injectivity.* If $m/f^d mapsto 0$, then by _(5.14a)_ there is $n > 0$
      such that $f^n m = 0$ in $Gamma(X, FF(n))$. Hence
      $m/f^d = f^n m/f^(n+d) = 0$ in $(Gamma_ast (FF))_((f))$.
    - *Surjectivity.* Given $t in Gamma(D_+(f), FF)$, by _(5.14b)_ there are
      $n > 0$ and $s in Gamma(X, tensor(FF, LL^(times.o n), OO_X)) =
      Gamma(X, FF(n))$ such that $s|_(D_+(f)) = f^n t$. Thus $s/f^n$ maps to
      $t$.
]

#corollary(number: 5.16)[
  Fix a ring $A$.

  #set enum(numbering: "a)", spacing: 1em)

  + If $Y$ is a closed subscheme of $PP_A^r$, then there is a homogeneous ideal
    $I lt.closed S = A[x_0, dots.c, x_r]$ such that $Y$ is the closed
    subscheme determined by $I$.
  + A scheme $Y$ over $Spec A$ is projective iff
    $Y simeq Proj S$ for some graded ring $S$ finitely generated by $S_1$ as an
    $S_0$-algebra with $S_0 = A$.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + Consider the closed immersion
    $Y morph(i, Sch) PP_A^r$. Let $II_Y = Ker i^sharp lt.closed OO_X$ be the
    ideal sheaf of $Y$ on $X = PP_A^r$. From
    $0 -> II_Y -> OO_X -> i_ast OO_Y -> 0$, exactness of twisting gives
    $0 -> II_Y(n) -> OO_X(n) -> (i_ast OO_Y)(n) -> 0$ for every $n in ZZ$.
    Taking global sections and then direct sums yields
    $0 -> Gamma_ast (II_Y) -> Gamma_ast (OO_X) -> Gamma_ast (i_ast OO_Y)$.
    Thus $I := Gamma_ast (II_Y)$ is an ideal of
    $Gamma_ast (OO_X) isoBy("(5.13)") S$. By _[3.12]_, $I$ determines a closed
    subscheme of $X = Proj S$ with sheaf of ideals $tildeOf(I)$. Since
    $II_Y in qcoh(X)$ by _(5.9)_,
    $II_Y isoBy("(5.15)") (Gamma_ast (II_Y))^tilde = tildeOf(I)$.

  + For the forward direction, if $Y$ is projective over $Spec A$, then
    $Y -> Spec A$ factors through a closed immersion
    $Y -> PP_A^r -> Spec A$. By (a), $Y simeq Proj S/I$ for a homogeneous ideal
    $I lt.closed S := A[x_0, dots.c, x_r]$. Let
    $I' := bigOPlus(I inter S_d, d > 0) subset S_+$. Then
    $(S/I')_d = (S/I)_d$ for $d > 0$ and $(S/I')_0 = A$; in particular,
    $S/I'$ is finitely generated by $(S/I')_1$ over $A$. Thus by _[3.12]_,
    $Y simeq Proj S/I simeq Proj S/I'$.

    Conversely, for such a graded ring $S$, write
    $S simeq A[x_0, dots.c, x_r]/I$. The quotient map
    $A[x_0, dots.c, x_r] -> S$ induces
    $Y = Proj S -> Proj A[x_0, dots.c, x_r] = PP_A^r$, a closed immersion by
    _[3.12a]_. Therefore $Y -> PP_A^r -> Spec A$ is projective.
]

#definition(title: "Twisting Sheaf on $PP_Y^r$")[
  For any scheme $Y$, the *twisting sheaf* $OO(1)$ on $PP_Y^r$ is
  $g^ast(OO(1))$, where
  $g: PP_Y^r = PP_(ZZ)^r times_(ZZ) Y -> PP_(ZZ)^r$ is the
  natural map.
]

#definition(number: none)[
  - *(Immersion).* A morphism $X morph(i, Sch) Z$ is an _immersion_ if $i$
    gives an isomorphism of $X$ with an open subscheme of a closed subscheme
    of $Z$, i.e. $i: X isolongto U -> Y -> Z$.
  - *(Very Ample Sheaf).* Let $X$ be a scheme over $Y$. An invertible sheaf
    $LL$ on $X$ is _very ample_ relative to $Y$ if there is an immersion
    $i: X -> PP_Y^r$ for some $r$ such that
    $i^ast(OO_(PP_Y^r)(1)) simeq LL$.
]

#remark[
  If $Y = Spec A$, then $OO(1)$ is just the $OO_X(1)$ defined on
  $X = PP_A^r = Proj A[x_0, dots.c, x_r]$ before, by _(5.12c)_.
]

#remark[
  *Remark 5.16.1.* Let $Y$ be a Noetherian scheme. Then a $Y$-scheme $X$ is projective iff it
  is proper and there exists a very ample sheaf on $X$ relative to $Y$.
]

#proof[
  - If $f: X -> Y$ is projective, then $f$ is proper by _(4.9)_. By definition
    of projective morphism, there is a closed immersion
    $X -> PP_Y^r$ for some $r$ that factors through $f$. Then $i^ast(OO(1))$
    gives a very ample invertible sheaf on $X$ relative to $Y$.
  - Conversely, if $f: X -> Y$ is proper and $LL$ is a very ample invertible
    sheaf on $X$, then $LL simeq i^ast(OO(1))$ for some immersion
    $i: X -> PP_Y^r$. But $i(X)$ is closed by _[4.4]_, so $i$ is a closed
    immersion. Hence $f: X -> PP_Y^r -> Y$ is projective.
]

#definition(number: none)[
  Fix $X in Sch$ and $FF in MOD(OO_X)$. We say $FF$ is _generated by global
  sections_ if there is a family of global sections ${s_i}_(i in I)$, where
  $s_i in Gamma(X, FF)$, such that for each $x in X$, the germs
  $(s_i)_x in FF_x$ generate the stalk $FF_x$ as an $OO_(X,x)$-module, i.e.
  $FF_x = OO_(X,x) spn { (s_i)_x : i in I }$.
]

#note-box(title: "Note")[
  $FF in MOD(OO_X)$ is generated by global sections iff $FF$ can be written
  as a quotient of a free $OO_X$-module.
]

#proof[
  Suppose $s_i in Gamma(X, FF)$ for $i in I$. Then
  $
    & FF text(" is generated by ") {s_i}_(i in I) \
    & arrow.l.r.double.long FF_x = OO_(X,x) spn { (s_i)_x : i in I } text(" for every ") x in X \
    & arrow.l.r.double.long OO_(X,x)^I morph(phi_x, #none) FF_x -> 0
      text(" is exact for every ") x in X \
    & arrow.l.r.double.long OO_X^I morph(phi, #none) FF -> 0 text(" is exact") \
    & arrow.l.r.double.long FF simeq OO_X^I / Ker phi.
  $
]

#theorem(title: "5.17. (Serre)")[
  Let $X$ be a projective scheme over a Noetherian ring $A$, let $OO_X(1)$ be
  a very ample invertible sheaf on $X$, and let $FF in coh(X)$. Then there is
  $n_0 in ZZ$ such that for every $n >= n_0$, the sheaf $FF(n)$ can be
  generated by finitely many global sections.
]

#proof[
  - By definition of the very ample sheaf $OO_X(1)$, there is a closed
    immersion $i: X -> PP_A^r$ with $i^ast OO_(PP_A^r)(1) = OO_X(1)$. Then
    $i_ast FF in coh(PP_A^r)$ by _[5.5c]_, and
    $i_ast(FF(n)) = (i_ast FF)(n)$ by _(5.12c)_. Also, $FF(n)$ is generated
    by global sections iff $i_ast(FF(n))$ is. Thus reduce to
    $X = PP_A^r = Proj S$ with $S := A[x_0, dots.c, x_r]$.
  - Cover $X$ by ${D_+(x_i)}_(i=0)^r$. For each $i$, write
    $B_i := A[x_0/x_i, dots.c, x_r/x_i]$. Since $FF in coh(X)$,
    $FF|_(D_+(x_i)) simeq tildeOf(M)_i$ for some
    $M_i in fg(MOD(B_i))$, say $M_i := B_i spn {s_(i j)}_(j=1)^(n_i)$.
  - By _(5.14b)_, for large $n > 0$ there are sections
    $t_(i j) in Gamma(X, FF(n))$ with
    $x_i^n s_(i j) = t_(i j)|_(D_+(x_i))$. The hypotheses apply because
    $D_+(x_i) simeq Spec S_((x_i)) = Spec B_i$, $FF in qcoh(X)$,
    $X_(x_i) = D_+(x_i)$, $OO_X(1)$ is invertible by _(5.12a)_, and
    $D_+(x_i) inter D_+(x_j) simeq Spec S_((x_i x_j))$ is affine.
  - Set $M_i' := M_i(n)$. Then
    $
      FF(n)|_(D_+(x_i))
      = tensor(FF, OO_X(n), OO_X)|_(D_+(x_i))
      simeq tensor(tildeOf(M)_i, tildeOf(B_i)(n), tildeOf(B_i))
      simeq tildeOf(M_i(n)) = tildeOf(M_i').
    $
    The map
    $x_i^n: FF -> FF(n), quad t mapsto.long t times.o x_i^n$
    gives an isomorphism $phi_i: M_i -> M_i(n) = M_i'$, with inverse induced
    by $x_i^(-n)$. Thus the sections $x_i^n s_(i j) = phi_i(s_(i j))$
    generate $M_i' = Gamma(D_+(x_i), FF(n))$. Therefore the global sections
    $t_(i j)$ generate $FF(n)$.
]

#corollary(number: 5.18)[
  Let $X$ be a projective scheme over a Noetherian ring $A$. Then every
  coherent sheaf $FF in coh(X)$ can be written as a quotient of a sheaf $EE$,
  where $EE$ is a finite direct sum of twisted structure sheaves $OO_X(n_i)$.
]

#proof[
  By _(5.17)_, choose $n$ such that $FF(n)$ is generated by finitely many global
  sections. Then $bigOPlus(OO_X, i=1, top: N) -> FF(n) -> 0$ is exact by the
  note above. Since twisting is exact,
  $bigOPlus(OO_X(-n), i=1, top: N) -> FF -> 0$ is exact. Thus $FF$ is a
  quotient of a finite direct sum of twisted structure sheaves.
]

#theorem(number: 5.19)[
  Let $A in fg(ALG)_k$, let $X$ be a projective scheme over $A$, and let
  $FF in coh(X)$. Then $Gamma(X, FF)$ is a finitely generated $A$-module. In
  particular, if $A = k$, then $Gamma(X, FF)$ is a finite-dimensional
  $k$-vector space.
]

#proof[
  *(I) Reduction.*

  - By _(5.16b)_, write $X = Proj S$, where $S$ is finitely generated by $S_1$
    over $S_0 = A$.
  - Set $M := Gamma_ast (FF) in GR MOD(S)$. By _(5.15)_,
    $tildeOf(M) simeq FF$.
  - Since $FF in coh(X)$, by _(5.17)_ the sheaf $FF(n)$ is generated by
    finitely many global sections for $n >> 0$, say
    $s_i in Gamma(X, FF(n))$, $1 lt.eq i lt.eq m$.
  - Let $M'$ be the $S$-submodule of $M$ generated by ${s_i}_(i=1)^m$; then
    $M' in fg(MOD(S))$. The exact sequence $0 -> M' -> M$ gives
    $0 -> tildeOf(M') -> tildeOf(M) = FF$, hence
    $0 -> tildeOf(M')(n) -> FF(n)$. Since $FF(n)$ is generated by the $s_i$,
    $tildeOf(M')(n) simeq FF(n)$. Twisting again yields
    $tildeOf(M') simeq FF$, so $FF$ corresponds to a finitely generated graded
    $S$-module.

  *(II)* It remains to show that if $M in fg(MOD(S))$, then
  $Gamma(X, tildeOf(M)) in fg(MOD(A))$.

  - Since $S_0 = A in fg(ALG)_k$, it is Noetherian. By _(3.F)_, $S$ is
    Noetherian. Since $M in GR MOD(S)$ is finitely generated, by _(I,7.4a)_
    there is a filtration
    $0 = M^0 subset M^1 subset dots.c subset M^r = M$
    in $GR MOD(S)$ such that
    $M^i / M^(i-1) simeq (S / pp_i)(n_i)$ for homogeneous primes
    $pp_i lt.closed S$.
  - This induces a filtration
    $0 = tildeOf(M)^0 subset tildeOf(M)^1 subset dots.c subset
    tildeOf(M)^r = tildeOf(M)$
    in $MOD(OO_X)$. Taking global sections preserves injectivity, so
    $
      0 = Gamma(X, tildeOf(M)^0) subset Gamma(X, tildeOf(M)^1) subset
      dots.c subset Gamma(X, tildeOf(M)^r) = Gamma(X, tildeOf(M))
    $
    in $MOD(A)$.
  - For each $i$,
    $
      0 -> Gamma(X, tildeOf(M)^(i-1)) -> Gamma(X, tildeOf(M)^i) ->
      Gamma(X, tildeOf(S / pp_i)(n_i)).
    $
    Hence the quotient is isomorphic to an $A$-submodule $N^i$ of
    $Gamma(X, tildeOf(S / pp_i)(n_i))$, giving
    $
      0 -> Gamma(X, tildeOf(M)^(i-1)) -> Gamma(X, tildeOf(M)^i) -> N^i -> 0.
    $
  - If each $Gamma(X, tildeOf(S / pp_i)(n_i))$ is finitely generated over $A$,
    then so is $N^i$ because $A$ is Noetherian. Inductively,
    $Gamma(X, tildeOf(M))$ is finitely generated over $A$.

  *(III)* It remains to handle the special case where $S$ is a graded integral
  domain, finitely generated by $S_1$ over $S_0 = A$, with
  $A in fg(ALG)_k$ an integral domain. We prove
  $Gamma(X, OO_X(n)) in fg(MOD(A))$ for every $n in ZZ$.

  - This applies to the integral domains $S / pp_i$ above, and
    $(S / pp_i)_0 = A / (pp_i inter A)$ is again a finitely generated
    $k$-algebra and an integral domain.
  - Write $S_1 := A spn {x_j : 0 lt.eq j lt.eq r}$. For every
    $n in ZZ$, the map $S(n) -> S(n+1)$ given by multiplication by
    $x_0$ is injective. Applying $Gamma(X, -)$, it suffices to prove
    $Gamma(X, OO_X(n)) in fg(MOD(A))$ for all large $n >> 0$.
  - Put $S' := bigOPlus(Gamma(X, OO_X(n)), n >= 0)$. Then
    $S subset S' subset inter_(i=0)^r S_(x_i)$. Indeed, every element of
    $S_0$ is a global section of $OO_X$, so $S_n subset Gamma(X, OO_X(n))$.
    Also, each $D_+(x_i)$ is affine, so
    $
      Gamma(X, OO_X(n)) -> Gamma(D_+(x_i), OO_X(n)) = (S_(x_i))_n subset S_(x_i).
    $
  - *Claim.* $S'$ is integral over $S$.

    Let $overline(S)$ be the integral closure of $S$ in $K = Frac S$; we show
    $S' subset overline(S)$. Since $S' = bigOPlus(S'_d, d >= 0)$, it suffices
    to show that any $s' in S'_d$ is integral over $S$. Since
    $s' in inter_(i=0)^r S_(x_i)$, for each $i$ there is $n_i > 0$ with
    $x_i^(n_i) s' in S$. Choose $n$ such that $x_i^n s' in S$ for all $i$.
    Since $S_1$ is generated by the $x_i$, for $n >> 0$ we may assume
    $y s' in S$ for every $y in S_n$. Inductively,
    $y (s')^q in S_(>= n)$ for every $q >= 1$ and $y in S_(>= n)$. Taking
    $y = x_0^n$, we get $(s')^q in (1 / x_0^n) S$ for every $q >= 1$. Thus
    $S[s'] subset (1 / x_0^n) S$, a finitely generated $S$-submodule of
    $Frac S$. By _(AM, 5.1)_, $s'$ is integral over $S$.

  - Since $S in fg(ALG)_k$ is an integral domain, taking $L = K = Frac S$ in
    _(I, 3.9)_ gives $overline(S) in fg(MOD(S))$. Since $S' subset
    overline(S)$, also $S' in fg(MOD(S))$, whence
    $Gamma(X, OO_X(n)) = S'_n in fg(MOD(A))$ for every $n >= 0$.
]

#corollary(number: 5.20)[
  Let $f: X -> Y$ be a projective morphism of schemes of finite type over $k$.
  If $FF in coh(X)$, then $f_ast FF in coh(Y)$.
]

#proof[
  - As in _(5.8c)_, the question is local on $Y$, so assume
    $Y = Spec A$ is affine. Since $Y$ is of finite type over $k$,
    $A in fg(ALG)_k$.
  - By _(5.16b)_, write $X = Proj S$, where $S$ is finitely generated by
    $S_1$ over $S_0 = A$. Since $S_0 = A$ is Noetherian, so is $S$ by
    _(3.F)_, hence $X = Proj S$ is Noetherian by _(3.H)_. By _(5.8c)_,
    $f_ast FF in qcoh(Y)$, and therefore
    $
      f_ast FF eqBy("(5.5)") tildeOf(Gamma(Y, f_ast FF))
      eqBy("Def. of f_ast") tildeOf(Gamma(X, FF)).
    $
  - Since $FF in coh(X)$, by _(5.19)_ we have
    $Gamma(X, FF) in fg(MOD(A))$. Therefore $f_ast FF in coh(Y)$.
]

=== Exercises

#exercise(
  title: "Exercise 5.3",
  // number: 5.3
)[
  Let $X = Spec A$ be an affine scheme. Show that the functors $tildeOf(dot)$
  and $Gamma(X, dot)$ are adjoint, i.e. for any $M in MOD(A)$ and any
  $FF in MOD(OO_X)$, there is a natural isomorphism
  $
    Hom(M, Gamma(X, FF), MOD(A)) simeq Hom(tildeOf(M), FF, MOD(OO_X)).
  $
]

#exercise(title: "Exercise 5.3*")[
  Let $X = Proj S$, where $S$ is a graded ring finitely generated by $S_1$ as
  an $S_0$-algebra. Show that the functors $tildeOf(dot)$ and $Gamma_ast (-)$
  are adjoint, i.e. for any $M in GR MOD(S)$ and any $FF in MOD(OO_X)$, there
  is a natural isomorphism
  $
    Hom(M, Gamma_ast (FF), MOD(S)) simeq Hom(tildeOf(M), FF, MOD(OO_X)).
  $
]
