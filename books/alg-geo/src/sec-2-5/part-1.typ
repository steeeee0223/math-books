#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.5, Definition D1
#definition(
  number: none,
  title: "Sheaves of Modules",
)[
  - Let $(X,shf.o_X)$ be a ringed space. A *sheaf of $shf.o_X$-modules* (or simply an *$shf.o_X$-module*) is a sheaf $shf.f$ on $X$, such that for each open set $U subset X$, the group $shf.f (U)$ is an $shf.o_X (U)$-module, and for each inclusion of open sets $V subset U$, the restriction homomorphism $shf.f (U)->shf.f (V)$ is compatible with the module structures via the ring homomorphism $shf.o_X (U)->shf.o_X (V)$.
  - A *morphism* $shf.f -> shf.g$ of sheaves of $shf.o_X$-module is a morphism of sheaves, such that for each open set $U subset X$, the map $shf.f (U) -> shf.g (U)$ is an $shf.o_X (U)$-module homomorphism.
]

// Hartshorne II.5, Definition D2
#definition(
  number: none,
  title: "Associated Sheaf on Spec A",
)[
  \
  Fix a ring $A$ and a graded $A$-module $M$. We define the _sheaf associated_ to $M$ on $ops.spec A$, denoted by $tildeOf(M)$, as follows. For any open subset $U subset ops.spec A$, define

  $
    tildeOf(M)(U):={s:U -> product.co_(idl.p in U)M_(idl.p) | s text("is locally a fraction") m/f med (m in M, f in A)}.
  $
  This make $tildeOf(M)$ into a sheaf with obvious restriction maps.

]

// Hartshorne II.5, Proposition 5.1
#proposition(number: 5.1)[
  Let $tildeOf(M)$ be the sheaf on $X=ops.spec A$ associated to $M in cat.mod(A)$. Then,

  #set enum(numbering: "a)", spacing: 1em)

  + $tildeOf(M)$ is an $shf.o_X$-module.
  + For each $idl.p in X$, we have $(tildeOf(M))_idl.p simeq M_idl.p$.
  + For any $f in A$, we have $tildeOf(M)(D(f)) simeq M_f$ as $A_f$-modules.
  + In particular, $Gamma(X, tildeOf(M))=M$.
]

// Hartshorne II.5, Proposition 5.2
#proposition(
  number: 5.2,
)[
  Given $A morph(phi, cat.ring) B$ and its corresponding morphism $Y=ops.spec B morph(f, cat.sch) ops.spec A=X$. Then,

  #set enum(numbering: "a)", spacing: 1em)

  + The map $M mapsto tildeOf(M)$ gives an exact, fully faithful functor $cat.mod(A) ->cat.mod(shf.o_X)$.
  + If $M,N in cat.mod(A)$, then $(tensor(M, N, over: A))^tilde simeq tensor(tildeOf(M), tildeOf(N), over: shf.o_X)$.
  + If $M_i in cat.mod(A) med (i in I)$, then $(bigOPlus(M_i, i in I))^tilde simeq bigOPlus(tildeOf(M_i), i in I)$.
  + For any $N in cat.mod(B)$, $f_ast (tildeOf(N)) simeq attach(tildeOf(N), bl: A)$ as $shf.o_X$-modules, where $N= attach(N, bl: A) in cat.mod(A)$.
  + For any $M in cat.mod(A)$, $f^ast (tildeOf(M)) simeq (tensor(M, B, over: A))^tilde$ as $shf.o_Y$-modules.
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
          & M'_idl.p edge(->) edge("d", simeq, ->)
          & M_idl.p edge(->) edge("d", simeq, ->)
          & M''_idl.p edge(->) edge("d", simeq, ->)
          & 0 \
          0 edge(->)
          & tildeOf(M)'_idl.p edge(->)
          & tildeOf(M)_idl.p edge(->)
          & tildeOf(M)''_idl.p edge(->)
          & 0
        $,
      )
    ]

    for every $idl.p in ops.spec A$. Therefore, _[1.2c]_ implies that the sequence $0 ->tildeOf(M)' -> tildeOf(M) ->tildeOf(M)'' ->0$ of $shf.o_X$-modules is exact.

    - *(Full Faithfulness).* We claim that $ops.hom(M, N, over: cat.mod(A)) simeq ops.hom(tildeOf(M), tildeOf(N), over: cat.mod(shf.o_X))$.
    Clearly, a homomorphism $M morph(tildeOf(phi), cat.mod(A)) N$ induces the morphism $tildeOf(M) morph(tildeOf(f), cat.mod(shf.o_X)) tildeOf(N)$. Conversely, if we have a morphism $tildeOf(M) morph(tildeOf(f), cat.mod(shf.o_X)) tildeOf(N)$, by definition with $U=X$, we have $tildeOf(f) :M= tildeOf(M)(X) morph(#none, cat.mod(A)) tildeOf(N)(X)=N$.

  + For each $idl.p in ops.spec A$, we have the isomorphisms
    $
      (tensor(M, N, over: A))^tilde_idl.p & isoBy("(5.1b)")
                                            (tensor(M, N, over: A))_idl.p isoBy("AM")
                                            tensor(M_idl.p, N_idl.p, over: A_idl.p) isoBy("(5.1b)")
                                            tensor(tildeOf(M)_idl.p, tildeOf(N)_idl.p, over: shf.o_(X,idl.p)) \
                                          & isoBy("Def.")
                                            (tensor(M, N, over: A))^tilde_idl.p
    $
    as stalks. Thus, _(1.1)_ implies that $(tensor(M, N, over: A))^tilde simeq tensor(tildeOf(M), tildeOf(N), over: shf.o_X)$ as sheaves.

  + For each $idl.p in ops.spec A$, we have the isomorphisms

    $
      (bigOPlus(M_i, i in I))^tilde_idl.p & isoBy("(5.1b)")
                                            (bigOPlus(M_i, i in I))_idl.p
                                            simeq bigOPlus((M_i)_idl.p, i in I) \
                                          & isoBy("(5.1b)")
                                            bigOPlus((tildeOf(M_i))_idl.p, i in I)
                                            isoBy("Def.")
                                            (bigOPlus(tildeOf(M_i), i in I))_idl.p
    $

    as stalks. Thus, $(bigOPlus(M_i, i in I))^tilde simeq bigOPlus(tildeOf(M_i), i in I)$ as sheaves.

  + Note that $tildeOf(A) = shf.o_(ops.spec A) = shf.o_X$ for any ring $A$.
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
          shf.o_X edge("d", f^sharp, ->) edge("r", tildeOf(alpha), ->) & attach(tildeOf(N), bl: A) edge("d", tildeOf(f)^sharp, -->) \
          f_* shf.o_Y edge("r", tildeOf(beta), ->) & f_* tildeOf(N)
        $,
      )
    ]

    where the action $alpha$ is defined by $(a,n) mapsto beta(phi(a), n) = phi(a) dot n$.

    Further, for each $idl.q in ops.spec B = Y$, diagram (i) induces the commutative diagram:

    #align(center)[
      #diagram(
        cell-size: 15mm,
        $
          A_(phi^(-1) (idl.q)) edge("r", ->) edge("d", phi_idl.q, ->) & attach(N, bl: A)_(phi^(-1) (idl.q)) edge("d", tilde(phi)_idl.q, ->) \
          B_idl.q edge("r", ->) & N_idl.q
        $,
      )
    ]

    Now, for every open set $U subset X$, define the sheaf map

    $
      tilde(f)^sharp_U : attach(tildeOf(N), bl: A)(U) -> f_* tildeOf(N)(U) = tildeOf(N)(f^(-1) U), quad
      s mapsto tilde(phi)_bullet compose s compose f.
    $

    This makes diagram (ii) commutative. For each $idl.q in ops.spec B$, the map
    $
      tilde(f)^sharp_idl.q :
      attach(tildeOf(N), bl: A)_(f(idl.q)) simeq attach(N, bl: A)_(phi^-1(idl.q))
      -> N_idl.q simeq (tildeOf(N))_idl.q
    $
    is a natural isomorphism of stalks. Hence, $tilde(f)^sharp$ gives an isomorphism $f_* (tildeOf(N)) simeq attach(tildeOf(N), bl: A)$ of $shf.o_X$-modules.

  + Note that $f^(-1) shf.o_X = coprod(shf.o_(X, f(y)), y in Y) in cat.shf (Y)$; and recall that
    $f^* shf.f = tensor(f^(-1) shf.f, shf.o_Y, over: f^(-1) shf.o_X)$ if $shf.f in cat.mod(shf.o_X)$.

    Now, for each $idl.q in ops.spec B = Y$, we see that

    $
      (f^* tildeOf(M))_idl.q eqBy("Def.")
      tensor(M_(phi^(-1) (idl.q)), B_idl.q, over: A_(phi^(-1) (idl.q)))
      simeq tensor((tensor(M_(phi^(-1) (idl.q)), A_(phi^(-1) (idl.q)), over: A)), B_idl.q, over: A_(phi^(-1) (idl.q))) \
      simeq tensor((tensor(M, B, over: A)), B_idl.q, over: B)
      simeq tensor(M, B_idl.q, over: A) \
      simeq (tensor(M, B, over: A))_idl.q
      isoBy("(5.1b)")
      (tensor(M, B, over: A))^tilde_idl.q
    $

    Therefore, $f^* tildeOf(M) simeq (tensor(M, B, over: A))^tilde$ as $shf.o_Y$-modules.
]

// Hartshorne II.5, Definition D3
#definition(number: none)[
  Fix a scheme $(X, shf.o_X)$.

  + (Quasi-Coherent Sheaves) A *quasi-coherent sheaf* on $X$ is a sheaf
    $shf.f in cat.mod(shf.o_X)$ such that $X$ can be covered by open affine subsets
    $U_i = ops.spec A_i$ where for each $i$,
    $shf.f|_(U_i) simeq tildeOf(M)_i$ for some $M_i in cat.mod(A_i)$.

  + (Coherent Sheaves) A *coherent sheaf* on $X$ is a quasi-coherent sheaf
    on $X$ with the additional assumption that each $M_i in cat.mod(A_i)$
    is finitely generated.
]

// Hartshorne II.5, Lemma 5.3
#lemma(number: 5.3)[
  Let $shf.f$ be a quasi-coherent sheaf on $X = ops.spec A$ and let $f in A$.

  #set enum(numbering: "a)", spacing: 1em)

  + If the global section $s in Gamma(X, shf.f)$ satisfies
    $s|_(D(f)) = 0$ in $shf.f (D(f))$, then $f^n s = 0$ for some $n > 0$.

  + Given $t in shf.f (D(f))$, then $f^n t$ extends to a global section
    in $Gamma(X, shf.f)$ for some $n > 0$.
]

#proof[
  - Some settings:

    - Since $shf.f$ is quasi-coherent on $X$, cover $X$ by open affine subsets
      $V = ops.spec B$ such that $shf.f|_V simeq tildeOf(M)$ for some $M in cat.mod(B)$.

    - ${D(g)}_(g in A)$ forms a base for $shf.t_X$.
      Cover $V$ by some $D(g)$’s. Then the inclusion
      $ops.spec A_g = D(g) inclusion(#none, cat.sch) V = ops.spec B$ induces
      $B morph(#none, cat.ring) A_g$.
      By _(5.2e)_,
      $
        shf.f|_(D(g)) = i^* (shf.f|_V)
        isoBy("(5.2e)") i^* tildeOf(M)
        isoBy("Def.") tildeOf(M tensor(B, A_g, over: B)).
      $

    - Since $shf.f$ is quasi-coherent on $X$, $X$ can be covered by $D(g_i)$’s
      such that $shf.f|_(D(g_i)) simeq tildeOf(M)_i$ for some
      $M_i in cat.mod(A_(g_i))$.
      But $X = ops.spec A$ is quasi-compact, so we may choose finitely many $i$'s,
      say $1 lt.eq i lt.eq r$.

  - Proof of (a):
    For each $i$, set
    $s_i := s|_(D(g_i)) in shf.f (D(g_i)) = Gamma(D(g_i), tildeOf(M)_i) simeq M_i$.
    On the intersection $D(f) inter D(g_i) = D(f g_i)$, we have
    $
      s_i|_(D(f)) = s|_(D(f g_i)) = 0
      text("in") (shf.f|_(D(g_i)))(D(f))
      simeq tildeOf(M)_i (D(f))
      simeq (M_i)_f.
    $
    So $f^(n_i) s = 0$ in $M_i = shf.f (D(g_i))$ for some $n_i > 0$.
    Since there are only finitely many $i$'s, pick
    $n >= max{ n_i : 1 lt.eq i lt.eq r }$ such that $f^n s_i = 0$ for all $i$.
    As the $D(g_i)$’s cover $X$, we get $f^n s = 0$.

  - Proof of (b):
    - Let $t in shf.f (D(f))$. For each $i$, set
      $t_i := t|_(D(g_i)) in shf.f (D(f g_i)) simeq (M_i)_f$.
      By localization, there exists
      $tildeOf(t)_i in M_i simeq shf.f (D(g_i))$ such that
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
      in shf.f (D(g_i g_j))$ with $s|_(D(f)) = 0$.
      By (a), there exists $m_(i j) > 0$ such that
      $f^(m_(i j)) s_(i j) = 0$ on $D(g_i g_j)$.
      Pick $m >= max{ m_(i j) : 1 lt.eq i,j lt.eq r }$ such that
      $f^m s_(i j) = 0$, i.e. $f^m tildeOf(t)_i = f^m tildeOf(t)_j$
      on $D(g_i g_j)$.

      Now glue the sections ${ f^m tildeOf(t)_i }_(i=1)^r$ on
      ${ D(g_i) }_(i=1)^r$, obtaining
      $s in shf.f (X)$ with $s|_(D(f)) = f^(n+m) t$.

      Indeed, on each $D(f g_i)$:
      $ s = f^m tildeOf(t)_i = f^(n+m) t_i = f^(n+m) t, $
      and on each $D(f g_i g_j)$:
      $ f^(n+m) t_i = f^m tildeOf(t)_i = f^m tildeOf(t)_j = f^(n+m) t_j. $
]

// Hartshorne II.5, Proposition 5.4
#proposition(
  number: 5.4,
)[
  Let $(X,shf.o_X)$ be a scheme. Then

  #set enum(numbering: "a)", spacing: 1em)

  + $shf.f in cat.mod(shf.o_X)$ is quasi-coherent $arrow.l.r.double.long$ For every open affine subset $U=ops.spec A subset X$, we have $shf.f|_U simeq tildeOf(M)$ for some $M in cat.mod(A)$.
  + If $X$ is Noetherian. Then $shf.f$ is coherent $arrow.l.r.double.long$ The same is true, with the extra condition that $M in cat.mod(A)$ is finitely generated.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)
  + $(Leftarrow)$. Clear. $(Rightarrow)$. Given an open affine subset $U=ops.spec A subset X$.

    - By _(5.3I)_, we may cover $X$ by $D(g_i)$ where $g_i in B_i$ such that $shf.f|_(D(g_i)) simeq tildeOf(M)_i$ for some $M_i in cat.mod((B_i)_(g_i))$. Since we may cover $U$ by some $D(g_i) subset U$, it follows that $shf.f_U$ is quasi-coherent. Thus, we may reduce to consider the affine case $X=ops.spec A$.
    - Consider $M := Gamma(X, shf.f)$. By _[5.3]_, there is a natural map $alpha: tildeOf(M) to shf.f$. Since $shf.f$ is quasi-coherent on $X=ops.spec A$, we may cover $X$ by $D(g_i) simeq ops.spec A_(g_i)$ such that $shf.f|_(D(g_i)) simeq tildeOf(M)_i$ for some $M_i in cat.mod(A_(g_i))$. Now,
    $
      M_i eqBy("(5.1d)") Gamma(D(g_i), tildeOf(M)_i) simeq Gamma(D(g_i), shf.f|_(D(g_i)))=shf.f (D(g_i)) isoBy("(5.3)") M_(g_i}).
    $
    Thus,
    $
      alpha_(D(g_i)): tildeOf(M)(D(g_i)) isoBy("(5.1c)") M_i morph(tilde, #none) M_(g_i) simeq shf.f (D(g_i))
    $
    is an isomorphism for each $i$, and hence, $alpha: tildeOf(M) morph(tilde, #none) shf.f$ is an isomorphism of $shf.o_X$-modules.

  + $(Leftarrow)$. Clear. $(Rightarrow)$. In addition to (i), $M_i=M_{g_i} in cat.mod(A_(g_i))$ is finitely generated for each $i$. Now, since $ops.spec A$ is Noetherian, $A$ is a Noetherian ring by _(3.2)_, whence so is $A_(g_i)$ for each $i$ by _(AM, 7.3)_. Further, $M_(g_i) in cat.mod(A_(g_i))$ is Noetherian for each $i$ by _(AM, 6.5)_, and thus, $M in cat.mod(A)$ is Noetherian as $A=(g_1,\cdots,g_n)$. Therefore, by _(AM, 6.2)_, $M in cat.mod(A)$ is finitely generated.

]

#remark[
  Note that being _finitely generated_ is actually a _local property_. Thus, there is no need to assume $X$ is Noetherian in (ii).
]

// Hartshorne II.5, Corollary 5.5
#corollary(
  number: 5.5,
)[
  Let $X=ops.spec A$.

  #set enum(numbering: "a)", spacing: 1em)

  + The functor $M mapsto tildeOf(M)$ gives an equivalence of categories between the category $cat.mod(A)$ of $A$-modules and the category $cat.qcoh (X)$ of quasi-coherent $shf.o_X$-modules. Its inversre is the functor $Gamma(X, dot)$.

  + If $A$ is Noetherian, the same functor also gives an equivalence of categories between the category $fg(cat.mod(A))$ of finitely generated $A$-modules and the category $cat.coh (X)$ of coherent $shf.o_X$-modules.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + We note that
    - For $M in cat.mod(A)$, we have $tildeOf(M) in cat.qcoh (X)$ by _(5.1)_.
    - For $shf.f in cat.qcoh (X)$, we have $Gamma(X, shf.f) in cat.mod(Gamma(X, shf.o_X)) = cat.mod(A)$ by definition.
    - By _(5.1d)_, we have
      $M mapsto.long tildeOf(M) mapsto.long Gamma(X, tildeOf(M)) = M$.
    - By _(5.4i)_, we have
      $shf.f mapsto.long Gamma(X, shf.f) mapsto.long Gamma(X, shf.f)^tilde
      attach(simeq, t: alpha) shf.f$.

  + Similarly.
]

// Hartshorne II.5, Proposition 5.6
#proposition(number: 5.6)[
  Let $X$ be an affine scheme, and let
  $0 -> shf.f' morph(phi, #none) shf.f morph(psi, #none) shf.f'' -> 0$
  be an exact sequence of $shf.o_X$-modules. If $shf.f' in cat.qcoh (X)$, then
  the sequence
  $
    0 -> Gamma(X, shf.f') morph(phi_X, #none) Gamma(X, shf.f)
    morph(psi_X, #none) Gamma(X, shf.f'') -> 0
  $
  is exact.
]

#notation[
  - For each $k$, denote $U_k := D(f_k)$; for each $i$, similarly,
    $U_i := D(g_i)$. For intersections, set
    $U_(k i) := D(f_k g_i) = D(f_k) inter D(g_i)$, and similarly for
    $U_(i j)$ and $U_(i j k)$.
  - For any $shf.f in cat.mod(shf.o_X)$ and any section $s$, denote the restriction
    $s|_k := s|_(U_k) in shf.f (U_k)$, and define $s|_(k i)$, $s|_(i j)$,
    and $s|_(i j k)$ similarly.
  - For any morphism $shf.f morph(phi, cat.mod(shf.o_X)) shf.g$, denote by $phi_k$ the map
    $phi_(U_k): shf.f (U_k) -> shf.g (U_k)$, and define $phi_(k i)$, $phi_(i j)$,
    and $phi_(i j k)$ similarly.
]

#proof[
  From _[1.8]_, $Gamma(X, dot)$ is a left exact functor, so it suffices to
  show that $psi_X$ is surjective. Given $s'' in shf.f''(X)$, since $psi$ is
  surjective, by _[1.3a]_ there exists an open cover ${D(f_k)}$ for $X$ and,
  for each $k$, a section $t_k in shf.f (U_k)$ such that
  $s''|_k = psi_k (t_k)$. Since $X$ is affine, hence quasi-compact, choose
  finitely many $k$'s, say $1 lt.eq k lt.eq r$.

  *Step I.* For each $k$, there are $n_k > 0$ and
  $hat(t)_k in shf.f (X)$ such that $psi_X (hat(t)_k) = f_k^(n_k) s''$ in
  $shf.f''(X)$.

  #set enum(numbering: "i)", spacing: 1em)

  + As $X$ is affine, choose a finite open affine cover ${D(g_i)}_(i=1)^p$
    for $X$ such that $s''|_i = psi_i (t_i)$ for some $t_i in shf.f (U_i)$.

  + On $U_(k i) = U_k inter U_i$, we have $psi_(i k) = psi_(k i)$, so
    $
      psi_(i k) (t_k|_i) = psi_(k i) (t_k|_i)
      = psi_k (t_k)|_i = s''|_(k i) = s''|_(i k)
      = psi_i (t_i)|_k = psi_(i k) (t_i|_k).
    $
    Hence $t_k|_i - t_i|_k in ops.ker psi_(i k) = ops.im phi_(i k)$. By exactness,
    $phi_(i k) (s'_(i k)) = t_k|_i - t_i|_k$ for some
    $s'_(i k) in shf.f'(U_(i k))$.

  + Since $shf.f' in cat.qcoh (X)$, by _(5.3b)_ we have
    $f_k^(n_i) s'_(i k) in shf.f'(U_i)$ for some $n_i > 0$. Take
    $n >= max{ n_i }_(i=1)^p$ such that $f_k^n s'_(i k) in shf.f'(U_i)$ for
    all $i$. Set
    $u_i := phi_i (f_k^n s'_(i k)) in shf.f (U_i)$ and
    $tilde(t)_i := f_k^n t_i + u_i in shf.f (U_i)$. Then
    $
      psi_i (tilde(t)_i)
      = f_k^n psi_i (t_i) + psi_i phi_i (f_k^n s'_(i k))
      = f_k^n s''|_i.
    $

  + For each $i,j$, on $U_(i j)$ we have
    $
      psi_(i j) (tilde(t)_i|_j)
      = psi_i (tilde(t)_i)|_j
      = f_k^n s''|_(i j)
      = f_k^n s''|_(j i)
      = psi_j (tilde(t)_j)|_i
      = psi_(i j) (tilde(t)_j|_i).
    $
    Thus $tilde(t)_i|_j - tilde(t)_j|_i in ops.ker psi_(i j) = ops.im phi_(i j)$.
    By exactness, choose $tilde(s)'_(i j) in shf.f'(U_(i j))$ with
    $phi_(i j) (tilde(s)'_(i j)) = tilde(t)_i|_j - tilde(t)_j|_i$.

  + Note that on $U_(i k)$,
    $
      tilde(t)_i|_k
      = f_k^n t_i|_k + u_i|_k
      = f_k^n t_i|_k + phi_(i k) (f_k^n s'_(i k))
      = f_k^n (t_i|_k + phi_(i k) (s'_(i k)))
      eqBy("(ii)") f_k^n t_k|_i.
    $
    Restricting to $U_(i j k)$ gives
    $
      phi_(i j k) (tilde(s)'_(i j)|_k)
      = phi_(i j) (tilde(s)'_(i j))|_k
      = tilde(t)_i|_(j k) - tilde(t)_j|_(i k)
      = f_k^n t_k|_(i j) - f_k^n t_k|_(j i)
      = 0.
    $
    Since $phi_(i j k)$ is injective, $tilde(s)'_(i j)|_k = 0$ on
    $U_(i j) inter U_k$. Since $shf.f' in cat.qcoh (X)$, by _(5.3a)_ there is
    $m_(i j) > 0$ such that $f_k^(m_(i j)) tilde(s)'_(i j) = 0$ in
    $shf.f'(U_(i j))$. Choose
    $m >= max{ m_(i j) : 1 lt.eq i,j lt.eq p }$. Then
    $
      f_k^m (tilde(t)_i|_j - tilde(t)_j|_i)
      = phi_(i j) (f_k^m tilde(s)'_(i j)) = 0,
    $
    so $f_k^m tilde(t)_i|_j = f_k^m tilde(t)_j|_i$ in $shf.f (U_(i j))$.
    Glue the sections ${f_k^m tilde(t)_i}_(i=1)^p$ on ${U_i}_(i=1)^p$ to
    obtain $hat(t)_k in shf.f (X)$.

  + For each $i$,
    $
      psi_X (hat(t)_k)|_i
      = psi_i (hat(t)_k|_i)
      = psi_i (f_k^m tilde(t)_i)
      = f_k^m psi_i (tilde(t)_i)
      eqBy("(iii)") f_k^(m+n) s''|_i.
    $
    Hence $psi_X (hat(t)_k) = f_k^(m+n) s''$ on $X$. This $m+n$ is the
    required $n_k$.

  *Step II.* Since there are finitely many $k$'s, choose
  $N >= max{ n_k }_(k=1)^r$ such that
  $psi_X (hat(t)_k) = f_k^N s''$ for all $k$. Further,
  $X = union_(k=1)^r D(f_k) = union_(k=1)^r D(f_k^N)$, so
  $lr(chevron.l f_1^N, dots.c, f_r^N chevron.r) = A$. Thus
  $1 = sum_(k=1)^r a_k f_k^N$ for some $a_k in A$. Set
  $t := sum_(k=1)^r a_k hat(t)_k in shf.f (X)$. Then
  $
    psi_X (t)
    = sum_(k=1)^r a_k psi_X (hat(t)_k)
    = sum_(k=1)^r a_k f_k^N s''
    = s''.
  $
]

// Hartshorne II.5, Remark 5.6.1
#remark(title: "5.6.1")[
  Cohomology later makes Proposition 5.6 immediate: higher cohomology of a
  quasi-coherent sheaf on an affine scheme vanishes (III.3.5), so the long
  exact cohomology sequence gives exactness on global sections.
]

// Hartshorne II.5, Proposition 5.7
#proposition(number: 5.7)[
  Let $X$ be a scheme.

  #set enum(numbering: "i)", spacing: 1em)

  + The kernel, cokernel, and image of any morphism
    $shf.f morph(phi, cat.qcoh (X)) shf.g$ are quasi-coherent.
  + Any extension of quasi-coherent sheaves is quasi-coherent.
  + If $X$ is Noetherian, then (i) and (ii) are true for coherent sheaves.
]

#proof[
  The question is local, so assume $X = ops.spec A$ is affine.

  #set enum(numbering: "i)", spacing: 1em)

  + By _(5.5)_, $shf.f = tildeOf(M)$ and $shf.g = tildeOf(N)$ for some
    $M,N in cat.mod(A)$. By _(5.2)_, the functor $M mapsto tildeOf(M)$ is exact
    and fully faithful, so $phi$ corresponds to a homomorphism
    $M morph(alpha, cat.mod(A)) N$. Since
    $0 -> ops.ker alpha -> M morph(alpha, #none) ops.im alpha -> 0$ is exact, the
    sequence
    $
      0 -> tildeOf(ops.ker alpha) -> tildeOf(M) morph(phi, #none)
      tildeOf(ops.im alpha) -> 0
    $
    is exact, with $tildeOf(ops.ker alpha) simeq ops.ker phi$ and
    $tildeOf(ops.im alpha) simeq ops.im phi$. Similarly,
    $ops.coker phi simeq tildeOf(ops.coker alpha)$. Therefore these sheaves are
    quasi-coherent.

  + *Claim.* If $0 -> shf.f' -> shf.f -> shf.f'' -> 0$ is exact and
    $shf.f', shf.f'' in cat.qcoh (X)$, then $shf.f in cat.qcoh (X)$.

    By _(5.6)_,
    $
      0 -> Gamma(X, shf.f') -> Gamma(X, shf.f) -> Gamma(X, shf.f'') -> 0
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
          & shf.f' edge(->)
          & shf.f edge(->)
          & shf.f'' edge(->)
          & 0
        $,
      )
    ]

    with exact rows. Since $shf.f', shf.f'' in cat.qcoh (X)$, the maps $theta'$ and
    $theta''$ are isomorphisms. By the Five Lemma, $theta$ is an isomorphism.
    Thus $shf.f simeq tildeOf(M) in cat.qcoh (X)$.

  + If $X$ is Noetherian and $shf.f', shf.f'' in cat.coh (X)$, then by _(5.5)_,
    $M', M'' in fg(cat.mod(A))$. Since $0 -> M' -> M -> M'' -> 0$ is exact,
    $M$ is finitely generated, whence $shf.f = tildeOf(M) in cat.coh (X)$.
]

// Hartshorne II.5, Proposition 5.8
#proposition(number: 5.8)[
  Let $f: X -> Y$ be a scheme morphism.

  #set enum(numbering: "a)", spacing: 1em)

  + If $shf.g in cat.qcoh (Y)$, then $f^ast shf.g in cat.qcoh (X)$.
  + If $X$ and $Y$ are Noetherian, and $shf.g in cat.coh (Y)$, then
    $f^ast shf.g in cat.coh (X)$.
  + Assume that either (i) $X$ is Noetherian, or (ii) $f$ is quasi-compact
    and separated. If $shf.f in cat.qcoh (X)$, then $f_ast shf.f in cat.qcoh (Y)$.
]

#proof[
  For (a) and (b), the questions are local, so assume
  $X = ops.spec A morph(f, cat.sch) ops.spec B = Y$ is induced by
  $B morph(phi, cat.ring) A$.

  #set enum(numbering: "a)", spacing: 1em)

  + If $shf.g in cat.qcoh (Y)$, then by _(5.5)_ $shf.g = tildeOf(N)$ for some
    $N in cat.mod(B)$. Hence
    $
      f^ast shf.g = f^ast tildeOf(N)
      isoBy("(5.2e)") (tensor(N, A, over: B))^tilde in cat.qcoh (X),
    $
    since $tensor(N, A, over: B) in cat.mod(A)$.

  + If $X,Y$ are Noetherian and $shf.g in cat.coh (Y)$, then in addition to (a) we
    have $N in fg(cat.mod(B))$. There is an $n > 0$ and a surjection
    $B^n -> N$. Since $- tensor_B A$ is right
    exact,
    $A^n simeq tensor(B^n, A, over: B) ->
    tensor(N, A, over: B)$, so $tensor(N, A, over: B) in fg(cat.mod(A))$. Thus
    $f^ast shf.g simeq (tensor(N, A, over: B))^tilde in cat.coh (X)$ by _(5.5)_.

  + This question is local on $Y$ only.

    - If $V subset Y$ is open affine, then $(f_ast shf.f)|_V$ depends on the
      restriction of $shf.f$ to $f^(-1) (V) subset X$. Replacing $Y$ and $X$ by
      $V$ and $f^(-1) (V)$, assume $Y := ops.spec B$ is affine.
    - In both cases (i) and (ii), $X$ is quasi-compact, so cover $X$ by
      finitely many open affines $U_i$ with $1 lt.eq i lt.eq r$.
    - *Case (ii).* Since $f$ is separated, by _[4.3]_ each
      $U_i inter U_j$ is affine. Denote it by $U_(i j k) := U_i inter U_j$,
      here with $k = 1$.
    - *Case (i).* Since $X$ is Noetherian, each $U_i inter U_j$ is
      quasi-compact. Cover each $U_i inter U_j$ by finitely many open affines
      $U_(i j k)$.
    - *Claim.* If $shf.f in cat.qcoh (X)$, then $f_ast shf.f in cat.qcoh (Y)$.

      By the sheaf property, if $V subset Y$ is open, giving
      $s in shf.f (f^(-1) V)$ is the same as giving sections
      $s_i in shf.f (f^(-1) V inter U_i)$ whose restrictions agree on
      $f^(-1) V inter U_(i j k)$. Thus we have an exact sequence of
      $shf.o_Y$-modules
      $
        0 -> f_ast shf.f -> bigOPlus(f_ast (shf.f|_(U_i)), i=1, top: r)
        morph(psi, #none) bigOPlus(f_ast (shf.f|_(U_(i j k))), (i,j,k)).
      $
      Since $shf.f in cat.qcoh (X)$,
      $
        bigOPlus(f_ast (shf.f|_(U_i)), i=1, top: r)
        isoBy("Def.") bigOPlus(f_ast (tildeOf(M)_i), i=1, top: r)
        isoBy("(5.2d)") bigOPlus(attach(tildeOf(M)_i, bl: B), i=1, top: r)
        isoBy("(5.2c)") (bigOPlus(attach(M_i, bl: B), i=1, top: r))^tilde
        in cat.qcoh (Y)
      $
      for some $M_i in cat.mod(A_i)$. Similarly,
      $bigOPlus(f_ast (shf.f|_(U_(i j k))), (i,j,k)) in cat.qcoh (Y)$. Hence $psi$ is a
      morphism of quasi-coherent sheaves on $Y$, so
      $f_ast shf.f = ops.ker psi in cat.qcoh (Y)$ by _(5.7a)_.
]

// Hartshorne II.5, Definition D4
#definition(
  number: none,
  title: "Ideal Sheaf",
)[
  Let $Y$ be a closed subscheme of $X$ and let $i: Y -> X$ be the inclusion
  morphism. The *ideal sheaf* of $Y$ is
  $shf.i_Y := ops.ker i^sharp = ops.ker (shf.o_X -> i_ast shf.o_Y)$.
]

// Hartshorne II.5, Proposition 5.9
#proposition(number: 5.9)[
  Let $X$ be a scheme.

  #set enum(numbering: "i)", spacing: 1em)

  + For any closed subscheme $Y$ of $X$, the ideal sheaf $shf.i_Y$ is a
    quasi-coherent sheaf of ideals on $X$.
  + In addition to (i), if $X$ is Noetherian, then $shf.i_Y$ is coherent.
  + Conversely, if $shf.j$ is a quasi-coherent sheaf of ideals on $X$, then
    $shf.j = shf.i_Y$ is the ideal sheaf of a uniquely determined closed subscheme
    $Y$ of $X$.
]

#proof[
  #set enum(numbering: "i)", spacing: 1em)

  + The inclusion morphism $i: Y -> X$ is quasi-compact and separated by
    _(4.6a)_ because $i$ is a closed immersion. Since $Y$ is a scheme,
    $shf.o_Y in cat.qcoh (Y)$, so by _(5.8c)_ $i_ast shf.o_Y in cat.qcoh (X)$. Hence
    $i^sharp: shf.o_X -> i_ast shf.o_Y$ is a morphism in $cat.qcoh (X)$. By _(5.7i)_,
    $shf.i_Y = ops.ker i^sharp in cat.qcoh (X)$.

  + If $X$ is Noetherian, then for any open affine subset
    $U = ops.spec A subset X$, the ring $A$ is Noetherian. Thus the ideal
    $I := Gamma(U, shf.i_Y|_U) lt.closed Gamma(U, shf.o_X|_U) = A$ is finitely
    generated. By _(5.5)_,
    $tildeOf(I) = (Gamma(U, shf.i_Y|_U))^tilde = shf.i_Y|_U$. Thus
    $shf.i_Y in cat.coh (X)$.

  + Given $shf.j in cat.qcoh (X)$ with $shf.j lt.closed shf.o_X$, consider
    $Y := ops.supp (shf.o_X\/shf.j)$. We claim that $(Y, shf.o_X\/shf.j)$ is the unique
    closed subscheme of $X$ with ideal sheaf $shf.j$. Uniqueness is clear.
    The question is local, so assume $X = ops.spec A$ is affine. Since
    $shf.j in cat.qcoh (X)$, $shf.j = tildeOf(idl.a)$ for some ideal $idl.a lt.closed A$.
    Then
    $
      Y & = ops.supp (shf.o_X\/shf.j)
          eqBy("Def.") { P in X : (shf.o_X\/shf.j)_P != 0 } \
        & eqBy("(5.1b)") { idl.p in X : (A \/idl.a)_idl.p != 0 }
          = ops.spec (A \/ idl.a) isoBy("homeom.") V(idl.a).
    $
    Thus $(Y, shf.o_X\/shf.j)$ is the closed subscheme of $X$ determined by $idl.a$
    (cf. _3.2.3_).
]

// Hartshorne II.5, Corollary 5.10
#corollary(number: 5.10)[
  If $X = ops.spec A$ is an affine scheme, then:

  #set enum(numbering: "i)", spacing: 1em)

  + There is a 1-1 correspondence between ideals $idl.a lt.closed A$ and closed
    subschemes $Y subset X$, given by $idl.a mapsto$ the image of
    $ops.spec (A\/idl.a)$ in $X$.
  + In particular, every closed subscheme of an affine scheme is affine.
]

#proof[
  By _(5.5)_, the quasi-coherent sheaves of ideals on $X = ops.spec A$ are in
  one-to-one correspondence with the ideals of $A$.
]

// Hartshorne II.5, Definition D5
#definition(title: "Associated Sheaf on Proj S")[
  Fix a graded ring $S$ and a graded $S$-module $M$. We define the _sheaf
  associated_ to $M$ on $ops.proj S$, denoted by $tildeOf(M)$, as follows. For any
  open subset $U subset ops.proj S$, define
  $
    tildeOf(M)(U) :=
    { s: U -> coprod(M_((idl.p)), idl.p in U) |
      s text(" is locally a fraction ") m/f med (m in M, f in A) }.
  $
  This makes $tildeOf(M)$ into a sheaf with obvious restriction maps.
]

// Hartshorne II.5, Proposition 5.11
#proposition(number: 5.11)[
  Fix a graded ring $S$ and a graded $S$-module $M$. Let $X = ops.proj S$. Then:

  #set enum(numbering: "a)", spacing: 1em)

  + For any $idl.p in X$, the stalk $(tildeOf(M))_idl.p = M_((idl.p))$.
  + For any homogeneous $f in S_+$,
    $tildeOf(M)|_(D_+(f)) simeq tildeOf(M_((f)))$ via
    $D_+(f) simeq ops.spec S_((f))$.
  + $tildeOf(M) in cat.qcoh (X)$. If $S$ is Noetherian and $M$ is finitely
    generated, then $tildeOf(M) in cat.coh (X)$.
]

#proposition(number: "5.A")[
  Fix a graded ring $S$ generated by $S_1$ as an $S_0$-algebra, and let
  $X = ops.proj S$.

  #set enum(numbering: "a)", spacing: 1em)

  + For any $M,N in cat.gr cat.mod(S)$ and $f in S_1$,
    $(tensor(M, N, over: S))_((f)) simeq tensor(M_((f)), N_((f)), over: S_((f)))$.
  + Continuing (a),
    $(tensor(M, N, over: S))^tilde simeq tensor(tildeOf(M), tildeOf(N), over: shf.o_X)$.

  Let $T$ be another graded ring, generated by $T_1$ as a $T_0$-algebra. Let
  $phi: S -> T$ be a graded homomorphism, let $U subset Y = ops.proj T$, and let
  $f: U -> X$ be determined by $phi$ as in _[2.14]_.

  + For any $M in cat.gr cat.mod(S)$,
    $f^ast tildeOf(M) simeq (tensor(M, T, over: S))^tilde|_U$ as $shf.o_Y$-modules.
  + For any $N in cat.gr cat.mod(T)$,
    $f_ast (tildeOf(N)|_U) simeq (attach(N, bl: S))^tilde$ as $shf.o_X$-modules.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + Note that $tensor(M, N, over: S)$ is a graded $S$-module by
    $(tensor(M, N, over: S))_d = bigOPlus(tensor(M_(d_1), N_(d_2), over: S), d_1+d_2=d)$.
    Fix $f in S_1$. The canonical inclusions
    $S_((f)) -> S_f$, $M_((f)) -> M_f$, and $N_((f)) -> N_f$ induce a
    homomorphism
    $tensor(M_((f)), N_((f)), over: S_((f))) -> tensor(M_f, N_f, over: S_f)$. The
    canonical isomorphism
    $tensor(M_f, N_f, over: S_f) -> (tensor(M, N, over: S))_f$ preserves degrees, yielding
    a map
    $
      phi_f: tensor(M_((f)), N_((f)), over: S_((f))) ->
      (tensor(M, N, over: S))_((f)), quad
      m/f^(d_1) times.o n/f^(d_2) mapsto.long (m times.o n)/f^(d_1+d_2)
    $
    for $m in M_(d_1)$ and $n in N_(d_2)$. It remains to show that $phi_f$ is
    an isomorphism.

    - *Surjectivity.* If $(m times.o n)/f^d in (tensor(M, N, over: S))_((f))$,
      then $deg(m times.o n) = d$, say
      $m times.o n in tensor(M_(d_1), N_(d_2), over: S)$ with $d_1 + d_2 = d$.
      Then $m/f^(d_1) times.o n/f^(d_2)$ maps to $(m times.o n)/f^d$.
    - *Injectivity.* Suppose $m/f^(d_1) times.o n/f^(d_2)$ maps to $0$.
      Then $f^r (m times.o n) = 0$ in $tensor(M, N, over: S)$ for some $r > 0$.
      Viewing $S_((f))$ as an $S$-algebra via
      $s in S_d mapsto s/f^d$, we get a canonical homomorphism
      $psi_f: tensor(M, N, over: S) -> tensor(M_((f)), N_((f)), over: S_((f)))$. Hence
      $
        m/f^(d_1) times.o n/f^(d_2)
        = (f^r m)/f^(r+d_1) times.o n/f^(d_2)
        = psi_f (f^r m times.o n)
        = 0,
      $
      so $phi_f$ is injective.

  + By _(2.5b)_, $D_+(f) simeq ops.spec S_((f))$ is affine. It suffices to show
    the desired isomorphism on every $D_+(f)$ with $f in S_+$. Since $S_1$
    generates $S_+$ over $S_0$, it is enough to check $f in S_1$:
    $
      (tensor(M, N, over: S))^tilde|_(D_+(f))
      isoBy("(5.11b)") ((tensor(M, N, over: S))_((f)))^tilde
      isoBy("(a)") (tensor(M_((f)), N_((f)), over: S_((f))))^tilde
      isoBy("(5.2b)") tensor(tildeOf(M_((f))), tildeOf(N_((f))), over: tildeOf(S_((f))))
      isoBy("(5.11b)") tensor(tildeOf(M)|_(D_+(f)), tildeOf(N)|_(D_+(f)), over: shf.o_X|_(D_+(f))).
    $

  + The sets ${D_+(g): g in phi(S_+)}$ form an open affine cover of $U$, and
    $D_+(g) simeq ops.spec T_((g))$ is affine. For $g := phi(h)$,
    $
      (tensor(M, T, over: S))^tilde|_(D_+(g))
      isoBy("(5.11b)") ((tensor(M, T, over: S))_((g)))^tilde
      simeq (tensor(M_((h)), T_((g)), over: S_((h))))^tilde
      isoBy("(5.2e)") f^ast (tildeOf(M_((h))))
      isoBy("(5.11b)") f^ast (tildeOf(M)|_(D_+(h))).
    $

  + Similarly, for every $h in S_+$,
    $
      f_ast (tildeOf(N)|_U)|_(D_+(h))
      = f_ast (tildeOf(N)|_(D_+(phi(h))))
      isoBy("(5.11b)") f_ast (tildeOf(N_((phi(h)))))
      isoBy("(5.2d)") (attach(N_((phi(h))), bl: S_((h))))^tilde
      = ((attach(N, bl: S))_((h)))^tilde
      isoBy("(5.11b)") (attach(N, bl: S))^tilde|_(D_+(h)).
    $
]

// Hartshorne II.5, Definition D6
#definition(title: "Twisted Sheaf")[
  Fix a graded ring $S$ and let $X = ops.proj S$. Suppose $n in ZZ$.

  - The sheaf $shf.o_X (n) := tildeOf(S(n))$, where
    $S(n) := bigOPlus(S_d, d >= n)$, is called the *twisting sheaf of Serre*
    when $n = 1$.
  - For any $shf.f in cat.mod(shf.o_X)$, denote
    $shf.f (n) := tensor(shf.f, shf.o_X (n), over: shf.o_X)$.
]

// Hartshorne II.5, Proposition 5.12
#proposition(number: 5.12)[
  Fix a graded ring $S$ generated by $S_1$ as an $S_0$-algebra, and let
  $X = ops.proj S$.

  #set enum(numbering: "a)", spacing: 1em)

  + The sheaf $shf.o_X (n)$ is an invertible sheaf on $X$ for every
    $n in ZZ$.
  + For any $M in cat.gr cat.mod(S)$, $tildeOf(M)(n) simeq tildeOf(M(n))$. Further,
    $tensor(shf.o_X (n), shf.o_X (m), over: shf.o_X) simeq shf.o_X (n+m)$.
  + Let $T$, $phi$, and $f$ be as in _(5.A)_. Then
    $f^ast (shf.o_X (n)) simeq shf.o_Y (n)|_U$ and
    $f_ast (shf.o_Y (n)|_U) simeq (f_ast (shf.o_Y|_U))(n)$.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + The sets ${D_+(f): f in S_1}$ cover $X$. Given $f in S_1$,
    $
      shf.o_X (n)|_(D_+(f))
      = tildeOf(S(n))|_(D_+(f))
      = tildeOf(S(n)_((f))).
    $
    The module $S(n)_((f))$ is free of rank $1$ over $S_((f))$, with canonical
    isomorphism
    $
      S_((f)) isolongto S(n)_((f)), quad
      a/f^d mapsto.long f^(n-d) a in S_(n-d) dot S_d subset S_n = S(n)_0.
    $
    Hence $shf.o_X (n)|_(D_+(f)) simeq tildeOf(S_((f))) simeq shf.o_X|_(D_+(f))$ is
    free of rank $1$, so $shf.o_X (n)$ is locally free of rank $1$, i.e. invertible.

  + For the first isomorphism,
    $
      tildeOf(M)(n)
      eqBy("Def.") tensor(tildeOf(M), shf.o_X (n), over: shf.o_X)
      = tensor(tildeOf(M), tildeOf(S(n)), over: tildeOf(S))
      isoBy("(5.Ab)") (tensor(M, S(n), over: S))^tilde
      simeq tildeOf(M(n)).
    $
    For the second,
    $
      tensor(shf.o_X (n), shf.o_X (m), over: shf.o_X) & simeq tensor(tildeOf(S(n)), tildeOf(S(m)), over: tildeOf(S))
                                                        isoBy("(5.Ab)") (tensor(S(n), S(m), over: S))^tilde
                                                        = tildeOf(S(n+m)) \
                                                      & = shf.o_X (n+m).
    $

  + First,
    $
      f^ast (shf.o_X (n))
      = f^ast (tildeOf(S(n)))
      isoBy("(5.Ac)") (tensor(S(n), T, over: S))^tilde|_U
      = tildeOf(T(n))|_U
      eqBy("(b)") shf.o_Y (n)|_U.
    $
    Also,
    $
      f_ast (shf.o_Y (n)|_U) & = f_ast (tildeOf(T(n))|_U)
                               isoBy("(5.Ad)") (attach(T(n), bl: S))^tilde
                               eqBy("(b)") tildeOf(attach(T, bl: S))(n)
                               isoBy("(5.Ad)") (f_ast (tildeOf(T)|_U))(n) \
                             & = (f_ast (shf.o_Y|_U))(n).
    $
]

#proposition(
  number: "5.B",
  // number: 5.B
)[
  The twisting functor $shf.f mapsto shf.f (n)$ is exact on $cat.mod(shf.o_X)$ for every
  $n in ZZ$, where $X = ops.proj S$ and $S$ is generated by $S_1$ as an
  $S_0$-algebra.
]

#proof[
  Fix $n in ZZ$. Suppose $0 -> shf.f' -> shf.f -> shf.f'' -> 0$ is a short exact
  sequence of $shf.o_X$-modules. We show that
  $0 -> shf.f'(n) -> shf.f (n) -> shf.f''(n) -> 0$ is exact.

  - For each $P in X$, the sequence $0 -> shf.f'_P -> shf.f_P -> shf.f''_P -> 0$ of
    stalks is exact. Since
    $- tensor_(shf.o_(X,P)) shf.o_X (n)_P$ is right exact, we get the exact
    sequence $shf.f'(n)_P -> shf.f (n)_P -> shf.f''(n)_P -> 0$. Thus
    $shf.f'(n) -> shf.f (n) -> shf.f''(n) -> 0$ is exact.
  - It remains to show $shf.f'(n) -> shf.f (n)$ is injective. For each $f in S_1$,
    $shf.o_X (n)|_(D_+(f)) simeq shf.o_X|_(D_+(f))$ is free by _(5.12a)_, so
    $shf.o_X (n)(D_+(f))$ is a flat $shf.o_X (D_+(f))$-module. Hence
    $
      shf.f'(n)(D_+(f)) simeq tensor(shf.f', shf.o_X (D_+(f)), over: shf.o_X)
      -> tensor(shf.f, shf.o_X (D_+(f)), over: shf.o_X) simeq shf.f (n)(D_+(f))
    $
    is injective as a presheaf map, hence as a sheaf map by _[1.4a]_. Since
    the $f in S_1$ generate $S$ over $S_0$, this gives the injection
    $shf.f'(n) -> shf.f (n)$.
]

#remark[
  The twisting operation above allows us to define a graded $shf.o_X$-module on
  $X = ops.proj S$.
]

// Hartshorne II.5, Definition D7
#definition(number: none)[
  Fix a graded ring $S$, let $X = ops.proj S$, and let $shf.f in cat.mod(shf.o_X)$. We define
  the _graded $S$-module associated_ to $shf.f$ as the group
  $Gamma_ast (shf.f) := bigOPlus(Gamma(X, shf.f (n)), n in ZZ)$. It has a graded
  $S$-module structure as follows. If $s in S_d$, then $s$ determines a global
  section $s in Gamma(X, shf.o_X (d))$. For $t in Gamma(X, shf.f (n))$, define
  $s dot t in Gamma(X, shf.f (n+d))$ by taking the tensor product
  $s times.o t$ via the natural isomorphism
  $tensor(shf.f (n), shf.o_X (d), over: shf.o_X) simeq shf.f (n+d)$.
]

// Hartshorne II.5, Proposition 5.13
#proposition(number: 5.13)[
  Suppose $S = A[x_0, dots.c, x_r]$ with $r >= 1$, and let
  $X = ops.proj S = sch.p_A^r$. Then $Gamma_ast (shf.o_X) simeq S$.
]

#proof[
  - Cover $X$ by ${D_+(x_i)}_(i=0)^r$. By the sheaf property, giving
    $t in Gamma(X, shf.o_X (n))$ is equivalent to giving
    $t_i in Gamma(D_+(x_i), shf.o_X (n))$ such that
    $t_i|_(D_+(x_i x_j)) = t_j|_(D_+(x_i x_j))$ for every $i,j$.
  - If $f in S_d$ with $d > 0$, then
    $S(n d)_((f)) = (S(n d)_f)_0 = (S_f (n))_0 = (S_f)_(n d)$. In particular,
    $S(n)_((x_i)) = (S_(x_i))_n$. Hence
    $shf.o_X (n)|_(D_+(x_i)) = tildeOf(S(n))|_(D_+(x_i))
    = tildeOf(S(n)_((x_i))) = tildeOf((S_(x_i))_n)$, and
    $
      t_i in Gamma(D_+(x_i), shf.o_X (n))
      = Gamma(ops.spec S_((x_i)), tildeOf((S_(x_i))_n))
      eqBy("(5.1d)") (S_(x_i))_n subset S_(x_i).
    $
    Similarly, $t_i|_j in (S_(x_i x_j))_n subset S_(x_i x_j)$.
  - Summing over all $n in ZZ$,
    $
      Gamma_ast (shf.o_X) & = bigOPlus(Gamma(X, shf.o_X (n)), n in ZZ) \
                          & = { (t_0, dots.c, t_r) : t_i in S_(x_i) text(" with ")
                              t_i|_j = t_j|_i text(" for every ") i,j }.
    $
  - Since each $x_i$ is not a zero divisor of $S = A[x_0, dots.c, x_r]$, the
    localization maps
    $S -> S_(x_i)$ and $S_(x_i) -> S_(x_i x_j)$ are injective. Thus all these
    rings are subrings of $S' := S_(x_0 dots.c x_r)$, and
    $Gamma_ast (shf.o_X) = inter_(i=0)^r S_(x_i) subset S'$.
  - Every homogeneous element $g in S'$ can be written as
    $g := x_0^(d_0) dots.c x_r^(d_r) f(x_0, dots.c, x_r)$ for some
    $d_k in ZZ$ and $f in S^h$ with $x_k divides.not f$ for every $k$.
    Then $g in S_(x_i)$ iff $d_k >= 0$ for every $k != i$. Therefore
    $
      g in Gamma_ast (shf.o_X) & arrow.l.r.double.long g in S_(x_i) text(" for all ") 0 lt.eq i lt.eq r \
                               & arrow.l.r.double.long d_i >= 0 text(" for all ") 0 lt.eq i lt.eq r \
                               & arrow.l.r.double.long g in S.
    $
    Hence $Gamma_ast (shf.o_X) simeq S$.
]

// Hartshorne II.5, Lemma 5.14
#lemma(number: 5.14)[
  Fix a scheme $X$, let $shf.l$ be an invertible sheaf on $X$, let
  $f in Gamma(X, shf.l)$, let
  $X_f = { x in X : f_x in.not idl.m_x shf.l_x }$, and let $shf.f in cat.qcoh (X)$.

  #set enum(numbering: "a)", spacing: 1em)

  + Suppose $X$ is quasi-compact and $s in Gamma(X, shf.f)$ has
    $s|_(X_f) = 0$. Then $f^n s = 0$ in
    $Gamma(X, tensor(shf.f, shf.l^(times.o n), over: shf.o_X))$ for some $n > 0$.
  + Suppose further that $X$ has a finite open affine cover $U_i$ such that
    $shf.l|_(U_i)$ is free for each $i$ and $U_i inter U_j$ is quasi-compact for
    every $i,j$. Given $t in Gamma(X_f, shf.f)$, then $f^n t$ extends to a global
    section $s in Gamma(X, tensor(shf.f, shf.l^(times.o n), over: shf.o_X))$ for some
    $n > 0$.
]

#proof[
  - General settings:

    - Choose a finite open affine cover $U_i = ops.spec A_i$,
      $1 lt.eq i lt.eq r$, of $X$ such that each $shf.l|_(U_i)$ is free.
    - Since $shf.l$ is invertible, let
      $psi_i: shf.l|_(U_i) isoBy(cat.mod(shf.o_X)) shf.o_X|_(U_i) = shf.o_(U_i)$.
    - Since $shf.f in cat.qcoh (X)$, by _(5.4)_ we have
      $shf.f|_(U_i) simeq tildeOf(M)_i$ for some $M_i in cat.mod(A_i)$.
    - For each $i$, let
      $g_i := psi_(i,U_i) (f|_i) in Gamma(U_i, shf.o_(U_i)) = A_i$. Then
      $U_i inter X_f = D(g_i)$ by _[2.16a]_.

  - Proof of (a): For each $i$, consider
    $s|_i in Gamma(U_i, shf.f) = Gamma(ops.spec A_i, tildeOf(M)_i) = M_i$. Since
    $(s|_i)|_(X_f) = 0$ on $D(g_i)$, by _(5.3a)_ there is $n_i > 0$ such
    that $g_i^(n_i) s|_i = 0$ in $shf.f (U_i) = M_i$. Via the isomorphism
    $shf.f times.o shf.l^(times.o n)|_(U_i) simeq shf.f|_(U_i)$ induced by $psi_i$,
    this gives $(f^(n_i) s)|_i = 0$. Choose
    $n >= max{ n_i : 1 lt.eq i lt.eq r }$, so $f^n s = 0$ on $X$.

  - Proof of (b):

    - For each $i$, let $t|_i in shf.f (X_f inter U_i) = shf.f (D(g_i)) simeq
      (M_i)_(g_i)$. By localization, there is
      $tilde(t)_i in M_i = shf.f (U_i)$ such that
      $tilde(t)_i|_(X_f) = g_i^(n_i) t|_i$ for some $n_i > 0$. Choose
      $n >= max{ n_i : 1 lt.eq i lt.eq r }$; under the trivialization by
      $psi_i$, this says
      $tilde(t)_i|_(X_f) = psi_i (f^n|_i) dot t|_i$.
    - On $D(g_i g_j) = (U_i inter U_j) inter X_f$, the two sections
      $tilde(t)_i$ and $tilde(t)_j$ have the same restriction. Thus
      $s_(i j) := tilde(t)_i|_j - tilde(t)_j|_i in shf.f (U_i inter U_j)$
      satisfies $s_(i j)|_(X_f) = 0$. Since $U_i inter U_j$ is
      quasi-compact, by (a) there is $m_(i j) > 0$ such that
      $f^(m_(i j)) s_(i j) = 0$. Choose
      $m >= max{ m_(i j) : 1 lt.eq i,j lt.eq r }$. Then
      $f^m tilde(t)_i|_j = f^m tilde(t)_j|_i$.
    - Glue the sections ${f^m tilde(t)_i}_(i=1)^r$ on ${U_i}_(i=1)^r$ to
      obtain $s in Gamma(X, tensor(shf.f, shf.l^(times.o (n+m)), over: shf.o_X))$ with
      $s|_(X_f) = f^(n+m) t$.
]

// Hartshorne II.5, Remark 5.14.1
#remark(title: "5.14.1")[
  The hypotheses in Lemma 5.14(a),(b) hold when $X$ is noetherian, and also
  when $X$ is quasi-compact and separated: in the latter case finite affine
  covers exist and intersections of affine opens are affine, hence
  quasi-compact.
]

// Hartshorne II.5, Proposition 5.15
#proposition(number: 5.15)[
  Fix a graded ring $S$ finitely generated by $S_1$ as an $S_0$-algebra, and
  let $X = ops.proj S$. If $shf.f in cat.qcoh (X)$, then there is a natural isomorphism
  $beta: (Gamma_ast (shf.f))^tilde isolongto shf.f$.
]

#proof[
  #set enum(numbering: "I)", spacing: 1em)

  + Define $beta: (Gamma_ast (shf.f))^tilde -> shf.f$. Since
    $(Gamma_ast (shf.f))^tilde in cat.qcoh (X)$ and $X$ has an open affine cover
    $D_+(f) simeq ops.spec S_((f))$ with $f in S_1$, we have
    $
      (Gamma_ast (shf.f))^tilde|_(D_+(f)) & simeq (Gamma_ast (shf.f))_((f)) \
                                          & simeq bigOPlus(Gamma(X, shf.f (n))_((f)), n in ZZ) \
                                          & simeq bigOPlus(Gamma(D_+(f), shf.f|_(D_+(f)) (n))^tilde, n in ZZ) \
                                          & simeq (Gamma_ast (shf.f|_(D_+(f))))^tilde.
    $
    By _[5.3]_,
    $
      ops.hom((Gamma_ast (shf.f|_(D_+(f))))^tilde, shf.f|_(D_+(f)), over: cat.mod(shf.o_X|_(D_+(f)))) \
      simeq ops.hom(Gamma_ast (shf.f|_(D_+(f))), Gamma(D_+(f), shf.f|_(D_+(f))), over: cat.mod(S_((f)))).
    $
    Thus it suffices to define, for every $f in S_1$,
    $
      alpha_f: (Gamma_ast (shf.f))_((f)) -> Gamma(D_+(f), shf.f).
    $
    Define
    $m/f^d mapsto.long m times.o f^(-d) in
    Gamma(D_+(f), tensor(shf.f (d), shf.o_X (-d), over: shf.o_X)) = Gamma(D_+(f), shf.f)$
    for $d >= 0$ and $m in Gamma(X, shf.f (d))$.

  + We claim that $alpha_f$ is an $S_((f))$-module isomorphism.

    - Let $shf.l := shf.o_X (1)$. Then
      $f in S(1) = Gamma(X, tildeOf(S(1))) = Gamma(X, shf.l)$.
    - Write $S = S_0[f_0, dots.c, f_r]$ with $f_i in S_1$. Thus $X$ has a
      finite open affine cover $D_+(f_i) simeq ops.spec S_((f_i))$ for which each
      $shf.l|_(D_+(f_i))$ is free.
    - The intersections $D_+(f_i) inter D_+(f_j) = D_+(f_i f_j)$ are affine,
      hence quasi-compact.
    - $shf.l^(times.o n) = shf.o_X (1)^(times.o n) eqBy("(5.12b)") shf.o_X (n)$ for
      every $n in ZZ$.
    - *Injectivity.* If $m/f^d mapsto 0$, then by _(5.14a)_ there is $n > 0$
      such that $f^n m = 0$ in $Gamma(X, shf.f (n))$. Hence
      $m/f^d = f^n m/f^(n+d) = 0$ in $(Gamma_ast (shf.f))_((f))$.
    - *Surjectivity.* Given $t in Gamma(D_+(f), shf.f)$, by _(5.14b)_ there are
      $n > 0$ and $s in Gamma(X, tensor(shf.f, shf.l^(times.o n), over: shf.o_X)) =
      Gamma(X, shf.f (n))$ such that $s|_(D_+(f)) = f^n t$. Thus $s/f^n$ maps to
      $t$.
]

// Hartshorne II.5, Corollary 5.16
#corollary(number: 5.16)[
  Fix a ring $A$.

  #set enum(numbering: "a)", spacing: 1em)

  + If $Y$ is a closed subscheme of $sch.p_A^r$, then there is a homogeneous ideal
    $I lt.closed S = A[x_0, dots.c, x_r]$ such that $Y$ is the closed
    subscheme determined by $I$.
  + A scheme $Y$ over $ops.spec A$ is projective iff
    $Y simeq ops.proj S$ for some graded ring $S$ finitely generated by $S_1$ as an
    $S_0$-algebra with $S_0 = A$.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + Consider the closed immersion
    $Y morph(i, cat.sch) sch.p_A^r$. Let $shf.i_Y = ops.ker i^sharp lt.closed shf.o_X$ be the
    ideal sheaf of $Y$ on $X = sch.p_A^r$. From
    $0 -> shf.i_Y -> shf.o_X -> i_ast shf.o_Y -> 0$, exactness of twisting gives
    $0 -> shf.i_Y (n) -> shf.o_X (n) -> (i_ast shf.o_Y)(n) -> 0$ for every $n in ZZ$.
    Taking global sections and then direct sums yields
    $0 -> Gamma_ast (shf.i_Y) -> Gamma_ast (shf.o_X) -> Gamma_ast (i_ast shf.o_Y)$.
    Thus $I := Gamma_ast (shf.i_Y)$ is an ideal of
    $Gamma_ast (shf.o_X) isoBy("(5.13)") S$. By _[3.12]_, $I$ determines a closed
    subscheme of $X = ops.proj S$ with sheaf of ideals $tildeOf(I)$. Since
    $shf.i_Y in cat.qcoh (X)$ by _(5.9)_,
    $shf.i_Y isoBy("(5.15)") (Gamma_ast (shf.i_Y))^tilde = tildeOf(I)$.

  + For the forward direction, if $Y$ is projective over $ops.spec A$, then
    $Y -> ops.spec A$ factors through a closed immersion
    $Y -> sch.p_A^r -> ops.spec A$. By (a), $Y simeq ops.proj S\/I$ for a homogeneous ideal
    $I lt.closed S := A[x_0, dots.c, x_r]$. Let
    $I' := bigOPlus(I inter S_d, d > 0) subset S_+$. Then
    $(S\/I')_d = (S\/I)_d$ for $d > 0$ and $(S\/I')_0 = A$; in particular,
    $S\/I'$ is finitely generated by $(S\/I')_1$ over $A$. Thus by _[3.12]_,
    $Y simeq ops.proj S\/I simeq ops.proj S\/I'$.

    Conversely, for such a graded ring $S$, write
    $S simeq A[x_0, dots.c, x_r]\/I$. The quotient map
    $A[x_0, dots.c, x_r] -> S$ induces
    $Y = ops.proj S -> ops.proj A[x_0, dots.c, x_r] = sch.p_A^r$, a closed immersion by
    _[3.12a]_. Therefore $Y -> sch.p_A^r -> ops.spec A$ is projective.
]

// Hartshorne II.5, Definition D8
#definition(title: "Twisting Sheaf on $PP_Y^r$")[
  For any scheme $Y$, the *twisting sheaf* $shf.o (1)$ on $sch.p_Y^r$ is
  $g^ast (shf.o (1))$, where
  $g: sch.p_Y^r = sch.p_(ZZ)^r times_(ZZ) Y -> sch.p_(ZZ)^r$ is the
  natural map.
]

// Hartshorne II.5, Definition D9
#definition(number: none)[
  - *(Immersion).* A morphism $X morph(i, cat.sch) Z$ is an _immersion_ if $i$
    gives an isomorphism of $X$ with an open subscheme of a closed subscheme
    of $Z$, i.e. $i: X isolongto U -> Y -> Z$.
  - *(Very Ample Sheaf).* Let $X$ be a scheme over $Y$. An invertible sheaf
    $shf.l$ on $X$ is _very ample_ relative to $Y$ if there is an immersion
    $i: X -> sch.p_Y^r$ for some $r$ such that
    $i^ast (shf.o_(sch.p_Y^r) (1)) simeq shf.l$.
]

#remark[
  If $Y = ops.spec A$, then $shf.o (1)$ is just the $shf.o_X (1)$ defined on
  $X = sch.p_A^r = ops.proj A[x_0, dots.c, x_r]$ before, by _(5.12c)_.
]

// Hartshorne II.5, Remark 5.16.1
#remark[
  *Remark 5.16.1.* Let $Y$ be a Noetherian scheme. Then a $Y$-scheme $X$ is projective iff it
  is proper and there exists a very ample sheaf on $X$ relative to $Y$.
]

#proof[
  - If $f: X -> Y$ is projective, then $f$ is proper by _(4.9)_. By definition
    of projective morphism, there is a closed immersion
    $X -> sch.p_Y^r$ for some $r$ that factors through $f$. Then $i^ast (shf.o (1))$
    gives a very ample invertible sheaf on $X$ relative to $Y$.
  - Conversely, if $f: X -> Y$ is proper and $shf.l$ is a very ample invertible
    sheaf on $X$, then $shf.l simeq i^ast (shf.o (1))$ for some immersion
    $i: X -> sch.p_Y^r$. But $i(X)$ is closed by _[4.4]_, so $i$ is a closed
    immersion. Hence $f: X -> sch.p_Y^r -> Y$ is projective.
]

// Hartshorne II.5, Definition D10
#definition(number: none)[
  Fix $X in cat.sch$ and $shf.f in cat.mod(shf.o_X)$. We say $shf.f$ is _generated by global
  sections_ if there is a family of global sections ${s_i}_(i in I)$, where
  $s_i in Gamma(X, shf.f)$, such that for each $x in X$, the germs
  $(s_i)_x in shf.f_x$ generate the stalk $shf.f_x$ as an $shf.o_(X,x)$-module, i.e.
  $shf.f_x = shf.o_(X,x) spn { (s_i)_x : i in I }$.
]

#note-box(title: "Note")[
  $shf.f in cat.mod(shf.o_X)$ is generated by global sections iff $shf.f$ can be written
  as a quotient of a free $shf.o_X$-module.
]

#proof[
  Suppose $s_i in Gamma(X, shf.f)$ for $i in I$. Then
  $
    & shf.f text(" is generated by ") {s_i}_(i in I) \
    & arrow.l.r.double.long shf.f_x = shf.o_(X,x) spn { (s_i)_x : i in I } text(" for every ") x in X \
    & arrow.l.r.double.long shf.o_(X,x)^I morph(phi_x, #none) shf.f_x -> 0
      text(" is exact for every ") x in X \
    & arrow.l.r.double.long shf.o_X^I morph(phi, #none) shf.f -> 0 text(" is exact") \
    & arrow.l.r.double.long shf.f simeq shf.o_X^I \/ops.ker phi.
  $
]

// Hartshorne II.5, Theorem 5.17
#theorem(number: 5.17, title: "Serre")[
  Let $X$ be a projective scheme over a Noetherian ring $A$, let $shf.o_X (1)$ be
  a very ample invertible sheaf on $X$, and let $shf.f in cat.coh (X)$. Then there is
  $n_0 in ZZ$ such that for every $n >= n_0$, the sheaf $shf.f (n)$ can be
  generated by finitely many global sections.
]

#proof[
  - By definition of the very ample sheaf $shf.o_X (1)$, there is a closed
    immersion $i: X -> sch.p_A^r$ with $i^ast shf.o_(sch.p_A^r) (1) = shf.o_X (1)$. Then
    $i_ast shf.f in cat.coh (sch.p_A^r)$ by _[5.5c]_, and
    $i_ast (shf.f (n)) = (i_ast shf.f)(n)$ by _(5.12c)_. Also, $shf.f (n)$ is generated
    by global sections iff $i_ast (shf.f (n))$ is. Thus reduce to
    $X = sch.p_A^r = ops.proj S$ with $S := A[x_0, dots.c, x_r]$.
  - Cover $X$ by ${D_+(x_i)}_(i=0)^r$. For each $i$, write
    $B_i := A[x_0/x_i, dots.c, x_r/x_i]$. Since $shf.f in cat.coh (X)$,
    $shf.f|_(D_+(x_i)) simeq tildeOf(M)_i$ for some
    $M_i in fg(cat.mod(B_i))$, say $M_i := B_i spn {s_(i j)}_(j=1)^(n_i)$.
  - By _(5.14b)_, for large $n > 0$ there are sections
    $t_(i j) in Gamma(X, shf.f (n))$ with
    $x_i^n s_(i j) = t_(i j)|_(D_+(x_i))$. The hypotheses apply because
    $D_+(x_i) simeq ops.spec S_((x_i)) = ops.spec B_i$, $shf.f in cat.qcoh (X)$,
    $X_(x_i) = D_+(x_i)$, $shf.o_X (1)$ is invertible by _(5.12a)_, and
    $D_+(x_i) inter D_+(x_j) simeq ops.spec S_((x_i x_j))$ is affine.
  - Set $M_i' := M_i (n)$. Then
    $
      shf.f (n)|_(D_+(x_i))
      = tensor(shf.f, shf.o_X (n), over: shf.o_X)|_(D_+(x_i))
      simeq tensor(tildeOf(M)_i, tildeOf(B_i)(n), over: tildeOf(B_i))
      simeq tildeOf(M_i (n)) = tildeOf(M_i').
    $
    The map
    $x_i^n: shf.f -> shf.f (n), quad t mapsto.long t times.o x_i^n$
    gives an isomorphism $phi_i: M_i -> M_i (n) = M_i'$, with inverse induced
    by $x_i^(-n)$. Thus the sections $x_i^n s_(i j) = phi_i (s_(i j))$
    generate $M_i' = Gamma(D_+(x_i), shf.f (n))$. Therefore the global sections
    $t_(i j)$ generate $shf.f (n)$.
]

// Hartshorne II.5, Corollary 5.18
#corollary(number: 5.18)[
  Let $X$ be a projective scheme over a Noetherian ring $A$. Then every
  coherent sheaf $shf.f in cat.coh (X)$ can be written as a quotient of a sheaf $shf.e$,
  where $shf.e$ is a finite direct sum of twisted structure sheaves $shf.o_X (n_i)$.
]

#proof[
  By _(5.17)_, choose $n$ such that $shf.f (n)$ is generated by finitely many global
  sections. Then $bigOPlus(shf.o_X, i=1, top: N) -> shf.f (n) -> 0$ is exact by the
  note above. Since twisting is exact,
  $bigOPlus(shf.o_X (-n), i=1, top: N) -> shf.f -> 0$ is exact. Thus $shf.f$ is a
  quotient of a finite direct sum of twisted structure sheaves.
]

// Hartshorne II.5, Theorem 5.19
#theorem(number: 5.19)[
  Let $A in fg(cat.alg)_k$, let $X$ be a projective scheme over $A$, and let
  $shf.f in cat.coh (X)$. Then $Gamma(X, shf.f)$ is a finitely generated $A$-module. In
  particular, if $A = k$, then $Gamma(X, shf.f)$ is a finite-dimensional
  $k$-vector space.
]

#proof[
  *(I) Reduction.*

  - By _(5.16b)_, write $X = ops.proj S$, where $S$ is finitely generated by $S_1$
    over $S_0 = A$.
  - Set $M := Gamma_ast (shf.f) in cat.gr cat.mod(S)$. By _(5.15)_,
    $tildeOf(M) simeq shf.f$.
  - Since $shf.f in cat.coh (X)$, by _(5.17)_ the sheaf $shf.f (n)$ is generated by
    finitely many global sections for $n >> 0$, say
    $s_i in Gamma(X, shf.f (n))$, $1 lt.eq i lt.eq m$.
  - Let $M'$ be the $S$-submodule of $M$ generated by ${s_i}_(i=1)^m$; then
    $M' in fg(cat.mod(S))$. The exact sequence $0 -> M' -> M$ gives
    $0 -> tildeOf(M') -> tildeOf(M) = shf.f$, hence
    $0 -> tildeOf(M')(n) -> shf.f (n)$. Since $shf.f (n)$ is generated by the $s_i$,
    $tildeOf(M')(n) simeq shf.f (n)$. Twisting again yields
    $tildeOf(M') simeq shf.f$, so $shf.f$ corresponds to a finitely generated graded
    $S$-module.

  *(II)* It remains to show that if $M in fg(cat.mod(S))$, then
  $Gamma(X, tildeOf(M)) in fg(cat.mod(A))$.

  - Since $S_0 = A in fg(cat.alg)_k$, it is Noetherian. By _(3.F)_, $S$ is
    Noetherian. Since $M in cat.gr cat.mod(S)$ is finitely generated, by _(I,7.4a)_
    there is a filtration
    $0 = M^0 subset M^1 subset dots.c subset M^r = M$
    in $cat.gr cat.mod(S)$ such that
    $M^i \/ M^(i-1) simeq (S \/ idl.p_i)(n_i)$ for homogeneous primes
    $idl.p_i lt.closed S$.
  - This induces a filtration
    $0 = tildeOf(M)^0 subset tildeOf(M)^1 subset dots.c subset
    tildeOf(M)^r = tildeOf(M)$
    in $cat.mod(shf.o_X)$. Taking global sections preserves injectivity, so
    $
      0 = Gamma(X, tildeOf(M)^0) subset Gamma(X, tildeOf(M)^1) subset
      dots.c subset Gamma(X, tildeOf(M)^r) = Gamma(X, tildeOf(M))
    $
    in $cat.mod(A)$.
  - For each $i$,
    $
      0 -> Gamma(X, tildeOf(M)^(i-1)) -> Gamma(X, tildeOf(M)^i) ->
      Gamma(X, tildeOf(S \/ idl.p_i)(n_i)).
    $
    Hence the quotient is isomorphic to an $A$-submodule $N^i$ of
    $Gamma(X, tildeOf(S \/ idl.p_i)(n_i))$, giving
    $
      0 -> Gamma(X, tildeOf(M)^(i-1)) -> Gamma(X, tildeOf(M)^i) -> N^i -> 0.
    $
  - If each $Gamma(X, tildeOf(S \/ idl.p_i)(n_i))$ is finitely generated over $A$,
    then so is $N^i$ because $A$ is Noetherian. Inductively,
    $Gamma(X, tildeOf(M))$ is finitely generated over $A$.

  *(III)* It remains to handle the special case where $S$ is a graded integral
  domain, finitely generated by $S_1$ over $S_0 = A$, with
  $A in fg(cat.alg)_k$ an integral domain. We prove
  $Gamma(X, shf.o_X (n)) in fg(cat.mod(A))$ for every $n in ZZ$.

  - This applies to the integral domains $S \/ idl.p_i$ above, and
    $(S \/ idl.p_i)_0 = A \/ (idl.p_i inter A)$ is again a finitely generated
    $k$-algebra and an integral domain.
  - Write $S_1 := A spn {x_j : 0 lt.eq j lt.eq r}$. For every
    $n in ZZ$, the map $S(n) -> S(n+1)$ given by multiplication by
    $x_0$ is injective. Applying $Gamma(X, -)$, it suffices to prove
    $Gamma(X, shf.o_X (n)) in fg(cat.mod(A))$ for all large $n >> 0$.
  - Put $S' := bigOPlus(Gamma(X, shf.o_X (n)), n >= 0)$. Then
    $S subset S' subset inter_(i=0)^r S_(x_i)$. Indeed, every element of
    $S_0$ is a global section of $shf.o_X$, so $S_n subset Gamma(X, shf.o_X (n))$.
    Also, each $D_+(x_i)$ is affine, so
    $
      Gamma(X, shf.o_X (n)) -> Gamma(D_+(x_i), shf.o_X (n)) = (S_(x_i))_n subset S_(x_i).
    $
  - *Claim.* $S'$ is integral over $S$.

    Let $overline(S)$ be the integral closure of $S$ in $K = ops.frac S$; we show
    $S' subset overline(S)$. Since $S' = bigOPlus(S'_d, d >= 0)$, it suffices
    to show that any $s' in S'_d$ is integral over $S$. Since
    $s' in inter_(i=0)^r S_(x_i)$, for each $i$ there is $n_i > 0$ with
    $x_i^(n_i) s' in S$. Choose $n$ such that $x_i^n s' in S$ for all $i$.
    Since $S_1$ is generated by the $x_i$, for $n >> 0$ we may assume
    $y s' in S$ for every $y in S_n$. Inductively,
    $y (s')^q in S_(>= n)$ for every $q >= 1$ and $y in S_(>= n)$. Taking
    $y = x_0^n$, we get $(s')^q in (1 / x_0^n) S$ for every $q >= 1$. Thus
    $S[s'] subset (1 / x_0^n) S$, a finitely generated $S$-submodule of
    $ops.frac S$. By _(AM, 5.1)_, $s'$ is integral over $S$.

  - Since $S in fg(cat.alg)_k$ is an integral domain, taking $L = K = ops.frac S$ in
    _(I, 3.9)_ gives $overline(S) in fg(cat.mod(S))$. Since $S' subset
    overline(S)$, also $S' in fg(cat.mod(S))$, whence
    $Gamma(X, shf.o_X (n)) = S'_n in fg(cat.mod(A))$ for every $n >= 0$.
]

// Hartshorne II.5, Remark 5.19.1
#remark(title: "5.19.1")[
  The proof of Theorem 5.19 generalizes the proof of I.3.4(a). A second
  proof using cohomology appears in III.5.2.1.
]

// Hartshorne II.5, Remark 5.19.2
#remark(title: "5.19.2")[
  The finite-type hypothesis on $A$ is used only to invoke the finiteness of
  integral closure. It is enough to assume that the integral closure of each
  finitely generated integral $A$-algebra in a finite field extension of its
  fraction field is finite over that algebra.
]

// Hartshorne II.5, Corollary 5.20
#corollary(number: "5.20")[
  Let $f: X -> Y$ be a projective morphism of schemes of finite type over $k$.
  If $shf.f in cat.coh (X)$, then $f_ast shf.f in cat.coh (Y)$.
]

#proof[
  - As in _(5.8c)_, the question is local on $Y$, so assume
    $Y = ops.spec A$ is affine. Since $Y$ is of finite type over $k$,
    $A in fg(cat.alg)_k$.
  - By _(5.16b)_, write $X = ops.proj S$, where $S$ is finitely generated by
    $S_1$ over $S_0 = A$. Since $S_0 = A$ is Noetherian, so is $S$ by
    _(3.F)_, hence $X = ops.proj S$ is Noetherian by _(3.H)_. By _(5.8c)_,
    $f_ast shf.f in cat.qcoh (Y)$, and therefore
    $
      f_ast shf.f eqBy("(5.5)") tildeOf(Gamma(Y, f_ast shf.f))
      eqBy("Def. of f_ast") tildeOf(Gamma(X, shf.f)).
    $
  - Since $shf.f in cat.coh (X)$, by _(5.19)_ we have
    $Gamma(X, shf.f) in fg(cat.mod(A))$. Therefore $f_ast shf.f in cat.coh (Y)$.
]

=== Exercises

#exercise(title: "Exercise 5.3")[
  Let $X = ops.spec A$ be an affine scheme. Show that the functors $tildeOf(dot)$
  and $Gamma(X, dot)$ are adjoint, i.e. for any $M in cat.mod(A)$ and any
  $shf.f in cat.mod(shf.o_X)$, there is a natural isomorphism
  $
    ops.hom(M, Gamma(X, shf.f), over: cat.mod(A)) simeq ops.hom(tildeOf(M), shf.f, over: cat.mod(shf.o_X)).
  $
]

#exercise(title: "Exercise 5.3*")[
  Let $X = ops.proj S$, where $S$ is a graded ring finitely generated by $S_1$ as
  an $S_0$-algebra. Show that the functors $tildeOf(dot)$ and $Gamma_ast (-)$
  are adjoint, i.e. for any $M in cat.gr cat.mod(S)$ and any $shf.f in cat.mod(shf.o_X)$, there
  is a natural isomorphism
  $
    ops.hom(M, Gamma_ast (shf.f), over: cat.mod(S)) simeq ops.hom(tildeOf(M), shf.f, over: cat.mod(shf.o_X)).
  $
]
