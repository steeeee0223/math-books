#import "@preview/theorion:0.4.0": *
#show: show-theorion
#import "../defs.typ": *

=== Exercises

// Hartshorne II.5, Exercise 5.1
#exercise(title: "Exercise 5.1 (Duality for Locally Free Sheaves)")[
  Let $shf.e$ be locally free of finite rank and put
  $shf.e^or=shf.hom_(shf.o_X) (shf.e,shf.o_X)$.

  + Show $(shf.e^or)^or simeq shf.e$.
  + Show $shf.hom_(shf.o_X) (shf.e,shf.f) simeq tensor(shf.e^or, shf.f, over: shf.o_X)$.
  + Establish the tensor–Hom adjunction
    $ops.hom(tensor(shf.e, shf.f), shf.g, over: shf.o_X)
    simeq ops.hom(shf.f, shf.hom (shf.e,shf.g), over: shf.o_X)$.
  + Prove the projection formula
    $f_*tensor(shf.f, f^*shf.e, over: shf.o_X)
    simeq tensor(f_*shf.f, shf.e, over: shf.o_Y)$.
]

#proof[
  Every isomorphism below is the canonical one; this matters because it lets
  the affine calculations glue.

  #set enum(numbering: "a)", spacing: 1em)

  + There is an evaluation morphism
    $
      shf.e -> (shf.e^or)^or,
      quad e mapsto (lambda mapsto lambda(e)).
    $
    On an open set $U$ on which $shf.e|_U simeq shf.o_U^r$, this is the usual
    map from a finite free module to its double dual.  If
    $e_1,dots.c,e_r$ is the standard basis and $e_1^or,dots.c,e_r^or$ its
    dual basis, its inverse sends a functional $Phi$ to
    $sum_(i=1)^r Phi(e_i^or)e_i$.  Hence evaluation is an isomorphism on a
    cover of $X$, and therefore is an isomorphism of sheaves:
    $(shf.e^or)^or simeq shf.e$.

  + Define
    $
      alpha:tensor(shf.e^or, shf.f, over: shf.o_X)
      -> shf.hom_(shf.o_X)(shf.e,shf.f)
    $
    by $alpha(tensor(lambda, s))(e)=lambda(e)s$.  This construction commutes
    with restriction.  On an open set where $shf.e simeq shf.o_X^r$, it is
    the evident isomorphism
    $
      tensor((shf.o_X^r)^or, shf.f, over: shf.o_X) simeq shf.f^r
      simeq shf.hom (shf.o_X^r,shf.f).
    $
    Thus $alpha$ is locally, hence globally, an isomorphism.

  + A morphism $u:tensor(shf.e, shf.f, over: shf.o_X) -> shf.g$ determines
    $
      tildeOf(u):shf.f -> shf.hom (shf.e,shf.g),
      quad tildeOf(u)(s)(e)=u(tensor(e, s)).
    $
    Conversely, from $v:shf.f->shf.hom (shf.e,shf.g)$ define
    $u_v(tensor(e, s))=v(s)(e)$.  Bilinearity gives a morphism from the tensor
    product, and the two constructions are inverse and natural.  Therefore
    $
      ops.hom(tensor(shf.e, shf.f, over: shf.o_X), shf.g)
      simeq ops.hom(shf.f, shf.hom (shf.e,shf.g)).
    $

  + Assume, as in the exercise, that $shf.e$ is locally free of finite rank.
    There is a natural morphism
    $
      theta:tensor(f_*shf.f, shf.e, over: shf.o_Y)
      -> f_*tensor(shf.f, f^*shf.e, over: shf.o_X),
      quad tensor(s, e) mapsto tensor(s, f^*e).
    $
    It is enough to check $theta$ on an open cover of $Y$.  If
    $shf.e|_V simeq shf.o_V^r$, then
    $
         tensor(f_*shf.f, shf.e, over: shf.o_Y)|_V & simeq (f_*shf.f|_V)^r, \
      f_*tensor(shf.f, f^*shf.e, over: shf.o_X)|_V & simeq f_*((shf.f|_(f^(-1)V))^r)
                                                     simeq (f_*shf.f|_V)^r.
    $
    The last equality follows directly from the definition of pushforward,
    since sections commute with finite direct sums.  Under these
    identifications $theta|_V$ is the identity.  Hence $theta$ is an
    isomorphism, which gives the displayed projection formula after taking
    its inverse if necessary.
]

// Hartshorne II.5, Exercise 5.2
#exercise(title: "Exercise 5.2")[
  For a DVR $R$ with fraction field $K$ and $X=ops.spec R$:

  + show an $shf.o_X$-module is equivalent to an $R$-module $M$, a $K$-vector
    space $L$, and a map $tensor(M, K, over: R)->L$;
  + show it is quasi-coherent exactly when that map is an isomorphism.
]

#proof[
  Let $eta=(0)$ be the generic point and let $x=(pi)$ be the closed point,
  where $pi$ is a uniformizer.  The only open subsets of $X$ are
  $nothing$, ${eta}=D(pi)$, and $X$.  Moreover
  $
    shf.o_X (X)=R, quad shf.o_X ({eta})=K,
  $
  and the restriction map is the inclusion $R->K$.

  An $shf.o_X$-module $shf.f$ therefore gives
  $
    M=shf.f (X), quad L=shf.f ({eta}),
  $
  where $M$ is an $R$-module, $L$ is a $K$-vector space, and restriction is
  an $R$-linear map $rho:M->L$.  By the universal property of localization,
  $rho$ is equivalently a $K$-linear map
  $
    bar(rho):tensor(M, K, over: R) -> L,
    quad tensor(m, a) mapsto a rho(m).
  $
  Conversely, such data define an $shf.o_X$-module by assigning $M$ to
  $X$, $L$ to ${eta}$, zero to the empty set, and using the associated map
  $M->L$ for restriction.  There are no other nontrivial covers, so the
  sheaf axiom is automatic.  These constructions are inverse, also on
  morphisms.

  If $shf.f$ is quasi-coherent, Proposition 5.1 gives
  $shf.f simeq tildeOf(M)$, where $M=Gamma(X, shf.f)$.  On $D(pi)={eta}$,
  $
    tildeOf(M)({eta})=M_pi=tensor(M, K, over: R).
  $
  Thus $bar(rho)$ is an isomorphism.  Conversely, if $bar(rho)$ is an
  isomorphism, the identity on $M$ and $bar(rho)$ on ${eta}$ give an
  isomorphism $tildeOf(M) simeq shf.f$.  Hence $shf.f$ is quasi-coherent.
]

// Hartshorne II.5, Exercise 5.3
#exercise(title: "Exercise 5.3")[
  For $X=ops.spec A$, prove the adjunction
  $
    ops.hom(M, Gamma(X, shf.f), over: A) simeq
    ops.hom(tildeOf(M), shf.f, over: shf.o_X).
  $
]

#proof[
  Given $u:M->Gamma(X, shf.f)$, define a morphism
  $tildeOf(u):tildeOf(M)->shf.f$ as follows.  On a distinguished open
  $D(a)$, a section of $tildeOf(M)$ is a fraction $m/a^n$, and we put
  $
    tildeOf(u)_(D(a))(m/a^n)
    = a^(-n) u(m)|_(D(a)).
  $
  This is well-defined by the universal property of localization, is
  compatible with restriction, and therefore defines a sheaf morphism
  because distinguished opens form a basis.

  Conversely, a morphism $v:tildeOf(M)->shf.f$ gives on global sections an
  $A$-linear map
  $
    M isoBy("5.1d") Gamma(X, tildeOf(M))
    morph(Gamma(X, v), cat.mod(A)) Gamma(X, shf.f).
  $
  Starting with $u$ and taking global sections recovers $u$.  Starting with
  $v$, the preceding formula recovers $v$ on every $D(a)$, hence on all
  opens.  The two constructions are natural, giving the required
  bijection.
]

// Hartshorne II.5, Exercise 5.4
#exercise(title: "Exercise 5.4")[
  Show an $shf.o_X$-module is quasi-coherent exactly when locally it is a
  cokernel of a morphism of free sheaves. If $X$ is noetherian, show it is
  coherent exactly when locally it is such a cokernel with both free sheaves
  of finite rank.
]

#proof[
  First suppose that $shf.f$ is quasi-coherent.  On a suitable affine open
  $U=ops.spec A$ we may write $shf.f|_U simeq tildeOf(M)$.  Choose generators
  $(m_i)_(i in I)$ of $M$.  They give a surjection
  $
    bigOPlus(A, i in I) -> M.
  $
  Choose generators $(r_j)_(j in J)$ of its kernel.  We obtain an exact
  sequence
  $
    bigOPlus(A, j in J) -> bigOPlus(A, i in I) -> M -> 0.
  $
  The functor $N mapsto tildeOf(N)$ is exact by Proposition 5.2(a), and it
  takes a free module to the corresponding free sheaf.  Hence on $U$,
  $
    bigOPlus(shf.o_U, j in J) -> bigOPlus(shf.o_U, i in I)
    -> shf.f|_U -> 0
  $
  is exact.  Thus $shf.f$ is locally a cokernel of a map of free sheaves.

  Conversely, suppose on an affine open $U=ops.spec A$ that
  $shf.f|_U$ is the cokernel of a morphism
  $
    bigOPlus(shf.o_U, j in J) -> bigOPlus(shf.o_U, i in I).
  $
  By the full faithfulness in Proposition 5.2(a), this morphism comes from
  an $A$-linear map
  $bigOPlus(A, j in J)->bigOPlus(A, i in I)$.  Exactness of the tilde functor
  identifies its sheaf cokernel with the tilde of the module cokernel.
  Hence $shf.f|_U$ is quasi-coherent, and so is $shf.f$.

  Now assume $X$ is noetherian.  If $shf.f$ is coherent, on an affine open
  $U=ops.spec A$ it has the form $tildeOf(M)$ with $A$ noetherian and $M$
  finite.  Choose a surjection $A^r->M$.  Its kernel is a submodule of the
  finite $A$-module $A^r$, hence is finite; choosing finitely many generators
  gives an exact sequence
  $
    A^s -> A^r -> M -> 0.
  $
  Sheafification gives the required finite-free cokernel presentation.
  Conversely, the cokernel of $shf.o_U^s->shf.o_U^r$ is the tilde of the
  cokernel of $A^s->A^r$, which is a finite $A$-module.  It is therefore
  coherent.  This proves both equivalences.
]

// Hartshorne II.5, Exercise 5.5
#exercise(title: "Exercise 5.5")[
  For $f:X->Y$:

  + give an example where coherent $shf.f$ has noncoherent $f_*shf.f$, even for
    varieties over a field;
  + show every closed immersion is finite;
  + if $f$ is finite between noetherian schemes, show $f_*$ preserves
    coherent sheaves.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + Let $Y=bb(A)^1_k=ops.spec k[t]$, let
    $U=D(t)=ops.spec k[t,t^(-1)]$, and let $j:U inclusion(#none, cat.sch) Y$
    be the open immersion.  The sheaf $shf.o_U$ is coherent.  Since $j$ is a
    quasi-compact open immersion, Proposition 5.2(d), applied on $Y$, gives
    $
      j_*shf.o_U simeq tildeOf(k[t,t^(-1)])
    $
    with the Laurent polynomial ring regarded as a $k[t]$-module.  This
    module is not finite: if finitely many Laurent polynomials generated it,
    their pole orders at $t=0$ would be bounded, whereas the elements
    $t^(-n)$ have arbitrarily large pole order.  Thus $j_*shf.o_U$ is not
    coherent.  Both $U$ and $Y$ are varieties over $k$.

  + Finiteness is local on the target.  This is exactly the target-local
    affine reduction developed in the locality calculus: finite ring maps
    are preserved by target localization and glue across finite
    distinguished covers.  We may therefore take $Y=ops.spec A$.

    A closed immersion into an affine scheme is the closed subscheme defined
    by a quasi-coherent ideal sheaf; hence it has the form
    $
      X=ops.spec(A/idl.a) -> ops.spec A.
    $
    The $A$-algebra $A/idl.a$ is generated as an $A$-module by $1$.
    Therefore the morphism is finite.  Target locality proves the assertion
    for every closed immersion.

  + Let $V=ops.spec A subset.eq Y$ be affine.  Because $f$ is finite,
    $f^(-1)(V)=ops.spec B$ is affine and $B$ is a finite $A$-module.  Write
    $
      shf.f|_(f^(-1)(V)) simeq tildeOf(M),
    $
    where $M$ is a finite $B$-module.  Proposition 5.2(d) identifies
    $
      (f_*shf.f)|_V simeq tildeOf(attach(M, bl: A)).
    $
    If $b_1,dots.c,b_r$ generate $B$ over $A$ and
    $m_1,dots.c,m_s$ generate $M$ over $B$, then the finitely many elements
    $b_i m_j$ generate $M$ over $A$.  Thus $M$ is finite as an $A$-module,
    so $(f_*shf.f)|_V$ is coherent.  The affine opens $V$ cover $Y$;
    therefore $f_*shf.f$ is coherent.
]

// Hartshorne II.5, Exercise 5.6
#exercise(title: "Exercise 5.6 (Support)")[
  + For $M$ over $A$, $X=ops.spec A$, and $m in M$, show
    $ops.supp m=V(ops.ann (m))$.
  + If $A$ is noetherian and $M$ finite, show
    $ops.supp tildeOf(M)=V(ops.ann (M))$.
  + Deduce that the support of a coherent sheaf on a noetherian scheme is
    closed.
  + For $idl.a subset.eq A$, identify sections supported on $V(idl.a)$ with
    $Gamma_idl.a (M)={m | idl.a^n m=0 text(" for some ") n}$.
  + Show subsheaves with support preserve quasi-coherence and coherence on a
    noetherian scheme.
]

// Hartshorne II.5, Exercise 5.7
#exercise(title: "Exercise 5.7")[
  Let $X$ be noetherian and $shf.f$ coherent.

  + If $shf.f_x$ is free, show $shf.f$ is free on a neighborhood of $x$.
  + Deduce $shf.f$ is locally free iff all stalks are free.
  + Show $shf.f$ is invertible iff some coherent $shf.g$ satisfies
    $tensor(shf.f, shf.g, over: shf.o_X) simeq shf.o_X$.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + Choose an affine neighborhood $U=ops.spec A$ of $x$.  Since $X$ is
    noetherian and $shf.f$ is coherent, we may write
    $shf.f|_U simeq tildeOf(M)$ with $A$ noetherian and $M$ finite.  Let
    $idl.p$ correspond to $x$.  By Proposition 5.1(b), the hypothesis says
    that $M_idl.p$ is a finite free $A_idl.p$-module, say of rank $r$.

    Choose $m_1,dots.c,m_r in M$ whose images form a basis of $M_idl.p$, and
    let
    $
      phi:A^r -> M, quad (a_i) mapsto sum_i a_i m_i.
    $
    The localization of $C=ops.coker(phi)$ at $idl.p$ is zero.  The module
    $C$ is finite, so a single element $a in.not idl.p$ annihilates all of a
    finite set of generators of $C$.  Hence $C_a=0$ and $phi_a$ is
    surjective.

    Put $K=ops.ker(phi)$.  Since $A$ is noetherian, $K subset.eq A^r$ is
    finite.  Also $K_idl.p=0$, because $phi_idl.p$ is an isomorphism.  Thus
    some $b in.not idl.p$ kills a finite set of generators of $K$, so
    $K_b=0$.  For $h=a b in.not idl.p$, the map
    $
      phi_h:A_h^r simeq M_h
    $
    is an isomorphism.  Consequently
    $shf.f|_(D(h)) simeq shf.o_(D(h))^r$, and $D(h)$ is the desired
    neighborhood of $x$.

  + If $shf.f$ is locally free, every stalk is the corresponding free module
    over the local ring.  Conversely, if every stalk is free, part (a)
    supplies, for every $x$, a neighborhood on which $shf.f$ is free.  These
    neighborhoods cover $X$, so $shf.f$ is locally free.

  + Suppose first that $shf.f$ is invertible.  It is locally free of rank
    one, hence coherent, and its dual $shf.g=shf.f^ast$ is also locally free
    of rank one and coherent.  The evaluation map
    $
      tensor(shf.f, shf.f^ast, over: shf.o_X) -> shf.o_X
    $
    is an isomorphism locally on every trivializing open, and hence globally.

    Conversely, suppose a coherent $shf.g$ satisfies
    $tensor(shf.f, shf.g, over: shf.o_X) simeq shf.o_X$.  At a point $x$, put
    $
      R=shf.o_(X,x), quad M=shf.f_x, quad N=shf.g_x.
    $
    Then $R$ is local, $M,N$ are finite, and
    $tensor(M, N, over: R) simeq R$.  After tensoring with the residue field $k(x)$,
    $
      tensor(M/frak(m)M, N/frak(m)N, over: k(x)) simeq k(x).
    $
    Both factors are nonzero finite-dimensional vector spaces, and the
    product of their dimensions is $1$; each therefore has dimension $1$.
    Choose $m in M$ and $n in N$ lifting bases.  Nakayama's lemma shows that
    $m$ and $n$ generate $M$ and $N$.

    The map $R->tensor(M, N, over: R)$ sending $1$ to $tensor(m, n)$ is
    surjective by Nakayama.  Composing with an isomorphism
    $tensor(M, N, over: R) simeq R$ gives a
    surjective endomorphism of the rank-one free module $R$, hence
    multiplication by a unit; it is injective.  If $a m=0$, then
    $a tensor(m, n)=0$, so $a=0$.  Thus $R->M$, $a mapsto a m$, is also
    injective, and it is already surjective.  Hence $M simeq R$.

    We have proved that every stalk $shf.f_x$ is free of rank one.  Part (b)
    makes $shf.f$ locally free; the rank is one on each resulting
    neighborhood.  Therefore $shf.f$ is invertible.
]

// Hartshorne II.5, Exercise 5.8
#exercise(title: "Exercise 5.8")[
  For coherent $shf.f$ on noetherian $X$, put
  $phi(x)=dim_(kappa(x)) (tensor(shf.f_x, kappa(x), over: shf.o_(X,x)))$.
  Using Nakayama, show:

  + $phi$ is upper semicontinuous;
  + if $shf.f$ is locally free and $X$ connected, $phi$ is constant;
  + if $X$ is reduced and $phi$ constant, $shf.f$ is locally free.
]

// Hartshorne II.5, Exercise 5.9
#exercise(title: "Exercise 5.9")[
  For $X=ops.proj S$ and graded $M$:

  + construct the natural graded map $M->Gamma_*(tildeOf(M))$;
  + under the stated finite-generation hypotheses, show it is an isomorphism
    in all sufficiently large degrees;
  + modulo equality in sufficiently large degrees, show quasi-finitely
    generated graded $S$-modules are equivalent to coherent sheaves on $X$.
]

// Hartshorne II.5, Exercise 5.10
#exercise(title: "Exercise 5.10 (Saturated Ideals)")[
  For $S=A[x_0,dots.c,x_r]$, define
  $bar(I)={s | text("for every ") i, x_i^n s in I text(" for some ") n}$.

  + Show $bar(I)$ is a homogeneous ideal.
  + Show two homogeneous ideals define the same closed subscheme of $ops.proj S$
    iff their saturations agree.
  + Show $Gamma_*(cal(I)_Y)$ is saturated and is the largest homogeneous
    ideal defining $Y$.
  + Deduce a bijection between saturated ideals and closed subschemes.
]

// Hartshorne II.5, Exercise 5.11
#exercise(title: "Exercise 5.11 (Cartesian Product of Graded Rings)")[
  For graded $S,T$ over $A$, put
  $S times_A T=bigOPlus(tensor(S_d, T_d, over: A), d>=0)$. Show
  $ops.proj (S times_A T) simeq ops.proj S times_A ops.proj T$ and identify its $shf.o (1)$
  with $tensor(p_1^*shf.o_X (1), p_2^*shf.o_Y (1), over: shf.o_(X times_A Y))$.
  Relate the induced embedding to
  the Segre embedding.
]

// Hartshorne II.5, Exercise 5.12
#exercise(title: "Exercise 5.12")[
  + Show the tensor product of two relatively very ample invertible sheaves
    is very ample, using Segre.
  + If $X->Y->Z$, $shf.l$ is very ample over $Y$, and $shf.m$ very ample over $Z$,
    show $tensor(shf.l, f^*shf.m, over: shf.o_X)$ is very ample over $Z$.
]

// Hartshorne II.5, Exercise 5.13
#exercise(title: "Exercise 5.13 (Veronese Construction)")[
  For $d>0$, put $S^((d))=bigOPlus(S_(n d), n>=0)$. Show
  $ops.proj S^((d)) simeq ops.proj S$ and that $shf.o (1)$ corresponds to $shf.o_X (d)$.
  Relate this to the $d$-uple embedding.
]

// Hartshorne II.5, Exercise 5.14
#exercise(title: "Exercise 5.14 (Projective Normality)")[
  Let connected normal $X subset.eq sch.p^r_k$.

  + If $S$ is its homogeneous coordinate ring and
    $S'=bigOPlus(Gamma(X, shf.o_X (n)), n>=0)$, show $S$ is a domain and $S'$ its
    integral closure.
  + Show $S_d=S'_d$ for all sufficiently large $d$.
  + Deduce a sufficiently high Veronese embedding is projectively normal.
  + Show $X$ is projectively normal iff it is normal and every restriction
    $Gamma(sch.p^r, shf.o (n))->Gamma(X, shf.o_X (n))$ is surjective for $n>=0$.
]

// Hartshorne II.5, Exercise 5.15
#exercise(title: "Exercise 5.15 (Extension of Coherent Sheaves)")[
  Let $X$ be noetherian, $U subset.eq X$ open, and $shf.f$ coherent on $U$.

  + On an affine noetherian scheme, show every quasi-coherent sheaf is the
    union of its coherent subsheaves.
  + Extend $shf.f$ coherently across $X-U$ first when $X$ is affine.
  + If $shf.f subset.eq shf.g|_U$ for quasi-coherent $shf.g$ on $X$, find a coherent
    $shf.f' subset.eq shf.g$ restricting to $shf.f$.
  + Extend this result affine-open by affine-open on general $X$.
  + Deduce every quasi-coherent sheaf on a noetherian scheme is the union of
    coherent subsheaves.
]

// Hartshorne II.5, Exercise 5.16
#exercise(title: "Exercise 5.16 (Tensor Operations)")[
  Define tensor, symmetric, and exterior algebras of an $shf.o_X$-module by
  sheafifying the corresponding presheaves.

  + Compute the ranks of $T^r (shf.f)$, $S^r (shf.f)$, and $Lambda^r shf.f$ when $shf.f$ is
    locally free of rank $n$.
  + Prove the perfect pairing
    $tensor(Lambda^r shf.f, Lambda^(n-r)shf.f, over: shf.o_X)->Lambda^n shf.f$.
  + For an exact sequence of locally free sheaves, construct the standard
    filtrations on symmetric and exterior powers and identify their graded
    pieces.
  + Show pullback commutes with all these tensor operations.
]

// Hartshorne II.5, Exercise 5.17
#exercise(title: "Exercise 5.17 (Affine Morphisms)")[
  A morphism is affine if inverse images of members of some affine cover are
  affine.

  + Show this then holds over every affine open; affine morphisms are
    quasi-compact and separated, and finite morphisms are affine.
  + For a quasi-coherent $shf.o_Y$-algebra $sch.a$, construct
    $ops.spec sch.a->Y$ by gluing the $ops.spec sch.a (V)$.
  + Show affine morphisms are exactly these relative spectra, with
    $sch.a=f_*shf.o_X$.
  + Prove $f_*$ yields an equivalence between quasi-coherent $shf.o_X$-modules
    and quasi-coherent $sch.a$-modules.
]

// Hartshorne II.5, Exercise 5.18
#exercise(title: "Exercise 5.18 (Vector Bundles)")[
  Define a geometric rank-$n$ vector bundle by affine-$n$-space local
  trivializations with linear transition functions.

  + From a locally free rank-$n$ sheaf $shf.e$, construct
    $V(shf.e)=ops.spec S(shf.e)$ and show it is basis-independent.
  + Show sections of any geometric vector bundle form a locally free sheaf
    of rank $n$.
  + Identify the section sheaf of $V(shf.e)$ with $shf.e^ast$.
  + Deduce a bijection between isomorphism classes of locally free rank-$n$
    sheaves and geometric rank-$n$ vector bundles.
]

#exercise(title: "Exercise 5.3* (Supplementary)")[
  For $X=ops.proj S$, prove the adjunction
  $
    ops.hom(M, Gamma_*(shf.f), over: cat.gr(S)) simeq
    ops.hom(tildeOf(M), shf.f, over: shf.o_X).
  $
]
