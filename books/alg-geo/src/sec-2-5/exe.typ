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
] <exercise-5-1>

For (a), (b), and (d), see #book-link(<sup-sc-11>)[SC-11]. For (c), see #book-link(<sup-sc-7>)[SC-7].

// Hartshorne II.5, Exercise 5.2
#exercise(title: "Exercise 5.2")[
  For a DVR $R$ with fraction field $K$ and $X=ops.spec R$:

  + show an $shf.o_X$-module is equivalent to an $R$-module $M$, a $K$-vector
    space $L$, and a map $tensor(M, K, over: R)->L$;
  + show it is quasi-coherent if and only if that map is an isomorphism.
] <exercise-5-2>

See #book-link(<sup-qc-9>)[QC-9].

// Hartshorne II.5, Exercise 5.3
#exercise(title: "Exercise 5.3")[
  For $X=ops.spec A$, prove the adjunction
  $
    ops.hom(M, Gamma(X, shf.f), over: A) simeq
    ops.hom(tildeOf(M), shf.f, over: shf.o_X).
  $
] <exercise-5-3>

See #book-link(<sup-qc-1>)[QC-1].

// Hartshorne II.5, Exercise 5.4
#exercise(title: "Exercise 5.4")[
  Show an $shf.o_X$-module is quasi-coherent if and only if locally it is a
  cokernel of a morphism of free sheaves. If $X$ is noetherian, show it is
  coherent if and only if locally it is such a cokernel with both free sheaves
  of finite rank.
] <exercise-5-4>

See #book-link(<sup-qc-7>)[QC-7].

// Hartshorne II.5, Exercise 5.5
#exercise(title: "Exercise 5.5")[
  For $f:X->Y$:

  + give an example where coherent $shf.f$ has noncoherent $f_*shf.f$, even for
    varieties over a field;
  + show every closed immersion is finite;
  + if $f$ is finite between noetherian schemes, show $f_*$ preserves
    coherent sheaves.
] <exercise-5-5>

For (a), see #book-link(<sup-qc-13>)[QC-13]. For (b), see #book-link(<sup-qc-5>)[QC-5]. For (c), see #book-link(<sup-qc-6>)[QC-6].

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
] <exercise-5-7>

For (a)~(b), see #book-link(<sup-se-10>)[SE-10]. For (c), see #book-link(<sup-se-12>)[SE-12].

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
