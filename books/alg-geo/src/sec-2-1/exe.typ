#import "@preview/theorion:0.4.0": *
#import "../defs.typ": *

#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

=== Exercises

// Hartshorne II.1, Exercise 1.1
#exercise(title: "Exercise 1.1")[
  Let $A$ be an abelian group and define the constant presheaf on $X$ by
  $U mapsto A$ for nonempty $U$, with identity restrictions. Show that the
  constant sheaf determined by $A$ is its associated sheaf.
] <exercise-1-1>

See #book-link(<sup-sc-10>)[SC-10].

// Hartshorne II.1, Exercise 1.2
#exercise(title: "Exercise 1.2")[
  Let $phi:shf.f->shf.g$ be a morphism of sheaves.

  + Show $(ops.ker phi)_P=ops.ker (phi_P)$ and $(ops.im phi)_P=ops.im (phi_P)$.
  + Show that $phi$ is injective, respectively surjective, exactly when all
    $phi_P$ are so.
  + Show that a sequence of sheaves is exact exactly when every induced
    sequence of stalks is exact.
] <exercise-1-2>

See #book-link(<sup-sc-4>)[SC-4].

// Hartshorne II.1, Exercise 1.3
#exercise(title: "Exercise 1.3")[
  + Show that $phi:shf.f->shf.g$ is surjective exactly when every section
    $s in shf.g (U)$ locally lifts: some cover $U=union U_i$ admits
    $t_i in shf.f (U_i)$ with $phi(t_i)=s|_(U_i)$.
  + Give a surjective sheaf morphism whose map on sections over some open
    set is not surjective.
] <exercise-1-3>

For (a), see #book-link(<sup-sc-4>)[SC-4]. For (b), see #book-link(<sup-sc-14>)[SC-14].

// Hartshorne II.1, Exercise 1.4
#exercise(title: "Exercise 1.4")[
  + If a presheaf morphism $phi:shf.f->shf.g$ is injective on every $U$, show the
    induced $phi^+:shf.f^+->shf.g^+$ is injective.
  + Deduce that the image sheaf of a sheaf morphism is naturally a subsheaf
    of the target.
] <exercise-1-4>

See #book-link(<sup-sc-4>)[SC-4].

// Hartshorne II.1, Exercise 1.5
#exercise(title: "Exercise 1.5")[
  Show that a morphism of sheaves is an isomorphism if and only if it is both
  injective and surjective.
] <exercise-1-5>

See #book-link(<sup-sc-4>)[SC-4].

// Hartshorne II.1, Exercise 1.6
#exercise(title: "Exercise 1.6")[
  + For a subsheaf $shf.f' subset.eq shf.f$, show that $shf.f->shf.f\/shf.f'$ is surjective
    with kernel $shf.f'$, giving $0->shf.f'->shf.f->shf.f\/shf.f'->0$.
  + Conversely, show that an exact sequence $0->shf.f'->shf.f->shf.f''->0$
    identifies $shf.f'$ with a subsheaf of $shf.f$ and $shf.f''$ with its quotient.
] <exercise-1-6>

See #book-link(<sup-sc-4>)[SC-4].

// Hartshorne II.1, Exercise 1.7
#exercise(title: "Exercise 1.7")[
  For a sheaf morphism $phi:shf.f->shf.g$, show
  $ops.im phi simeq shf.f\/ops.ker phi$ and $ops.coker phi simeq shf.g\/ops.im phi$.
] <exercise-1-7>

See #book-link(<sup-sc-4>)[SC-4].

// Hartshorne II.1, Exercise 1.8
#exercise(title: "Exercise 1.8")[
  Show that $Gamma(U, dot)$ is left exact: if
  $0->shf.f'->shf.f->shf.f''$ is exact, then
  $0->Gamma(U, shf.f')->Gamma(U, shf.f)->Gamma(U, shf.f'')$ is exact. It need not be
  right exact; compare Exercise 1.21.
] <exercise-1-8>

See #book-link(<sup-sc-6>)[SC-6].

// Hartshorne II.1, Exercise 1.9
#exercise(title: "Exercise 1.9 (Direct Sum)")[
  For sheaves $shf.f$ and $shf.g$ on $X$, show that
  $U mapsto shf.f (U) times shf.g (U)$ is a sheaf. Show that the resulting
  $shf.f plus.o shf.g$ is both a direct sum and a direct product in the category
  of sheaves of abelian groups.
] <exercise-1-9>

See #book-link(<sup-sc-3>)[SC-3].

// Hartshorne II.1, Exercise 1.10
#exercise(title: "Exercise 1.10 (Direct Limit)")[
  For a direct system of sheaves $shf.f_i$, define $ops.colim shf.f_i$ as the sheaf
  associated to $U mapsto ops.colim shf.f_i (U)$. Prove its universal property as a
  direct limit in the category of sheaves.
] <exercise-1-10>

See #book-link(<sup-sc-1>)[SC-1].

// Hartshorne II.1, Exercise 1.11
#exercise(title: "Exercise 1.11")[
  If $X$ is noetherian and $shf.f_i$ is a direct system of sheaves, show that
  $U mapsto ops.colim shf.f_i (U)$ already is a sheaf. In particular,
  $Gamma(X, ops.colim shf.f_i)=ops.colim Gamma(X, shf.f_i)$.
] <exercise-1-11>

See #book-link(<sup-sc-9>)[SC-9].

// Hartshorne II.1, Exercise 1.12
#exercise(title: "Exercise 1.12 (Inverse Limit)")[
  For an inverse system $shf.f_i$, show that $U mapsto op("lim") shf.f_i (U)$ is a sheaf
  and has the universal property of $op("lim") shf.f_i$ in the category of sheaves.
] <exercise-1-12>

See #book-link(<sup-sc-1>)[SC-1].

// Hartshorne II.1, Exercise 1.13
#exercise(title: "Exercise 1.13 (Espace Étale of a Presheaf)")[
  Given a presheaf $shf.f$, set $op("Spe")(shf.f)=union_(P in X) shf.f_P$ and project
  it to $X$. Give it the strongest topology making every germ map
  $s:U->op("Spe")(shf.f)$, for $s in shf.f (U)$, continuous. Show that $shf.f^+(U)$
  is the set of continuous sections over $U$. Hence $shf.f$ is a sheaf exactly
  when its sections are all continuous sections of this espace étale.
]

// Hartshorne II.1, Exercise 1.14
#exercise(title: "Exercise 1.14 (Support)")[
  For $s in shf.f (U)$ define $ops.supp s={P in U | s_P != 0}$. Show it is closed
  in $U$. Define $ops.supp shf.f={P in X | shf.f_P != 0}$ and note that this need not
  be closed.
]

// Hartshorne II.1, Exercise 1.15
#exercise(title: "Exercise 1.15 (Sheaf Hom)")[
  Show that $ops.hom(shf.f|_U, shf.g|_U)$ is naturally an abelian group and that
  $U mapsto ops.hom(shf.f|_U, shf.g|_U)$ is a sheaf, denoted
  $shf.hom (shf.f,shf.g)$.
] <exercise-1-15>

See #book-link(<sup-sc-5>)[SC-5].

// Hartshorne II.1, Exercise 1.16
#exercise(title: "Exercise 1.16 (Flasque Sheaves)")[
  A sheaf is *flasque* if every restriction $shf.f (U)->shf.f (V)$ is surjective.

  + Show that a constant sheaf on an irreducible space is flasque.
  + If $0->shf.f'->shf.f->shf.f''->0$ is exact and $shf.f'$ is flasque, show the
    sequence on sections over every $U$ is exact.
  + If $shf.f'$ and $shf.f$ are flasque in such a sequence, show $shf.f''$ is flasque.
  + If $f:X->Y$ is continuous and $shf.f$ is flasque, show $f_*shf.f$ is flasque.
  + Let $shf.g (U)$ be all functions $s:U->union_(P in U) shf.f_P$ with
    $s(P) in shf.f_P$. Show $shf.g$ is flasque and $shf.f->shf.g$ is naturally
    injective.
]

// Hartshorne II.1, Exercise 1.17
#exercise(title: "Exercise 1.17 (Skyscraper Sheaves)")[
  Let $P in X$ and let $A$ be an abelian group. Define
  $i_P (A)(U)=A$ if $P in U$ and $0$ otherwise. Show its stalk is $A$ at
  points of $overline({P})$ and $0$ elsewhere. Show it is also the direct
  image of the constant sheaf $A$ on $overline({P})$.
]

// Hartshorne II.1, Exercise 1.18
#exercise(title: "Exercise 1.18 (Adjoint Property)")[
  Given a continuous map $f:X->Y$:

  + construct a natural map $f^(-1)f_*shf.f->shf.f$ for every sheaf $shf.f$ on $X$;
  + construct a natural map $shf.g->f_*f^(-1)shf.g$ for every sheaf $shf.g$ on $Y$;
  + use them to prove the natural bijection
    $ops.hom(f^(-1)shf.g, shf.f, over: X) simeq ops.hom(shf.g, f_*shf.f, over: Y)$.

  Thus $f^(-1)$ is left adjoint to $f_*$.
] <exercise-1-18>

See #book-link(<sup-sc-6>)[SC-6].

// Hartshorne II.1, Exercise 1.19
#exercise(title: "Exercise 1.19 (Extending a Sheaf by Zero)")[
  Let $Z subset.eq X$ be closed, $U=X-Z$, and let $i:Z->X$, $j:U->X$ be
  inclusions.

  + For a sheaf $shf.f$ on $Z$, show $(i_*shf.f)_P=shf.f_P$ on $Z$ and is $0$
    outside $Z$.
  + For a sheaf $shf.f$ on $U$, sheafify the presheaf taking $V$ to $shf.f (V)$
    when $V subset.eq U$ and to $0$ otherwise. Show the resulting $j_!shf.f$
    has stalk $shf.f_P$ on $U$ and $0$ outside, and is uniquely characterized
    by this property and its restriction to $U$.
  + For a sheaf $shf.f$ on $X$, show
    $0->j_! (shf.f|_U)->shf.f->i_*(shf.f|_Z)->0$ is exact.
]

// Hartshorne II.1, Exercise 1.20
#exercise(title: "Exercise 1.20 (Subsheaf with Supports)")[
  For closed $Z subset.eq X$, let $Gamma_Z (X,shf.f)$ be sections supported in
  $Z$.

  + Show $V mapsto Gamma_(Z inter V) (V,shf.f|_V)$ is a sheaf, denoted
    $cal(H)^0_Z (shf.f)$.
  + Let $U = X-Z$, and let $j:U arrow.r.hook X$, show
    $0->cal(H)^0_Z (shf.f)->shf.f->j_*(shf.f|_U)$ is exact; if $shf.f$ is flasque,
    the last map is surjective.
]

// Hartshorne II.1, Exercise 1.21
#exercise(title: "Exercise 1.21 (Sheaves on Varieties)")[
  Let $X$ be a variety over an algebraically closed field and $shf.o_X$ its
  sheaf of regular functions.

  + For closed $Y subset.eq X$, show that the ideals of functions vanishing
    on $Y inter U$ form an ideal sheaf $cal(I)_Y subset.eq shf.o_X$.
  + If $Y$ is a subvariety, show
    $shf.o_X\/cal(I)_Y simeq i_*shf.o_Y$.
  + For $X=sch.p^1$ and $Y={P,Q}$, use
    $0->cal(I)_Y->shf.o_X->i_*shf.o_P plus.o i_*shf.o_Q->0$ to show the map on
    global sections is not surjective.
  + Let $cal(K)$ be the constant sheaf of the function field $K$ of $sch.p^1$.
    Show $shf.o_X->cal(K)$ is injective and
    $cal(K)\/shf.o_X simeq bigOPlus(i_P (K\/shf.o_P), P in X)$.
  + Show $0->Gamma(X, shf.o_X)->Gamma(X, cal(K))->
    Gamma(X, cal(K)\/shf.o_X)->0$ is exact.
]

// Hartshorne II.1, Exercise 1.22
#exercise(title: "Exercise 1.22 (Glueing Sheaves)")[
  Let $X=union_i U_i$. Suppose sheaves $shf.f_i$ on $U_i$ are equipped with
  isomorphisms
  $phi_(i j):shf.f_i|_(U_i inter U_j) simeq shf.f_j|_(U_i inter U_j)$ satisfying
  $phi_(i i)=ops.id$ and the cocycle condition
  $phi_(i k)=phi_(j k) compose phi_(i j)$ on triple intersections. Show
  there is a sheaf $shf.f$ on $X$, unique up to unique isomorphism, with
  isomorphisms $shf.f|_(U_i) simeq shf.f_i$ compatible with the $phi_(i j)$.
] <exercise-1-22>

See #book-link(<sup-sl-4>)[SL-4].
