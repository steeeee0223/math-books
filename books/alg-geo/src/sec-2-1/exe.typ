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
]

#proof[
  Let $shf.a^-$ denote the given presheaf and let $shf.a$ be the sheaf
  of locally constant $A$-valued functions.  There is a presheaf morphism
  $theta:shf.a^- ->shf.a$ which sends $a in A$ to the constant function
  with value $a$.  At the empty open set take the zero group; its unique
  section maps to the empty function.  Pointwise operations make $shf.a$ a
  sheaf of abelian groups, since compatible functions glue uniquely and
  local constancy can be tested on an open cover.

  We verify the universal property of sheafification.  Let $shf.g$ be a sheaf
  and let $u:shf.a^- ->shf.g$ be a presheaf morphism.  If
  $s in shf.a (U)$, choose an open cover $U=union_i U_i$ on which $s$ is
  constant, say with value $a_i$.  The sections $u_(U_i)(a_i)$ agree on every
  overlap: on a nonempty overlap the constants $a_i$ and $a_j$ are equal,
  while on an empty overlap there is nothing to check.  They therefore glue
  uniquely to a section $tilde(u)_U(s) in shf.g (U)$.

  Refining the cover does not change the glued section, so the maps
  $tilde(u)_U$ commute with restrictions.  Thus $tilde(u):shf.a->shf.g$ is a
  sheaf morphism and $tilde(u) compose theta=u$.  Since locally constant
  sections are locally in the image of $theta$, uniqueness follows from the
  uniqueness part of the sheaf axiom.  Hence $(shf.a,theta)$ is the associated
  sheaf of $shf.a^-$.
]

// Hartshorne II.1, Exercise 1.2
#exercise(title: "Exercise 1.2")[
  Let $phi:shf.f->shf.g$ be a morphism of sheaves.

  + Show $(ops.ker phi)_P=ops.ker (phi_P)$ and $(ops.im phi)_P=ops.im (phi_P)$.
  + Show that $phi$ is injective, respectively surjective, exactly when all
    $phi_P$ are so.
  + Show that a sequence of sheaves is exact exactly when every induced
    sequence of stalks is exact.
]

#proof[
  + The inclusion $ops.ker phi arrow.r.hook shf.f$ induces a map
    $(ops.ker phi)_P -> ops.ker(phi_P)$.  It is injective: equality of
    germs is equality after restricting to a common neighborhood, also in
    the kernel presheaf.  Conversely, an element of $ops.ker(phi_P)$ is
    represented by a section $s in shf.f (U)$ whose image has zero germ at $P$.
    After shrinking $U$
    around $P$, $phi(s)$ is zero, so the same germ is represented by a section
    of $ops.ker phi$.  This proves
    $(ops.ker phi)_P simeq ops.ker(phi_P)$.  For the image, a germ in
    $ops.im(phi_P)$ is locally represented by some $phi(s)$, hence belongs to
    the stalk of the image presheaf.  Sheafification does not change stalks,
    giving $(ops.im phi)_P simeq ops.im(phi_P)$.

  + By the first isomorphism, $phi$ is injective exactly when every
    $ops.ker(phi_P)$ is zero.  A sheaf is zero exactly when all its stalks are
    zero, so this is equivalent to every $phi_P$ being injective.  Likewise,
    $phi$ is surjective exactly when $ops.im phi=shf.g$; taking stalks and using
    the image isomorphism shows that this is equivalent to every $phi_P$ being
    surjective.

  + A sequence is exact at a sheaf precisely when its image sheaf equals the
    next kernel sheaf.  The preceding identifications turn this equality on
    every stalk into the usual equality of image and kernel for abelian
    groups.  Since equality of subsheaves can be checked on all stalks, the
    original sequence is exact exactly when all stalk sequences are exact.
]

// Hartshorne II.1, Exercise 1.3
#exercise(title: "Exercise 1.3")[
  + Show that $phi:shf.f->shf.g$ is surjective exactly when every section
    $s in shf.g (U)$ locally lifts: some cover $U=union U_i$ admits
    $t_i in shf.f (U_i)$ with $phi(t_i)=s|_(U_i)$.
  + Give a surjective sheaf morphism whose map on sections over some open
    set is not surjective.
]

#proof[
  + Suppose first that $phi$ is surjective.  By Exercise 1.2 every stalk map
    $phi_P$ is surjective.  Given $s in shf.g (U)$ and $P in U$, choose a germ
    $t_P in shf.f_P$ mapping to $s_P$.  Represent $t_P$ by a section on a
    neighborhood $V_P subset.eq U$.  Equality of the two germs means that,
    after shrinking $V_P$ once more, $phi(t_P)=s|_(V_P)$.  The neighborhoods
    $V_P$ cover $U$ and give the required local lifts.

    Conversely, local lifts imply that every germ of $shf.g$ has a preimage:
    represent the germ by $s in shf.g (U)$ and choose one member of the lifting
    cover which contains the point.  Thus every $phi_P$ is surjective, and
    Exercise 1.2 implies that $phi$ is surjective.

  + Take $X=RR\/ZZ$, and let $cal(C)_RR$ and $cal(C)_(RR\/ZZ)$ be the sheaves
    of continuous functions with values in the indicated additive groups.
    The map
    $
      exp:cal(C)_RR -> cal(C)_(RR\/ZZ),
      quad t mapsto t mod ZZ,
    $
    is locally surjective because the quotient map $RR->RR\/ZZ$ has local
    continuous sections.  Hence it is a surjective sheaf morphism.  On the
    open set $X$ itself, however, the identity map $X->RR\/ZZ$ has no
    continuous lift $h:RR\/ZZ->RR$.  Indeed, with $q:RR->RR\/ZZ$ the
    quotient map, $h(q(t))-t$ would be a continuous integer-valued function
    on the connected space $RR$, hence constant.  But its values at $t=0$
    and $t=1$ differ by $1$, since $q(0)=q(1)$, a contradiction.
    Therefore the map on
    global sections is not surjective.
]

// Hartshorne II.1, Exercise 1.4
#exercise(title: "Exercise 1.4")[
  + If a presheaf morphism $phi:shf.f->shf.g$ is injective on every $U$, show the
    induced $phi^+:shf.f^+->shf.g^+$ is injective.
  + Deduce that the image sheaf of a sheaf morphism is naturally a subsheaf
    of the target.
]

#proof[
  + Let $P in X$.  Taking stalks commutes with sheafification, so the stalk of
    $phi^+$ identifies with the map on the stalks of the original presheaves.
    A germ represented by $s in shf.f (U)$ can map to zero only if, on some
    neighborhood $V subset.eq U$ of $P$, the section $phi_V(s|_V)$ is zero.
    Since $phi_V$ is injective, $s|_V=0$, and therefore the original germ is
    zero.  Thus every stalk map of $phi^+$ is injective.  Exercise 1.2 now
    shows that $phi^+$ is injective.

  + The presheaf image $U mapsto ops.im(phi_U)$ is a subpresheaf of $shf.g$.
    Its inclusion is injective on every open set, so part (a) sheafifies to an
    injection
    $ops.im phi=(U mapsto ops.im(phi_U))^+ arrow.r.hook shf.g^+$.
    Since $shf.g$ is already a sheaf, $shf.g^+ simeq shf.g$.  This realizes the
    image sheaf naturally as a subsheaf of the target.
]

// Hartshorne II.1, Exercise 1.5
#exercise(title: "Exercise 1.5")[
  Show that a morphism of sheaves is an isomorphism if and only if it is both
  injective and surjective.
]

#proof[
  An isomorphism is plainly both injective and surjective.  Conversely, if
  $phi$ is injective and surjective, Exercise 1.2 says that every stalk map
  $phi_P$ is an injective and surjective homomorphism of abelian groups, hence
  an isomorphism.  Proposition 1.1 then implies that $phi$ is an isomorphism.
]

// Hartshorne II.1, Exercise 1.6
#exercise(title: "Exercise 1.6")[
  + For a subsheaf $shf.f' subset.eq shf.f$, show that $shf.f->shf.f\/shf.f'$ is surjective
    with kernel $shf.f'$, giving $0->shf.f'->shf.f->shf.f\/shf.f'->0$.
  + Conversely, show that an exact sequence $0->shf.f'->shf.f->shf.f''->0$
    identifies $shf.f'$ with a subsheaf of $shf.f$ and $shf.f''$ with its quotient.
]

#proof[
  + Let $q:shf.f->shf.f\/shf.f'$ be the canonical map.  At a point $P$ it is
    the quotient homomorphism (filtered colimits of abelian groups commute
    with quotients, and sheafification preserves stalks)
    $shf.f_P->shf.f_P\/shf.f'_P$.  It is surjective and its kernel is exactly
    $shf.f'_P$.  Exercise 1.2 therefore shows that $q$ is surjective and that
    its kernel is $shf.f'$.  Hence
    $0->shf.f'->shf.f->shf.f\/shf.f'->0$ is exact.

  + Now suppose
    $0->shf.f'->^i shf.f->^q shf.f''->0$ is exact.  The map $i$ is injective,
    so it identifies $shf.f'$ with its image, a subsheaf of $shf.f$.  Exactness
    says $ops.im i=ops.ker q$.  The induced map
    $bar(q):shf.f\/ops.ker q->shf.f''$ has stalk map
    $shf.f_P\/ops.ker(q_P)->shf.f''_P$; this is an isomorphism by the first
    isomorphism theorem for abelian groups because $q_P$ is surjective.
    Proposition 1.1 gives
    $shf.f\/shf.f' simeq shf.f\/ops.ker q simeq shf.f''$.
]

// Hartshorne II.1, Exercise 1.7
#exercise(title: "Exercise 1.7")[
  For a sheaf morphism $phi:shf.f->shf.g$, show
  $ops.im phi simeq shf.f\/ops.ker phi$ and $ops.coker phi simeq shf.g\/ops.im phi$.
]

#proof[
  The morphism $phi$ factors through its image,
  $shf.f->shf.f\/ops.ker phi->ops.im phi arrow.r.hook shf.g$.
  On every stalk the middle map is the ordinary first-isomorphism-theorem map
  $shf.f_P\/ops.ker(phi_P)->ops.im(phi_P)$, hence is an isomorphism.  By
  Proposition 1.1 it is an isomorphism of sheaves, proving
  $shf.f\/ops.ker phi simeq ops.im phi$.

  By definition, $ops.coker phi$ is the sheafification of the presheaf
  $U mapsto shf.g (U)\/ops.im(phi_U)$.  The quotient morphism
  $shf.g->shf.g\/ops.im phi$ kills the presheaf
  image, so it induces a canonical morphism from $ops.coker phi$ to this
  quotient.  On every stalk this is the identity of the quotient group:
  both sides are
  $shf.g_P\/ops.im(phi_P)$.  Thus
  $ops.coker phi simeq shf.g\/ops.im phi$.
]

// Hartshorne II.1, Exercise 1.8
#exercise(title: "Exercise 1.8")[
  Show that $Gamma(U, dot)$ is left exact: if
  $0->shf.f'->shf.f->shf.f''$ is exact, then
  $0->Gamma(U, shf.f')->Gamma(U, shf.f)->Gamma(U, shf.f'')$ is exact. It need not be
  right exact; compare Exercise 1.21.
]

#proof[
  Write the sequence as
  $0->shf.f'->^i shf.f->^q shf.f''$ and fix an open set $U$.
  Since $i$ is an injective sheaf morphism, Exercise 1.2 shows that
  $i_U$ is injective.  Also $q_U compose i_U=0$, so
  $ops.im(i_U) subset.eq ops.ker(q_U)$.

  For the reverse inclusion, let $s in shf.f (U)$ satisfy $q_U(s)=0$.
  Exactness on stalks gives, near every $P in U$, a section
  $t_P in shf.f'(V_P)$ with $i(t_P)=s|_(V_P)$.  On overlaps the sections
  $t_P$ agree because $i$ is injective there.  They glue to
  $t in shf.f'(U)$, and the separatedness axiom for $shf.f$ gives
  $i_U(t)=s$.  Hence $ops.im(i_U)=ops.ker(q_U)$.

  There is generally no reason for $q_U$ to be surjective: the counterexample
  in Exercise 1.3 already supplies a surjective sheaf morphism which is not
  surjective on global sections.
]

// Hartshorne II.1, Exercise 1.9
#exercise(title: "Exercise 1.9 (Direct Sum)")[
  For sheaves $shf.f$ and $shf.g$ on $X$, show that
  $U mapsto shf.f (U) times shf.g (U)$ is a sheaf. Show that the resulting
  $shf.f plus.o shf.g$ is both a direct sum and a direct product in the category
  of sheaves of abelian groups.
]

#proof[
  Put $shf.h (U)=shf.f (U) times shf.g (U)$, with restrictions taken componentwise.
  Suppose $(s_i,t_i) in shf.h (U_i)$ are compatible on a cover of $U$.  The
  sections $s_i$ glue uniquely to $s in shf.f (U)$, and the $t_i$ glue uniquely
  to $t in shf.g (U)$.  Then $(s,t)$ is the unique section of $shf.h (U)$ which
  restricts to every $(s_i,t_i)$.  Hence $shf.h$ is a sheaf.

  Let $i_f(s)=(s,0)$ and $i_g(t)=(0,t)$ be the inclusions, and let $p_f,p_g$
  be the two projections.  For every sheaf $shf.k$, composition with the
  projections gives a natural bijection
  $
    ops.hom(shf.k, shf.h)
    simeq ops.hom(shf.k, shf.f) times ops.hom(shf.k, shf.g).
  $
  Indeed, a pair $(a,b)$ corresponds to the componentwise map $k mapsto
  (a(k),b(k))$.  Thus $shf.h$ is the product of $shf.f$ and $shf.g$.

  Similarly, composition with the inclusions gives a natural bijection
  $
    ops.hom(shf.h, shf.k)
    simeq ops.hom(shf.f, shf.k) times ops.hom(shf.g, shf.k).
  $
  The inverse sends $(a,b)$ to the morphism $(s,t) mapsto a(s)+b(t)$.  Thus
  $shf.h$ is also the direct sum.
]

// Hartshorne II.1, Exercise 1.10
#exercise(title: "Exercise 1.10 (Direct Limit)")[
  For a direct system of sheaves $shf.f_i$, define $ops.colim shf.f_i$ as the sheaf
  associated to $U mapsto ops.colim shf.f_i (U)$. Prove its universal property as a
  direct limit in the category of sheaves.
]

#proof[
  Let $cal(P)$ be the presheaf $cal(P)(U)=ops.colim_i shf.f_i (U)$, and let
  $cal(P)^+$ be its associated sheaf.  The canonical maps
  $shf.f_i (U)->cal(P)(U)->cal(P)^+(U)$ commute with restrictions and with the
  transition maps, so they form a cocone $shf.f_i->cal(P)^+$.

  Now let $(u_i:shf.f_i->shf.g)$ be any compatible cocone whose target
  $shf.g$ is a sheaf.  For each open $U$, the universal property of the
  colimit of abelian groups gives a unique map
  $
    u_U:cal(P)(U)=ops.colim_i shf.f_i (U) -> shf.g (U)
  $
  whose composite with every canonical map is $(u_i)_U$.  Naturality of the
  $u_i$ and uniqueness of the colimit map show that the $u_U$ commute with
  restrictions.  Hence they form a presheaf morphism $u:cal(P)->shf.g$.

  Because $shf.g$ is a sheaf, the universal property of sheafification extends
  $u$ uniquely to $u^+:cal(P)^+->shf.g$.  This map factors the original cocone,
  and any other such factorization restricts to the same map on $cal(P)$, so
  it is equal to $u^+$.  Therefore $cal(P)^+$ has the universal property of
  $ops.colim_i shf.f_i$.
]

// Hartshorne II.1, Exercise 1.11
#exercise(title: "Exercise 1.11")[
  If $X$ is noetherian and $shf.f_i$ is a direct system of sheaves, show that
  $U mapsto ops.colim shf.f_i (U)$ already is a sheaf. In particular,
  $Gamma(X, ops.colim shf.f_i)=ops.colim Gamma(X, shf.f_i)$.
]

#proof[
  Write $cal(P)(U)=ops.colim_i shf.f_i (U)$.  Because $X$ is noetherian,
  every open subset of $X$ is quasi-compact.  We check the sheaf axiom for an
  open cover $(U_a)$ of $U$.  Only finitely many members are needed, so replace
  the cover by $U_1,dots,U_n$ for the finite gluing argument below.
  Once a section on $U$ is obtained, it has the prescribed restriction on
  any omitted $U_a$: apply separatedness to the finite cover
  $(U_a inter U_i)_(i=1)^n$.  The empty open has zero colimit group.

  Let $s_a in cal(P)(U_a)$ be compatible.  Choose a representative of each
  $s_a$ in some $shf.f_(i_a) (U_a)$.  Since the index category is filtered and
  only finitely many indices occur, there is a common later index $j$ to which
  all these representatives map.  Their images may not yet be equal on every
  overlap, but equality in a filtered colimit means equality at some later
  stage.  There are only finitely many overlaps $U_a inter U_b$, so filteredness
  again gives one index $k$ at which all overlap equalities hold simultaneously.

  The resulting compatible sections in $shf.f_k (U_a)$ glue uniquely to a
  section $t in shf.f_k (U)$.  Its image in $cal(P)(U)$ restricts to every
  $s_a$, proving existence.  For uniqueness, if two elements of $cal(P)(U)$
  have equal restrictions, represent them at a common stage.  Their
  restrictions become equal at finitely many later stages, hence at one common
  stage; uniqueness in that sheaf then makes the two elements equal in the
  colimit.  Thus $cal(P)$ is already a sheaf.

  Exercise 1.10 therefore requires no further sheafification.  Taking $U=X$
  in its pointwise definition gives
  $
    Gamma(X, ops.colim_i shf.f_i)
    = ops.colim_i Gamma(X, shf.f_i).
  $
]

// Hartshorne II.1, Exercise 1.12
#exercise(title: "Exercise 1.12 (Inverse Limit)")[
  For an inverse system $shf.f_i$, show that $U mapsto op("lim") shf.f_i (U)$ is a sheaf
  and has the universal property of $op("lim") shf.f_i$ in the category of sheaves.
]

#proof[
  Put $cal(L)(U)=op("lim")_i shf.f_i (U)$, with restrictions defined
  componentwise.  Thus a section of $cal(L)(U)$ is a compatible tuple
  $(s_i)_i$ with $s_i in shf.f_i (U)$.

  Given compatible sections $s_a=(s_(a,i))_i in cal(L)(U_a)$ on a cover of
  $U$, fix $i$.  The sections $s_(a,i)$ glue uniquely in the sheaf $shf.f_i$
  to a section $s_i in shf.f_i (U)$.  For every arrow $i->j$ in the inverse
  system, the image of $s_i$ and the section $s_j$ have identical restrictions
  to every $U_a$; uniqueness in $shf.f_j$ makes them equal.  Hence $(s_i)_i$
  is a section of $cal(L)(U)$, and componentwise uniqueness proves the sheaf
  axiom.

  The projections $cal(L)->shf.f_i$ form a limiting cone.  If a sheaf $shf.g$
  has a compatible cone $u_i:shf.g->shf.f_i$, define
  $u_U(s)=((u_i)_U(s))_i$.  These maps commute with restrictions, so they form
  a sheaf morphism $u:shf.g->cal(L)$.  Its composites with the projections are
  the $u_i$, and those equations determine every component of $u$, proving
  uniqueness.  This is the universal property of the inverse limit.
]

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
]

#proof[
  Put
  $shf.hom (shf.f,shf.g)(U)=
  ops.hom(shf.f|_U, shf.g|_U)$.
  If $V subset.eq U$, restriction sends a morphism $alpha$ to
  $alpha|_V$.  Addition and inverses are defined componentwise:
  $(alpha+beta)_W=alpha_W+beta_W$ for every $W subset.eq U$.  Naturality of
  $alpha$ and $beta$ shows that these operations again give sheaf morphisms,
  so every $shf.hom (shf.f,shf.g)(U)$ is an abelian group and every
  restriction map is a homomorphism.

  It remains to check the sheaf axiom.  Let $U=union_i U_i$ and suppose that
  morphisms
  $alpha_i:shf.f|_(U_i)->shf.g|_(U_i)$ agree on all overlaps.  For an open
  $W subset.eq U$ and $s in shf.f (W)$, the sections
  $
    alpha_i(s|_(W inter U_i)) in shf.g (W inter U_i)
  $
  agree on every triple overlap by the compatibility of the $alpha_i$.
  Since $shf.g$ is a sheaf, they glue uniquely to a section
  $alpha_W(s) in shf.g (W)$.  Uniqueness of gluing shows both that $alpha_W$
  is a homomorphism and that the maps $alpha_W$ commute with restriction.
  Thus they form a morphism
  $alpha:shf.f|_U->shf.g|_U$ whose restriction to $U_i$ is $alpha_i$.

  If two such morphisms exist, their values on every section over every
  $W subset.eq U$ agree on the cover ${W inter U_i}$ and hence agree by the
  uniqueness axiom for $shf.g$.  The gluing is therefore unique, proving that
  $shf.hom (shf.f,shf.g)$ is a sheaf of abelian groups.
]

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
]

#proof[
  Write $P_f shf.g$ for the presheaf on $X$ given by
  $P_f shf.g (U)=ops.colim_(f(U) subset.eq V) shf.g (V)$.
  By definition, $f^(-1)shf.g$ is the sheafification of $P_f shf.g$.

  First let $shf.f$ be a sheaf on $X$. For every $V$ occurring in
  $P_f (f_*shf.f)(U)$, the inclusion $U subset.eq f^(-1)(V)$ gives a restriction
  homomorphism
  $shf.f (f^(-1)(V))->shf.f (U)$.
  These homomorphisms are compatible as $V$ varies, so the universal property
  of the colimit gives $P_f (f_*shf.f)(U)->shf.f (U)$. They commute with restriction
  in $U$ and hence form a presheaf morphism $P_f (f_*shf.f)->shf.f$.
  Since $shf.f$ is already a sheaf, the universal property of sheafification
  extends it uniquely to a sheaf morphism
  $epsilon_(shf.f): f^(-1)f_*shf.f->shf.f$.
  The construction uses only restriction maps, so it is natural in $shf.f$.

  Now let $shf.g$ be a sheaf on $Y$. If $V subset.eq Y$ is open, then
  $f(f^(-1)(V)) subset.eq V$. Thus $V$ is one of the indices in
  $P_f shf.g (f^(-1)(V))$, and the corresponding colimit map followed by
  sheafification is
  $shf.g (V)->P_f shf.g (f^(-1)(V))->f^(-1)shf.g (f^(-1)(V))$.
  These maps commute with restrictions in $V$, giving a natural sheaf morphism
  $eta_(shf.g):shf.g->f_*f^(-1)shf.g$.

  For $alpha:f^(-1)shf.g->shf.f$ and $beta:shf.g->f_*shf.f$, define
  $
    Phi(alpha) & =f_*alpha compose eta_(shf.g),       && Phi(alpha):shf.g->f_*shf.f, \
     Psi(beta) & =epsilon_(shf.f) compose f^(-1)beta, && Psi(beta):f^(-1)shf.g->shf.f.
  $

  On stalks, identify $(f^(-1)shf.g)_x$ with $shf.g_(f(x))$ by
  representing a germ on a neighborhood $V$ of $f(x)$.  The unit sends this
  representative to its inverse-image section on $f^(-1)(V)$, and the
  counit restricts a representative to the chosen source neighborhood.
  Applying these operations successively recovers the original germ.
  Thus the colimit maps used above satisfy the two triangle identities
  $
    f^(-1)shf.g
    ->^(f^(-1)eta_(shf.g))f^(-1)f_*f^(-1)shf.g
    ->^(epsilon_(f^(-1)shf.g))f^(-1)shf.g & =ops.id_(f^(-1)shf.g), \
     f_*shf.f
     ->^(eta_(f_*shf.f))f_*f^(-1)f_*shf.f
     ->^(f_*epsilon_(shf.f))f_*shf.f      & =ops.id_(f_*shf.f).
  $
  Indeed, before sheafification both composites are the canonical colimit map
  followed by the restriction map belonging to the same inclusion; the colimit
  and sheafification universal properties identify this composite with the
  identity.

  Naturality of $epsilon$ and the first triangle identity now give
  $
    Psi(Phi(alpha)) & =epsilon_(shf.f) compose f^(-1)f_*alpha compose f^(-1)eta_(shf.g) \
                    & =alpha compose epsilon_(f^(-1)shf.g) compose f^(-1)eta_(shf.g)
                      =alpha.
  $
  Similarly, naturality of $eta$ and the second triangle identity give
  $
    Phi(Psi(beta)) & =f_*epsilon_(shf.f) compose f_*f^(-1)beta compose eta_(shf.g) \
                   & =f_*epsilon_(shf.f) compose eta_(f_*shf.f) compose beta
                     =beta.
  $
  Therefore $Phi$ and $Psi$ are inverse bijections. Every ingredient is natural
  in both $shf.g$ and $shf.f$, so the bijection is natural in both variables.
]

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
]

#proof[
  For an open set $V subset.eq X$, define $shf.f (V)$ to be the abelian group
  of compatible families
  $
    (s_i)_i,
    quad s_i in shf.f_i(V inter U_i),
  $
  satisfying, on $V inter U_i inter U_j$,
  $
    phi_(i j)(s_i)=s_j.
  $
  The restriction maps are componentwise.  The identity and cocycle
  conditions imply that compatibility is preserved by restriction, addition,
  and inverses, so this defines a presheaf of abelian groups.

  To verify the sheaf axiom, cover $V$ by opens $V_a$ and take compatible
  sections $s^a=(s_i^a)_i$.  For each fixed $i$, the sections $s_i^a$ glue in
  the sheaf $shf.f_i$ to a unique
  $s_i in shf.f_i(V inter U_i)$.  On a pairwise overlap, the equality
  $phi_(i j)(s_i)=s_j$ holds after restriction to every $V_a$; separatedness
  of $shf.f_j$ makes it hold globally.  Hence $(s_i)_i$ is a section of
  $shf.f (V)$, and componentwise uniqueness proves uniqueness in $shf.f$.

  The construction also handles empty intersections, whose section groups
  are zero.  Fix $i$.  Projection to the $i$-th component gives
  $rho_i:shf.f|_(U_i)->shf.f_i$.  It is an isomorphism.  Indeed, if
  $t in shf.f_i(V)$ for $V subset.eq U_i$, its inverse image has $j$-th
  component
  $
    phi_(i j)(t|_(V inter U_j)).
  $
  The cocycle condition makes these components compatible, and the identity
  condition makes the $i$-th component equal to $t$.  The same computation
  shows that on $U_i inter U_j$ one has
  $rho_j=phi_(i j) compose rho_i$.

  Finally, suppose $shf.g$ has another compatible family of isomorphisms
  $sigma_i:shf.g|_(U_i) simeq shf.f_i$.  The local maps
  $rho_i^(-1) compose sigma_i:shf.g|_(U_i)->shf.f|_(U_i)$ agree on overlaps,
  so the construction in Exercise 1.15 glues them to an isomorphism
  $shf.g simeq shf.f$.  Its restrictions are prescribed, hence the same
  separatedness argument makes it unique.
]
