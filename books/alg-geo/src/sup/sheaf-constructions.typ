#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== SC — Sheaf constructions and exactness <sup-sc>

Read #book-link(<sup-cat>)[CAT] and #book-link(<sup-sl>)[SL] first. Module statements
use #book-link(<text-ii-5>)[II.5, D1] and #book-link(<sup-al>)[AL]. The following
constructions refer to abelian groups, rings, or modules
over a fixed sheaf of rings. Kernel, image, quotient, and
sheafification definitions remain in #book-link(<text-ii-1>)[II.1, D5–D7].

#metadata(none) <sup-sc-1>
#proposition(number: "SC-1", title: "Small limits and colimits")[
  + For a small diagram $shf.f_i$, its limit has sections
    $U mapsto lim_i shf.f_i\(U)$, with restriction induced by the restrictions
    of all $shf.f_i$. Its projections are the sectionwise projections.

  + Its colimit is the sheafification of $U mapsto ops.colim_i shf.f_i\(U)$;
    the canonical maps are the presheaf structure maps followed by
    sheafification. These objects satisfy the cone and cocone properties in
    #book-link(<sup-cat-6>)[CAT-6].

  + For rings, take limits and colimits in rings;
    for modules, take them in $shf.o\(U)$-modules. Restriction in the latter case
    is semilinear for $shf.o\(U)->shf.o\(V)$.
  (Ex. II.1.10, II.1.12)
]

#proof[

  + *Construct limits sectionwise.* For limits, a compatible family of sections on a cover glues separately in
    each $shf.f_i$. Every diagram relation holds after restriction to that cover,
    so the glued family satisfies it by uniqueness. Thus the sectionwise limit
    is already a sheaf. A cone to the diagram induces sectionwise maps into
    this limit, compatible with restriction and uniquely determined by its
    projections. For modules, these maps are linear over the ring of sections;
    for rings, they preserve both multiplication and identity.

  + *Sheafify sectionwise colimits.* Form the sectionwise colimit presheaf $P$. Restriction is induced by the
    structure maps of the diagram; for modules, it is semilinear along the
    restriction of the ring of sections. A compatible cocone to a sheaf $G$
    gives a unique presheaf map $P->G$. The sheafification property gives a
    unique map $P^+->G$ with the original cocone. This proves the claimed
    colimit in each category. Local representatives also give $P^+$ its module
    or ring operations, since the corresponding finite identities can be
    checked locally.
]

#metadata(none) <sup-sc-2>
#proposition(number: "SC-2", title: "Stalk comparisons")[
  + In these concrete categories, the canonical maps
    $ops.colim_i (shf.f_i)_x -> (ops.colim_i shf.f_i)_x$ are isomorphisms.

  + For finite diagrams, the map
    $(lim_i shf.f_i)_x -> lim_i (shf.f_i)_x$ is also an isomorphism.
    The latter assertion does not hold for arbitrary limits. Finite-limit
    compatibility uses the filtered system of neighborhoods and the finite
    number of representatives and equalities involved; see
    #book-link(<sup-sl-1>)[SL-1].

  Kernel and image comparisons are included in SC-4.
]

#proof[

  + *Compare colimits with stalks.* Sheafification leaves stalks unchanged by SL-5. For abelian groups, rings,
    and sets, a stalk of the colimit presheaf is an iterated colimit: first over
    the given diagram, then over neighborhoods of $x$. A map out of either
    order is the same compatible family of maps, so the two colimits are
    canonically isomorphic. For modules, the scalars become $shf.o_x$; the
    same universal property uses semilinear restriction followed by this scalar
    action. Equivalently, present a module colimit by generators and additive,
    scalar, and diagram relations. Every element and relation uses finitely
    many sections and scalars, all representable on a common neighborhood.
    This gives both surjectivity and injectivity of the stalk comparison.

  + *Compare finite limits with stalks.* For a finite limit, represent its finitely many component germs on one
    neighborhood. Its finitely many arrow equations hold as germs and hence,
    by SL-1, on a smaller common neighborhood. They now define a section of
    the sectionwise limit, proving surjectivity. If two such sections have the
    same component germs, shrink once for each of the finitely many components;
    they become equal, proving injectivity. The constructed bijections preserve
    the operations, and their component formulas identify the stated maps.
    The counterexamples below exhibit the failure for infinite limits.
]

#metadata(none) <sup-sc-3>
#proposition(number: "SC-3", title: "Direct sums of abelian-group sheaves")[
  + A finite direct sum is a biproduct, with its usual injections and projections.
    (Ex. II.1.9)

  + An arbitrary direct sum is the
    sheafification of the presheaf direct sum. A section is a family of sections
    which, locally on the space, has only finitely many nonzero components.

  + For $shf.o$-modules, use the same construction with componentwise scalar
    multiplication.
]

#proof[

  + *Construct the sheaf.* Put $shf.h (U)=shf.f (U) times shf.g (U)$, with restrictions taken componentwise.
    Suppose $(s_i,t_i) in shf.h (U_i)$ are compatible on a cover of $U$.  The
    sections $s_i$ glue uniquely to $s in shf.f (U)$, and the $t_i$ glue uniquely
    to $t in shf.g (U)$.  Then $(s,t)$ is the unique section of $shf.h (U)$ which
    restricts to every $(s_i,t_i)$.  Hence $shf.h$ is a sheaf.

  + *Verify the product property.* Let $i_f\(s)=(s,0)$ and $i_g\(t)=(0,t)$ be the inclusions, and let $p_f,p_g$
    be the two projections.  For every sheaf $shf.k$, composition with the
    projections gives a natural bijection
    $
      ops.hom(shf.k, shf.h)
      simeq ops.hom(shf.k, shf.f) times ops.hom(shf.k, shf.g).
    $
    Indeed, a pair $(a,b)$ corresponds to the componentwise map $k mapsto
    (a(k),b(k))$.  Thus $shf.h$ is the product of $shf.f$ and $shf.g$.

  + *Verify the direct-sum property.* Similarly, composition with the inclusions gives a natural bijection
    $
      ops.hom(shf.h, shf.k)
      simeq ops.hom(shf.f, shf.k) times ops.hom(shf.g, shf.k).
    $
    The inverse sends $(a,b)$ to the morphism $(s,t) mapsto a(s)+b(t)$.  Thus
    $shf.h$ is also the direct sum.

  + *Construct arbitrary direct sums.* For an arbitrary index set, sheafify
    the sectionwise direct sum as in SC-1.

  + *Embed it in the product.* Its map to the
    product sheaf is injective: a locally finite-support representative with
    all components zero is locally zero, hence zero by SL-1.

  + *Describe the image.* Its image consists
    exactly of families having finite support on a neighborhood of each point.
    Such a family locally belongs to the presheaf direct sum, and these local
    representatives agree componentwise and glue in its sheafification. For
    modules, all these constructions respect the scalar action componentwise.
]

#metadata(none) <sup-sc-4>
#proposition(number: "SC-4", title: "Exactness calculus")[
  + For abelian groups and modules, kernels and images commute with stalks.
    Injectivity, surjectivity, and exactness are detected on stalks.
    In particular, a morphism is an isomorphism if and only if it is both
    injective and surjective.

  + Sheafification preserves sectionwise injections of presheaves. Hence
    the sheafified presheaf image is a subsheaf of the target.

  + For sheaves of abelian groups or modules, a morphism $u:shf.f->shf.g$
    is surjective if and only if, for every open $U$ and $s in shf.g (U)$,
    there are an open cover $U=union_i U_i$ and sections $t_i in shf.f (U_i)$
    such that $u(t_i)=s|_(U_i)$ for every $i$. A lift over $U$ itself
    need not exist.

  + There is a canonical isomorphism
    $shf.f\/ops.ker(u) -> ops.im(u)$, and
    $ops.coker(u) simeq shf.g\/ops.im(u)$.

  + Thus $0->shf.f'->shf.f->shf.f''->0$ is exact exactly when the first map
    identifies a subsheaf and the second identifies its quotient with $shf.f''$. (Ex. II.1.2\~7)

  + For a ring morphism, the image is a subring sheaf, and the kernel is an
    ideal sheaf, not a subring. Quotients by ideal sheaves are obtained
    by sheafifying sectionwise ring quotients. Here a surjective ring-sheaf
    map means surjective on underlying stalks, not an arbitrary categorical
    epimorphism. Abelian-category exactness is not being applied to rings.
]

#proof[

  + *Compute kernels and images.* A germ in $ops.ker(u_x)$ has a
    representative whose image vanishes after shrinking, by SL-1. Thus
    $(ops.ker u)_x=ops.ker(u_x)$. The image presheaf has stalk
    $ops.im(u_x)$, and sheafification preserves this stalk by SL-5.
    A sectionwise injection remains injective on stalks: a germ mapping
    to zero has a representative mapping to zero on a smaller open,
    where injectivity forces it to vanish. Applying SL-5 proves that
    sheafification preserves injections and identifies the image sheaf
    with a subsheaf of the target.

  + *Detect exactness.* A sheaf is zero if all its stalks vanish, by SL-1.
    Two subsheaves with equal stalks are equal: a section of either belongs
    locally to the other, and these local sections glue. Consequently,
    kernel-image equality is equivalent to equality on every stalk.
    This proves the injectivity, surjectivity, and exactness criteria.
    A map both injective and surjective has bijective stalk maps, hence
    is an isomorphism by II.1, Proposition 1.1. A bijective homomorphism
    of groups or modules is an isomorphism (Check!).

  + *Lift sections locally.* If $u_x$ is surjective, lift the germ of a
    target section at $x$ and choose a representative of the lift.
    SL-1 permits shrinking until its image equals the target section.
    These neighborhoods form a lifting cover. Conversely, any such cover
    gives a lift of every germ and hence surjectivity on stalks.

  + *Identify quotients and cokernels.* For a subsheaf $shf.f'$ of $shf.f$,
    the stalk of the quotient map is
    $shf.f_x->shf.f_x\/shf.f'_x$: filtered colimits of modules commute
    with quotients (Check!), and SL-5 removes sheafification from the
    stalk calculation. It is surjective with kernel $shf.f'_x$.
    Thus $0->shf.f'->shf.f->shf.f\/shf.f'->0$ is exact.
    For an arbitrary $u$, the canonical map
    $shf.f\/ops.ker u->ops.im u$ induces the algebraic
    first-isomorphism map at each stalk, so is an isomorphism.
    The algebraic first-isomorphism theorem is left to the reader (Check!).
    Likewise the canonical map
    $ops.coker u->shf.g\/ops.im u$ is the identity of
    $shf.g_x\/ops.im(u_x)$ on stalks, hence is an isomorphism.
    Applying these formulas to a short exact sequence gives the stated
    identification with a subsheaf and its quotient.

  + *Retain the scalar and ring structures.* Module kernels, images, and
    quotients carry their induced scalar actions, so the preceding maps
    are linear. For rings, the kernel is an ideal, and the image and
    quotient are obtained by sheafifying their presheaf versions.
    Their stalks are the ring image and quotient by SL-5. The ring
    first-isomorphism theorem (Check!) gives the same quotient-to-image
    comparison. No assertion about arbitrary ring epimorphisms is used.
]

#metadata(none) <sup-sc-5>
#proposition(number: "SC-5", title: "Sheaf Hom")[
  + The assignment $U mapsto ops.hom(shf.f|_U, shf.g|_U)$, with restriction of
    morphisms, is a sheaf.

  + It is abelian-group-valued for abelian groups,
    set-valued for ring homomorphisms, and $shf.o$-module-valued for
    $shf.o$-linear maps.

  + Its global sections are precisely the morphisms
    $shf.f->shf.g$ and its restriction to an open is the Hom sheaf of the
    restrictions. (Ex. II.1.15)

  + The natural map from its stalk to the Hom of stalks need not be an
    isomorphism; the finite-presentation comparison is in #book-link(<sup-qc-3>)[QC-3].
]

#proof[

  + *Glue morphisms and operations.* Apply SL-3 on every open $U$ to compatible local morphisms: it gives the
    existence and uniqueness clause of the sheaf axiom for Hom. Restriction
    of a morphism is transitive, and addition and scalar multiplication of
    linear maps are computed sectionwise, giving the asserted structures.

  + *Identify sections and restrictions.* Over $X$ its definition is precisely the set of global sheaf morphisms;
    over any smaller open the same definition gives the Hom sheaf of the
    restricted sheaves. The pointwise abelian-group and module identities
    are algebraic checks left to the reader (Check!).

  + *Describe the stalk comparison.* The stalk comparison evaluates a local
    morphism on germs. A germ of a morphism requires one neighborhood on which
    all its section maps are defined; a map between two stalks need not have
    such a representative. For example, on $ops.spec ZZ$ take
    $shf.f=bigOPlus(shf.o, n>=0)$ and $shf.g=shf.o$. At the generic point,
    send the $n$-th basis vector to $1/p_n$, where the $p_n$ enumerate
    the positive primes. A local sheaf morphism would be defined on some
    $D(a)$ with $a!=0$ and would require every $1/p_n$ to lie in
    $ZZ[1/a]$. But a prime not dividing $a$ has no inverse in that ring
    (Check!), and such a prime exists by the infinitude of primes (Check!).
    Thus this stalk map has no local representative.
]

#metadata(none) <sup-sc-6>
#proposition(number: "SC-6", title: "Direct and inverse image")[
  For a continuous map $f:X->Y$, use the definitions in
  #book-link(<text-ii-1>)[II.1, D7].

  + The adjunction
    $ops.hom(f^(-1)shf.g, shf.f) simeq ops.hom(shf.g, f_*shf.f)$ has unit
    $shf.g->f_*f^(-1)shf.g$ and counit $f^(-1)f_*shf.f->shf.f$.
    (Ex. II.1.18)

  + For $g:Y->Z$, the canonical identifications are
    $(g compose f)_* simeq g_*f_*$ and
    $(g compose f)^(-1) simeq f^(-1)g^(-1)$, compatible with these adjunctions.

  + For abelian groups, inverse image is exact and direct image is left exact.

  + Sections over an open are left exact. (Ex. II.1.8) They need not be right
    exact, as SC-14 shows.
]

#proof[
  Write $P_f shf.g$ for the presheaf on $X$ given by
  $P_f shf.g (U)=ops.colim_(f(U) subset.eq V) shf.g (V)$.
  By definition, $f^(-1)shf.g$ is the sheafification of $P_f shf.g$.


  + *Construct the counit.* First let $shf.f$ be a sheaf on $X$. For every $V$ occurring in
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

  + *Construct the unit.* Now let $shf.g$ be a sheaf on $Y$. If $V subset.eq Y$ is open, then
    $f(f^(-1)(V)) subset.eq V$. Thus $V$ is one of the indices in
    $P_f shf.g (f^(-1)(V))$, and the corresponding colimit map followed by
    sheafification is
    $shf.g (V)->P_f shf.g (f^(-1)(V))->f^(-1)shf.g (f^(-1)(V))$.
    These maps commute with restrictions in $V$, giving a natural sheaf morphism
    $eta_(shf.g):shf.g->f_*f^(-1)shf.g$.

  + *Define the two Hom maps.* For $alpha:f^(-1)shf.g->shf.f$ and $beta:shf.g->f_*shf.f$, define
    $
      Phi(alpha) & =f_*alpha compose eta_(shf.g),       && Phi(alpha):shf.g->f_*shf.f, \
       Psi(beta) & =epsilon_(shf.f) compose f^(-1)beta, && Psi(beta):f^(-1)shf.g->shf.f.
    $

  + *Verify the triangle identities.* On stalks, identify $(f^(-1)shf.g)_x$ with $shf.g_(f(x))$ by
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
    Indeed, before sheafification, both composites are the canonical colimit map
    followed by the restriction map belonging to the same inclusion; the colimit
    and sheafification universal properties identify this composite with the
    identity.

  + *Show the Hom maps are inverse and natural.* Naturality of $epsilon$ and the first triangle identity now give
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

    The constructions use restriction and local representatives, so they
    preserve ring operations and the corresponding inverse-image scalar actions.

  + *Compare composites.* Direct images
    compose because inverse images of open subsets compose. Applying the two
    adjunctions successively identifies the Hom functors represented by the
    composite inverse image and by the inverse image of the composite. The
    unique adjunction-compatible comparison is therefore an isomorphism by
    CAT-2; its unit and counit are the composites under that same bijection.

  + *Prove inverse-image exactness on stalks.* For $x in X$, the canonical map identifies
    $(f^(-1)shf.g)_x$ with $shf.g_(f(x))$: both describe representatives on
    neighborhoods of $f(x)$, and the inverse-image construction followed by
    sheafification introduces no new germs or germ equalities. Inverse image
    is thus exact for abelian groups by the stalkwise exactness criterion.

  + *Prove left exactness of direct image.* Direct image is right adjoint, hence preserves kernels by CAT-9 and is
    left exact. For sections, if a section lies in the kernel of the
    second map of an exact sequence, stalkwise exactness supplies local
    lifts to the first sheaf. Injectivity makes these lifts agree on
    overlaps, so they glue to a unique lift. This proves left exactness
    of sections on every open.
]

#metadata(none) <sup-sc-7>
#proposition(number: "SC-7", title: "Tensor sheaves and the tensor–Hom adjunction")[
  + The tensor sheaf is the sheafification of
    $U mapsto tensor(shf.f (U), shf.g (U), over: shf.o (U))$; its canonical balanced
    map represents compatible bilinear maps into sheaves.

  + For modules,
    $ops.hom(tensor(shf.e, shf.f), shf.g) simeq
    ops.hom(shf.f, shf.hom (shf.e,shf.g))$ naturally.
  (Ex. II.5.1(c))
]

#proof[

  + *Apply the tensor universal property.* The sectionwise tensor universal property sends a balanced bilinear family
    to a presheaf map from the tensor presheaf. Sheafification extends it
    uniquely to a sheaf map. Conversely, composition with the canonical pure-tensor
    map recovers that family.

  + *Construct the tensor–Hom adjunction.* Currying the family on each open gives
    $shf.f->shf.hom (shf.e,shf.g)$; restriction commutes with currying, so
    this is the claimed natural adjunction. Its inverse evaluates the Hom
    section on the $shf.e$ section. The two maps are inverse by the
    algebraic tensor universal property (Check!).
]

#metadata(none) <sup-sc-8>
#proposition(number: "SC-8", title: "Module pullback and scalar extension")[
  + For a morphism of ringed spaces, the module pullback of
    #book-link(<text-ii-5>)[II.5, D1] uses extension of scalars:
    $f^*shf.g=tensor(shf.o_X, f^(-1)shf.g, over: f^(-1)shf.o_Y)$.

  + It is left adjoint to module direct image, and is right exact.

  + If $shf.o_(X,x)$ is flat over $shf.o_(Y,f(x))$ for every $x in X$,
    then the pullback functor $f^*$ is exact.

  + The canonical maps comparing pullback of tensor, symmetric, and exterior
    operations with the corresponding operations on pullbacks are isomorphisms.
    The operations are those of #book-link(<sup-al-6>)[AL-6], applied sectionwise
    and then sheafified.

  Inverse image alone does not extend scalars.
]

#proof[

  + *Construct the module adjunction.* A linear map $tensor(shf.o_X, f^(-1)shf.g, over: f^(-1)shf.o_Y)->shf.f$
    is equivalent, by extension of scalars, to an $f^(-1)shf.o_Y$-linear map
    $f^(-1)shf.g->shf.f$. The inverse-image adjunction identifies these with
    $shf.o_Y$-linear maps $shf.g->f_*shf.f$. These identifications send a
    pure tensor $tensor(a, s)$ to $a$ times the image of $s$, so are the desired
    module pullback adjunction. A left adjoint preserves cokernels and direct
    sums, hence is right exact.

  + *Compute pullback stalks.* On the stalk at $x$, the pullback is
    $tensor(shf.o_(X,x), shf.g_(f(x)), over: shf.o_(Y,f(x)))$.
    Indeed, tensor products use finite sums of pure tensors and finite relations,
    so representatives and their relations can be taken on a common neighborhood
    before sheafification; SL-5 then computes the stalk.

  + *Use flatness for exactness.* If the indicated ring
    module is flat, tensoring there preserves exact sequences; SC-4 gives
    exactness of pullback.

  + *Compare the algebraic operations.* Apply AL-6 on the same stalks to compare tensor,
    symmetric, and exterior operations. These are the stalk maps of the
    canonical sheaf comparisons on generators, so stalkwise invertibility proves
    the sheaf comparisons are isomorphisms.
]

#metadata(none) <sup-sc-9>
#proposition(number: "SC-9", title: "Sections and filtered colimits")[
  On a Noetherian topological space, for a directed system of abelian-group
  sheaves and every open $U$, the canonical map
  $ops.colim_i shf.f_i(U) -> (ops.colim_i shf.f_i)(U)$ is an isomorphism.
  (Ex. II.1.11) Every open, including intersections of
  members of a finite cover, is quasi-compact; these finiteness conditions
  permit choosing common indices for representatives and their relations.
  No assertion of this kind is made for an arbitrary space.
]

#proof[

  + *Reduce the sheaf axiom to a finite cover.* Write $cal(P)(U)=ops.colim_i shf.f_i (U)$.  Because $X$ is noetherian,
    every open subset of $X$ is quasi-compact (Check!).  We check the sheaf axiom for an
    open cover $(U_a)$ of $U$.  Only finitely many members are needed, so replace
    the cover by $U_1,dots,U_n$ for the finite gluing argument below.
    Once a section on $U$ is obtained, it has the prescribed restriction on
    any omitted $U_a$: apply separatedness to the finite cover
    $(U_a inter U_i)_(i=1)^n$.  The empty open has zero colimit group.

  + *Choose one stage for representatives and relations.* Let $s_a in cal(P)(U_a)$ be compatible.  Choose a representative of each
    $s_a$ in some $shf.f_(i_a) (U_a)$.  Since the index category is filtered and
    only finitely many indices occur, there is a common later index $j$ to which
    all these representatives map.  Their images may not yet be equal on every
    overlap, but equality in a filtered colimit means equality at some later
    stage by CAT-8.  There are only finitely many overlaps $U_a inter U_b$, so filteredness
    again gives one index $k$ at which all overlap equalities hold simultaneously.

  + *Glue and prove uniqueness.* The resulting compatible sections in $shf.f_k (U_a)$ glue uniquely to a
    section $t in shf.f_k (U)$.  Its image in $cal(P)(U)$ restricts to every
    $s_a$, proving existence.  For uniqueness, if two elements of $cal(P)(U)$
    have equal restrictions, represent them at a common stage.  Their
    restrictions become equal at finitely many later stages, hence at one common
    stage; uniqueness in that sheaf then makes the two elements equal in the
    colimit.  Thus $cal(P)$ is already a sheaf.

  + *Identify the sections of the colimit sheaf.* SC-1 therefore requires no further sheafification.  Taking $U=X$
    in its pointwise definition gives
    $
      Gamma(X, ops.colim_i shf.f_i)
      = ops.colim_i Gamma(X, shf.f_i).
    $
]

#metadata(none) <sup-sc-10>
#proposition(number: "SC-10", title: "Constant and skyscraper sheaves")[
  + For an abelian group $A$, the sheafification of the constant presheaf is
    the sheaf of locally constant $A$-valued functions. (Ex. II.1.1)

  + For $i_P:{P}->X$, the skyscraper
    $i_(P*)A$ has sections $A$ on opens containing $P$ and zero otherwise.

  + Its stalk at $x$ is $A$ if $x in overline({P})$, and zero otherwise.

  + It is also the direct image of the constant sheaf on $overline({P})$.

  For a nonclosed $P$, its support is not just ${P}$.
]

#proof[

  + *Construct the canonical morphism.* Let $shf.a^-$ denote the given presheaf and let $shf.a$ be the sheaf
    of locally constant $A$-valued functions.  There is a presheaf morphism
    $theta:shf.a^- ->shf.a$ which sends $a in A$ to the constant function
    with value $a$.  At the empty open set, take the zero group; its unique
    section maps to the empty function.  Pointwise operations make $shf.a$ a
    sheaf of abelian groups, since compatible functions glue uniquely and
    local constancy can be tested on an open cover.

  + *Extend a presheaf morphism by gluing.* We verify the universal property of sheafification.  Let $shf.g$ be a sheaf
    and let $u:shf.a^- ->shf.g$ be a presheaf morphism.  If
    $s in shf.a (U)$, choose an open cover $U=union_i U_i$ on which $s$ is
    constant, say with value $a_i$.  The sections $u_(U_i)(a_i)$ agree on every
    overlap: on a nonempty overlap the constants $a_i$ and $a_j$ are equal,
    while on an empty overlap there is nothing to check.  They therefore glue
    uniquely to a section $tilde(u)_U(s) in shf.g (U)$.

  + *Check naturality and uniqueness.* Refining the cover does not change the glued section, so the maps
    $tilde(u)_U$ commute with restrictions.  Thus $tilde(u):shf.a->shf.g$ is a
    sheaf morphism and $tilde(u) compose theta=u$.  Since locally constant
    sections are locally in the image of $theta$, uniqueness follows from the
    uniqueness part of the sheaf axiom.  Hence $(shf.a,theta)$ is the associated
    sheaf of $shf.a^-$.

  For a skyscraper, the definition of direct image from ${P}$ gives
  the stated sections.

  + *Compute skyscraper stalks.* If $x in overline({P})$, every neighborhood
    of $x$ contains $P$, so the system computing the stalk is constantly $A$
    with identity maps. Otherwise, a neighborhood avoids $P$, and its smaller
    neighborhoods give the zero stalk.

  + *Use the constant sheaf on the closure.* Put $Z=overline({P})$.
    Every nonempty relatively open subset of $Z$ contains $P$, so $Z$ and
    all its nonempty opens are irreducible and in particular connected.
    A locally constant function on such an open is constant (Check!). The direct image
    of the constant sheaf on $Z$ therefore has sections $A$ exactly on opens
    meeting $Z$, equivalently containing $P$, and zero on the other opens.
    The identifications commute with restriction and give the claimed isomorphism.
]

#metadata(none) <sup-sc-11>
#proposition(number: "SC-11", title: "Finite locally free duality and projection formula")[
  Let $shf.e$ be a finite locally free module on a ringed space $X$,
  and put $shf.e^or=shf.hom_(shf.o_X)(shf.e,shf.o_X)$.

  + Evaluation gives $shf.e simeq (shf.e^or)^or$.
  + For every module $shf.f$, the canonical map
    $
      tensor(shf.e^or, shf.f, over: shf.o_X) & ->shf.hom_(shf.o_X)(shf.e,shf.f), \
                           tensor(lambda, s) & mapsto (e mapsto lambda(e)s)
    $
    is an isomorphism.
  + For a morphism of ringed spaces $f:X->Y$, an $shf.o_X$-module $shf.f$,
    and finite locally free $shf.e$ on $Y$, the canonical map
    $
      tensor(f_*shf.f, shf.e, over: shf.o_Y)->f_*(tensor(shf.f, f^*shf.e, over: shf.o_X)),
    $
    sending $tensor(s, e) & mapsto tensor(s, f^*e)$ locally, is an isomorphism.

  No properness or quasi-coherence is required. (Ex. II.5.1)
]

#proof[

  + *Restrict the canonical maps.* The evaluation and dual-tensor maps
    in the statement commute with restriction. Tensor sheaves and sheaf
    Hom restrict to the corresponding constructions on each open by
    their definitions. Choose an open cover trivializing $shf.e$ with
    finite rank $r$ on each member. SL-1 allows testing the maps on this
    cover and gluing their unique inverses.

  + *Compute duality in a basis.* On a trivializing open $U$, double-dual
    evaluation is the sheaf version of finite-free evaluation. Its inverse
    is $Phi mapsto sum_(i=1)^r Phi(e_i^or)e_i$ in a basis and its dual.
    The dual-tensor map identifies both sides with $(shf.f|_U)^r$;
    its inverse sends $v$ to $sum_(i=1)^r tensor(e_i^or, v(e_i))$.
    Over each $W subset.eq U$, these are finite-free identities over
    $shf.o_X(W)$, as in AL-5 (Check!). They commute with restriction,
    so give sheaf inverses. Uniqueness makes them agree on overlaps.

  + *Construct the projection map.* For the last assertion, use the map
    $theta:tensor(f_*shf.f, shf.e)->f_*tensor(shf.f, f^*shf.e)$
    induced on local pure tensors by $tensor(s, e) mapsto tensor(s, f^*e)$.
    Bilinearity and compatibility with restriction give a sheaf map.

  + *Trivialize on the target.* Let $V$ be a trivializing open for $shf.e$
    on $Y$, put $f_V:f^(-1)(V)->V$, and set
    $shf.f_V=shf.f|_(f^(-1)(V))$. Direct image restricts to
    $(f_V)_*shf.f_V$ by its section formula, and pullback gives
    $(f^*shf.e)|_(f^(-1)(V)) simeq shf.o_(f^(-1)(V))^r$ by SC-8.
    Tensoring with a finite free module is a finite direct sum (Check!),
    so both sides of $theta|_V$ identify with $((f_V)_*shf.f_V)^r$.
    The direct-image comparison is checked on every $W subset.eq V$:
    both sides have sections $shf.f (f^(-1)(W))^r$.
    Under these identifications $theta|_V$ is the identity. The opens $V$
    cover the target, and their local inverses agree because they invert
    the same map. SL-1 proves that $theta$ is an isomorphism.
]

#metadata(none) <sup-sc-examples>
#metadata(none) <sup-sc-12>
#example(number: "SC-12")[
  Let $X=NN union {infinity}$, with isolated natural numbers and
  tail neighborhoods at $infinity$. Let $shf.f_n$ be the skyscraper with
  coefficient $ZZ$ at $n$. Every $(shf.f_n)_infinity$ is zero, but the germ
  of $(1,1,dots)$ in $(product_n shf.f_n)_infinity$ is nonzero. Thus the
  comparison to $product_n (shf.f_n)_infinity$ is not injective.
]

#proof[

  + *Compute the component stalks.* An isolated point $n$ has a neighborhood disjoint from a sufficiently small
    tail neighborhood of $infinity$, so $(shf.f_n)_infinity=0$.

  + *Find a nonzero product germ.* Products of sheaves are sectionwise by SC-1. The section with value $1$
    in every skyscraper component restricts to a nonzero section on every tail,
    since a tail still contains natural numbers. Its germ is therefore nonzero,
    although every component germ is zero.
]

#metadata(none) <sup-sc-13>
#example(number: "SC-13")[
  Put $shf.g_m=product_(n<=m) shf.f_n$ with truncation maps.
  The same germ shows that $(lim_m shf.g_m)_infinity ->
  lim_m (shf.g_m)_infinity$ is not injective.
]

#proof[

  + *Identify the inverse limit.* Sectionwise, the inverse limit of the finite products with truncation maps
    is the full product: a compatible sequence of finite tuples is uniquely
    its infinite tuple of coordinates. SC-1 identifies this with the sheaf
    inverse limit.

  + *Compare its stalk with the limit of stalks.* Each finite product has zero stalk at $infinity$ by SC-2,
    whereas its inverse-limit sheaf has the nonzero germ from SC-12.
]

#metadata(none) <sup-sc-14>
#example(number: "SC-14")[
  For two distinct $k$-points on $sch.p^1_k$, the restriction
  of the structure sheaf onto their structure sheaf is surjective, but its
  map on global sections is the diagonal $k->k times k$.
  (Ex. II.1.3(b), II.1.21(c))
]

#proof[

  + *Check sheaf surjectivity.* At either of the two points, the stalk map is the residue-field quotient,
    and away from them its target is zero. It is therefore surjective as a
    sheaf map by SC-4.

  + *Compute the map on global sections.* Global regular functions on the projective line are
    constant, so the map on global sections is $a mapsto (a,a)$.
    The pair $(1,0)$ is not in its image.
]

#metadata(none) <sup-sc-15>
#example(number: "SC-15")[
  On a one-point space, $ZZ->QQ$ is an epimorphism of rings but not an underlying surjection.
]

#proof[

  + *Check the epimorphism property.* Two ring maps out of $QQ$ agreeing on $ZZ$ agree on every fraction,
    since the image of $a/b$ must be the image of $a$ times the inverse of
    the image of $b$. This is the categorical epimorphism property.

  + *Check failure of surjectivity.* The map
    is not surjective because $1/2$ is not an integer. On a one-point space,
    sheaves and their morphisms are simply the corresponding algebraic objects.
]

#metadata(none) <sup-sc-16>
#example(number: "SC-16")[
  Pullback along the one-point ringed-space map corresponding to
  $ZZ->ZZ\/2ZZ$ sends multiplication by $2$ on $ZZ$ to the zero map;
  see #book-link(<sup-al-examples>)[AL-12].
]

#proof[
  For a one-point ringed space, module pullback is scalar extension along the
  ring map. It sends the given multiplication map to multiplication by $2$
  on $ZZ\/2ZZ$, which is zero by AL-12.
]
