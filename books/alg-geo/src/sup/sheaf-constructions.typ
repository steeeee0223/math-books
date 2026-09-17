#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

=== SC — Sheaf constructions and exactness <sup-sc>

Read #book-link(<sup-cat>)[CAT] and #book-link(<sup-sl>)[SL] first. Module statements
use #book-link(<text-ii-5>)[II.5, D1] and #book-link(<sup-al>)[AL]. The following
constructions refer to abelian groups, rings, or modules
over a fixed sheaf of rings. Kernel, image, quotient, and
sheafification definitions remain in #book-link(<text-ii-1>)[II.1, D5–D7].

#metadata(none) <sup-sc-1>
#proposition(number: "SC-1", title: "Small limits and colimits")[
  - For a small diagram $shf.f_i$, its limit has sections
    $U mapsto lim_i shf.f_i (U)$, with restriction induced by the restrictions
    of all $shf.f_i$. Its projections are the sectionwise projections.

  - Its colimit is the sheafification of $U mapsto ops.colim_i shf.f_i(U)$;
    the canonical maps are the presheaf structure maps followed by
    sheafification. These objects satisfy the cone and cocone properties in
    #book-link(<sup-cat-4>)[CAT-4].

  - For rings, take limits and colimits in rings;
    for modules, take them in $shf.o\(U)$-modules. Restriction in the latter case
    is semilinear for $shf.o\(U)->shf.o\(V)$.

  See #book-link(<sup-proof-1-10>)[II.1.10] and #book-link(<sup-proof-1-12>)[II.1.12]
  for the direct-system and inverse-system constructions in abelian groups.
]

#proof[
  #set enum(numbering: "1.")

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
  - In these concrete categories, the canonical maps
    $ops.colim_i (shf.f_i)_x -> (ops.colim_i shf.f_i)_x$ are isomorphisms.

  - For finite diagrams, the map
    $(lim_i shf.f_i)_x -> lim_i (shf.f_i)_x$ is also an isomorphism.
    The latter assertion does not hold for arbitrary limits. Finite-limit
    compatibility uses the filtered system of neighborhoods and the finite
    number of representatives and equalities involved; see
    #book-link(<sup-sl-5>)[SL-5].

  Kernel and image comparisons for abelian groups
  are proved in #book-link(<sup-proof-1-2>)[II.1.2].
]

#proof[
  #set enum(numbering: "1.")

  + *Compare colimits with stalks.* Sheafification leaves stalks unchanged by SL-6. For abelian groups, rings,
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
    by SL-5, on a smaller common neighborhood. They now define a section of
    the sectionwise limit, proving surjectivity. If two such sections have the
    same component germs, shrink once for each of the finitely many components;
    they become equal, proving injectivity. The constructed bijections preserve
    the operations, and their component formulas identify the stated maps.
    The counterexamples below exhibit the failure for infinite limits.
]

#metadata(none) <sup-sc-3>
#proposition(number: "SC-3", title: "Direct sums of abelian-group sheaves")[
  - A finite direct sum is a biproduct, with its usual injections and projections;
    see #book-link(<sup-proof-1-9>)[II.1.9].

  - An arbitrary direct sum is the
    sheafification of the presheaf direct sum. A section is a family of sections
    which, locally on the space, has only finitely many nonzero components.

  - For $shf.o$-modules, use the same construction with componentwise scalar
    multiplication.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the direct sum.* The finite case is proved in #book-link(<sup-proof-1-9>)[II.1.9]. For an arbitrary
    index set, sheafify the sectionwise direct sum as in SC-1.

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
  - For abelian groups and modules, a sequence is exact if and only if its
    stalk sequences are exact.

  - For sheaves of abelian groups or modules, a morphism $u:shf.f->shf.g$
    is surjective if and only if, for every open $U$ and $s in shf.g (U)$,
    there are an open cover $U=union_i U_i$ and sections $t_i in shf.f (U_i)$
    such that $u(t_i)=s|_(U_i)$ for every $i$. A lift over $U$ itself
    need not exist.

  - There is a canonical isomorphism
    $shf.f\/ops.ker(u) -> ops.im(u)$.

  - Thus $0->shf.f'->shf.f->shf.f''->0$ is exact exactly when the first map
    identifies a subsheaf and the second identifies its quotient with $shf.f''$.
    The proofs of #book-link(<sup-proof-1-2>)[II.1.2–II.1.7 below] supply these
    criteria, including preservation of injections by sheafification.

  - For a ring morphism, the image is a subring sheaf, and the kernel is an
    ideal sheaf, not a subring. Quotients by ideal sheaves are obtained
    by sheafifying sectionwise ring quotients. Here a surjective ring-sheaf
    map means surjective on underlying stalks, not an arbitrary categorical
    epimorphism. Abelian-category exactness is not being applied to rings.
]

#proof[
  #set enum(numbering: "1.")

  + *Use the abelian-group criteria.* The abelian-group assertions, including the canonical quotient-to-image
    isomorphism and the local lifting criterion, are proved in
    #book-link(<sup-proof-1-2>)[II.1.2–II.1.7].

  + *Compute module kernels, images, and quotients.* For modules, kernels are the same
    sectionwise kernels with their induced scalar action; images and cokernels
    are sheafifications of the corresponding module presheaves. SL-6 identifies
    their stalks with the algebraic kernels, images, and cokernels. The ordinary
    module first-isomorphism map is stalkwise invertible, hence gives the stated
    sheaf isomorphism by II.1, Proposition 1.1.

  + *Characterize local lifting.* A surjective stalk map lifts a
    germ, and equality with the target germ holds on a smaller neighborhood;
    this gives local lifting of sections. Conversely, local lifts give stalkwise
    surjectivity. These observations prove all the module assertions.

  + *Treat ring ideals and quotients.* For rings, kernels are closed under multiplication by arbitrary local ring
    sections, hence form ideal sheaves. Sheafifying the sectionwise image and
    quotient gives their stalkwise ring image and quotient by SL-6. Thus the
    ring statements follow from the ring first-isomorphism theorem, without
    using an abelian-category argument or identifying ring epimorphisms with
    surjections.
]

#metadata(none) <sup-sc-5>
#definition(number: "SC-5", title: "Sheaf Hom")[
  - The assignment $U mapsto ops.hom(shf.f|_U, shf.g|_U)$, with restriction of
    morphisms, is a sheaf.

  - It is abelian-group-valued for abelian groups,
    set-valued for ring homomorphisms, and $shf.o$-module-valued for
    $shf.o$-linear maps.

  - Its global sections are precisely the morphisms
    $shf.f->shf.g$ and its restriction to an open is the Hom sheaf of the
    restrictions. The proof is in #book-link(<sup-proof-1-15>)[II.1.15].

  - The natural map from its stalk to the Hom of stalks need not be an
    isomorphism; the finite-presentation comparison is in #book-link(<sup-qc-3>)[QC-3].
]

#proof[
  #set enum(numbering: "1.")

  + *Glue morphisms and operations.* Apply SL-3 on every open $U$ to compatible local morphisms: it gives the
    existence and uniqueness clause of the sheaf axiom for Hom. Restriction
    of a morphism is transitive, and addition and scalar multiplication of
    linear maps are computed sectionwise, giving the asserted structures.

  + *Identify sections and restrictions.* Over $X$ its definition is precisely the set of global sheaf morphisms;
    over any smaller open the same definition gives the Hom sheaf of the
    restricted sheaves. The abelian-group proof is also recorded in
    #book-link(<sup-proof-1-15>)[II.1.15].

  + *Describe the stalk comparison.* The stalk comparison evaluates a local
    morphism on germs. A germ of a morphism requires one neighborhood on which
    all its section maps are defined; a map between two stalks need not have
    such a representative, as the Hom-localization example AL-E3 shows on an
    affine scheme at the generic point.
]

#metadata(none) <sup-sc-6>
#proposition(number: "SC-6", title: "Direct and inverse image")[
  For a continuous map $f:X->Y$, use the definitions in
  #book-link(<text-ii-1>)[II.1, D7].

  - The adjunction
    $ops.hom(f^(-1)shf.g, shf.f) simeq ops.hom(shf.g, f_*shf.f)$ has unit
    $shf.g->f_*f^(-1)shf.g$ and counit $f^(-1)f_*shf.f->shf.f$;
    see #book-link(<sup-proof-1-18>)[II.1.18] for their construction and identities.

  - For $g:Y->Z$, the canonical identifications are
    $(g compose f)_* simeq g_*f_*$ and
    $(g compose f)^(-1) simeq f^(-1)g^(-1)$, compatible with these adjunctions.

  - For abelian groups, inverse image is exact and direct image is left exact.

  - Sections over an open are left exact by #book-link(<sup-proof-1-8>)[II.1.8].
]

#proof[
  #set enum(numbering: "1.")

  + *Use the inverse-image adjunction.* The adjunction, its unit and counit, and the triangle identities are proved
    in #book-link(<sup-proof-1-18>)[II.1.18]. The constructions there use restriction
    and local representatives, so preserve ring and module operations whenever
    the respective inverse-image scalar structures are used.

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

  + *Prove left exactness of direct image.* Direct image is right adjoint, hence preserves kernels by CAT-6 and is
    left exact. This also explains left exactness of sections, whose elementary
    proof appears in #book-link(<sup-proof-1-8>)[II.1.8].
]

#metadata(none) <sup-sc-7>
#definition(number: "SC-7", title: "Module tensor and pullback")[
  - The tensor sheaf is the sheafification of
    $U mapsto tensor(shf.f (U), shf.g (U), over: shf.o (U))$; its canonical balanced
    map represents compatible bilinear maps into sheaves.

  - For modules,
    $ops.hom(tensor(shf.e, shf.f), shf.g) simeq
    ops.hom(shf.f, shf.hom (shf.e,shf.g))$ naturally.

  See #book-link(<sup-proof-5-1>)[II.5.1(c)] for the construction.
]

#proof[
  #set enum(numbering: "1.")

  + *Apply the tensor universal property.* The sectionwise tensor universal property sends a balanced bilinear family
    to a presheaf map from the tensor presheaf. Sheafification extends it
    uniquely to a sheaf map. Conversely, composition with the canonical pure-tensor
    map recovers that family.

  + *Construct the tensor–Hom adjunction.* Currying the family on each open gives
    $shf.f->shf.hom (shf.e,shf.g)$; restriction commutes with currying, so
    this is the claimed natural adjunction. Its inverse evaluates the Hom
    section on the $shf.e$ section. The construction is also given in
    #book-link(<sup-proof-5-1>)[II.5.1(c)].
]

#proposition(number: "SC-7.1", title: "Module pullback and scalar extension")[
  - For a morphism of ringed spaces, the module pullback of
    #book-link(<text-ii-5>)[II.5, D1] uses extension of scalars:
    $f^*shf.g=tensor(shf.o_X, f^(-1)shf.g, over: f^(-1)shf.o_Y)$.

  - It is left adjoint to module direct image, and is right exact.

  - If $shf.o_(X,x)$ is flat over $shf.o_(Y,f(x))$ for every $x in X$,
    then the pullback functor $f^*$ is exact.

  - The canonical maps comparing pullback of tensor, symmetric, and exterior
    operations with the corresponding operations on pullbacks are isomorphisms.
    The operations are those of #book-link(<sup-al-5>)[AL-5], applied sectionwise
    and then sheafified.

  Inverse image alone does not extend scalars.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the module adjunction.* A linear map $tensor(shf.o_X, f^(-1)shf.g, over: f^(-1)shf.o_Y)->shf.f$
    is equivalent, by extension of scalars, to an $f^(-1)shf.o_Y$-linear map
    $f^(-1)shf.g->shf.f$. The inverse-image adjunction identifies these with
    $shf.o_Y$-linear maps $shf.g->f_*shf.f$. These identifications send a
    pure tensor $a tensor s$ to $a$ times the image of $s$, so are the desired
    module pullback adjunction. A left adjoint preserves cokernels and direct
    sums, hence is right exact.

  + *Compute pullback stalks.* On the stalk at $x$, the pullback is
    $tensor(shf.o_(X,x), shf.g_(f(x)), over: shf.o_(Y,f(x)))$.
    Indeed, tensor products use finite sums of pure tensors and finite relations,
    so representatives and their relations can be taken on a common neighborhood
    before sheafification; SL-6 then computes the stalk.

  + *Use flatness for exactness.* If the indicated ring
    module is flat, tensoring there preserves exact sequences; SC-4 gives
    exactness of pullback.

  + *Compare the algebraic operations.* Apply AL-5 on the same stalks to compare tensor,
    symmetric, and exterior operations. These are the stalk maps of the
    canonical sheaf comparisons on generators, so stalkwise invertibility proves
    the sheaf comparisons are isomorphisms.
]

#metadata(none) <sup-sc-8>
#proposition(number: "SC-8", title: "Sections and filtered colimits")[
  On a Noetherian topological space, for a directed system of abelian-group
  sheaves and every open $U$, the canonical map
  $ops.colim_i shf.f_i(U) -> (ops.colim_i shf.f_i)(U)$ is an isomorphism.
  See #book-link(<sup-proof-1-11>)[II.1.11]. Every open, including intersections of
  members of a finite cover, is quasi-compact; these finiteness conditions
  permit choosing common indices for representatives and their relations.
  No assertion of this kind is made for an arbitrary space.
]

#metadata(none) <sup-sc-9>
#proposition(number: "SC-9", title: "Constant and skyscraper sheaves")[
  - For an abelian group $A$, the sheafification of the constant presheaf is
    the sheaf of locally constant $A$-valued functions; see
    #book-link(<sup-proof-1-1>)[II.1.1].

  - For $i_P:{P}->X$, the skyscraper
    $i_(P*)A$ has sections $A$ on opens containing $P$ and zero otherwise.

  - Its stalk at $x$ is $A$ if $x in overline({P})$, and zero otherwise.

  - It is also the direct image of the constant sheaf on $overline({P})$.

  For a nonclosed $P$, its support is not just ${P}$.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the section formulas.* The constant-sheaf identification is proved in #book-link(<sup-proof-1-1>)[II.1.1].
    For a skyscraper, direct image from ${P}$ has the displayed sections by
    the definition of direct image.

  + *Compute skyscraper stalks.* If $x in overline({P})$, every neighborhood
    of $x$ contains $P$, so the system computing the stalk is constantly $A$
    with identity maps. Otherwise, a neighborhood avoids $P$, and its smaller
    neighborhoods give the zero stalk.

  + *Use the constant sheaf on the closure.* Put $Z=overline({P})$.
    Every nonempty relatively open subset of $Z$ contains $P$, so $Z$ and
    all its nonempty opens are irreducible and in particular connected.
    A locally constant function on such an open is constant. The direct image
    of the constant sheaf on $Z$ therefore has sections $A$ exactly on opens
    meeting $Z$, equivalently containing $P$, and zero on the other opens.
    The identifications commute with restriction and give the claimed isomorphism.
]

#metadata(none) <sup-sc-10>
#proposition(number: "SC-10", title: "Finite locally free projection formula")[
  For a morphism of ringed spaces $f:X->Y$, an $shf.o_X$-module $shf.f$,
  and a finite locally free $shf.o_Y$-module $shf.e$, the canonical map
  $tensor(f_*shf.f, shf.e, over: shf.o_Y) ->
  f_*tensor(shf.f, f^*shf.e, over: shf.o_X)$,
  sending $tensor(s, e)$ to $tensor(s, f^*e)$ locally, is an isomorphism.
  No properness or quasi-coherence is required. The finite-free computation
  is in #book-link(<sup-proof-5-1>)[II.5.1(d)]; duality is in
  #book-link(<sup-al-4>)[AL-4].
]

#metadata(none) <sup-sc-examples>
#example(number: "SC-E1")[
  Let $X=NN union {infinity}$, with isolated natural numbers and
  tail neighborhoods at $infinity$. Let $shf.f_n$ be the skyscraper with
  coefficient $ZZ$ at $n$. Every $(shf.f_n)_infinity$ is zero, but the germ
  of $(1,1,dots)$ in $(product_n shf.f_n)_infinity$ is nonzero. Thus the
  comparison to $product_n (shf.f_n)_infinity$ is not injective.
]

#proof[
  #set enum(numbering: "1.")

  + *Compute the component stalks.* An isolated point $n$ has a neighborhood disjoint from a sufficiently small
    tail neighborhood of $infinity$, so $(shf.f_n)_infinity=0$.

  + *Find a nonzero product germ.* Products of sheaves are sectionwise by SC-1. The section with value $1$
    in every skyscraper component restricts to a nonzero section on every tail,
    since a tail still contains natural numbers. Its germ is therefore nonzero,
    although every component germ is zero.
]

#example(number: "SC-E2")[
  Put $shf.g_m=product_(n<=m) shf.f_n$ with truncation maps.
  The same germ shows that $(lim_m shf.g_m)_infinity ->
  lim_m (shf.g_m)_infinity$ is not injective.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the inverse limit.* Sectionwise, the inverse limit of the finite products with truncation maps
    is the full product: a compatible sequence of finite tuples is uniquely
    its infinite tuple of coordinates. SC-1 identifies this with the sheaf
    inverse limit.

  + *Compare its stalk with the limit of stalks.* Each finite product has zero stalk at $infinity$ by SC-2,
    whereas its inverse-limit sheaf has the nonzero germ from SC-E1.
]

#example(number: "SC-E3")[
  For two distinct $k$-points on $sch.p^1_k$, the restriction
  of the structure sheaf onto their structure sheaf is surjective, but its
  map on global sections is the diagonal $k->k times k$; see II.1.21(c).
]

#proof[
  #set enum(numbering: "1.")

  + *Check sheaf surjectivity.* At either of the two points, the stalk map is the residue-field quotient,
    and away from them its target is zero. It is therefore surjective as a
    sheaf map by SC-4.

  + *Compute the map on global sections.* Global regular functions on the projective line are
    constant, so the map on global sections is $a mapsto (a,a)$.
    The pair $(1,0)$ is not in its image.
]

#example(number: "SC-E4")[
  On a one-point space, $ZZ->QQ$ is an epimorphism of rings but not an underlying surjection.
]

#proof[
  #set enum(numbering: "1.")

  + *Check the epimorphism property.* Two ring maps out of $QQ$ agreeing on $ZZ$ agree on every fraction,
    since the image of $a/b$ must be the image of $a$ times the inverse of
    the image of $b$. This is the categorical epimorphism property.

  + *Check failure of surjectivity.* The map
    is not surjective because $1/2$ is not an integer. On a one-point space,
    sheaves and their morphisms are simply the corresponding algebraic objects.
]

#example(number: "SC-E5")[
  Pullback along the one-point ringed-space map corresponding to
  $ZZ->ZZ\/2ZZ$ sends multiplication by $2$ on $ZZ$ to the zero map;
  see #book-link(<sup-al-examples>)[AL-E1].
]

#proof[
  For a one-point ringed space, module pullback is scalar extension along the
  ring map. It sends the given multiplication map to multiplication by $2$
  on $ZZ\/2ZZ$, which is zero by AL-E1.
]

#block(sticky: true)[#strong[Application: II.1.1]] <sup-proof-1-1>

#exercise(title: "Exercise 1.1")[
  Let $A$ be an abelian group and define the constant presheaf on $X$ by
  $U mapsto A$ for nonempty $U$, with identity restrictions. Show that the
  constant sheaf determined by $A$ is its associated sheaf.
]

#proof[
  #set enum(numbering: "1.")

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
]

#block(sticky: true)[#strong[Application: II.1.2]] <sup-proof-1-2>

#exercise(title: "Exercise 1.2")[
  Let $phi:shf.f->shf.g$ be a morphism of sheaves.

  + Show $(ops.ker phi)_P=ops.ker (phi_P)$ and $(ops.im phi)_P=ops.im (phi_P)$.
  + Show that $phi$ is injective, respectively surjective, exactly when all
    $phi_P$ are so.
  + Show that a sequence of sheaves is exact exactly when every induced
    sequence of stalks is exact.
]

#proof[
  + *Kernels and images on stalks.*

    - *Compare kernels.* The inclusion $ops.ker phi arrow.r.hook shf.f$ induces a map
      $(ops.ker phi)_P -> ops.ker(phi_P)$.  It is injective: equality of
      germs is equality after restricting to a common neighborhood, also in
      the kernel presheaf.  Conversely, an element of $ops.ker(phi_P)$ is
      represented by a section $s in shf.f (U)$ whose image has zero germ at $P$.
      After shrinking $U$
      around $P$, $phi(s)$ is zero, so the same germ is represented by a section
      of $ops.ker phi$.  This proves
      $(ops.ker phi)_P simeq ops.ker(phi_P)$.

    - *Compare images.* For the image, a germ in
      $ops.im(phi_P)$ is locally represented by some $phi(s)$, hence belongs to
      the stalk of the image presheaf.  Sheafification does not change stalks,
      giving $(ops.im phi)_P simeq ops.im(phi_P)$.

  + *Injectivity and surjectivity on stalks.*

    - *Detect injectivity.* By the first isomorphism, $phi$ is injective exactly when every
      $ops.ker(phi_P)$ is zero.  A sheaf is zero exactly when all its stalks are
      zero, so this is equivalent to every $phi_P$ being injective.

    - *Detect surjectivity.* Likewise,
      $phi$ is surjective exactly when $ops.im phi=shf.g$; taking stalks and using
      the image isomorphism shows that this is equivalent to every $phi_P$ being
      surjective.

  + A sequence is exact at a sheaf precisely when its image sheaf equals the
    next kernel sheaf.  The preceding identifications turn this equality on
    every stalk into the usual equality of image and kernel for abelian
    groups.  Since equality of subsheaves can be checked on all stalks, the
    original sequence is exact exactly when all stalk sequences are exact.
]

#block(sticky: true)[#strong[Application: II.1.3]] <sup-proof-1-3>

#exercise(title: "Exercise 1.3")[
  + Show that $phi:shf.f->shf.g$ is surjective exactly when every section
    $s in shf.g (U)$ locally lifts: some cover $U=union U_i$ admits
    $t_i in shf.f (U_i)$ with $phi(t_i)=s|_(U_i)$.
  + Give a surjective sheaf morphism whose map on sections over some open
    set is not surjective.
]

#proof[
  + *The local lifting criterion.*

    - *Obtain local lifts from surjective stalk maps.* Suppose first that $phi$ is surjective.  By Exercise 1.2, every stalk map
      $phi_P$ is surjective.  Given $s in shf.g (U)$ and $P in U$, choose a germ
      $t_P in shf.f_P$ mapping to $s_P$.  Represent $t_P$ by a section on a
      neighborhood $V_P subset.eq U$.  Equality of the two germs means that,
      after shrinking $V_P$ once more, $phi(t_P)=s|_(V_P)$.  The neighborhoods
      $V_P$ cover $U$ and give the required local lifts.

    - *Recover surjectivity from local lifts.* Conversely, local lifts imply that every germ of $shf.g$ has a preimage:
      represent the germ by $s in shf.g (U)$ and choose one member of the lifting
      cover which contains the point.  Thus every $phi_P$ is surjective, and
      Exercise 1.2 implies that $phi$ is surjective.

  + *Failure of surjectivity on global sections.*

    - *Construct a locally surjective morphism.* Take $X=RR\/ZZ$, and let $cal(C)_RR$ and $cal(C)_(RR\/ZZ)$ be the sheaves
      of continuous functions with values in the indicated additive groups.
      The map
      $
        exp:cal(C)_RR -> cal(C)_(RR\/ZZ),
        quad t mapsto t mod ZZ,
      $
      is locally surjective because the quotient map $RR->RR\/ZZ$ has local
      continuous sections.  Hence it is a surjective sheaf morphism.

    - *Rule out a global lift.* On the
      open set $X$ itself, however, the identity map $X->RR\/ZZ$ has no
      continuous lift $h:RR\/ZZ->RR$.  Indeed, with $q:RR->RR\/ZZ$ the
      quotient map, $h(q(t))-t$ would be a continuous integer-valued function
      on the connected space $RR$, hence constant.  But its values at $t=0$
      and $t=1$ differ by $1$, since $q(0)=q(1)$, a contradiction.
      Therefore the map on
      global sections is not surjective.
]

#block(sticky: true)[#strong[Application: II.1.4]] <sup-proof-1-4>

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

#block(sticky: true)[#strong[Application: II.1.5]] <sup-proof-1-5>

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

#block(sticky: true)[#strong[Application: II.1.6]] <sup-proof-1-6>

#exercise(title: "Exercise 1.6")[
  + For a subsheaf $shf.f' subset.eq shf.f$, show that $shf.f->shf.f\/shf.f'$ is surjective
    with kernel $shf.f'$, giving $0->shf.f'->shf.f->shf.f\/shf.f'->0$.
  + Conversely, show that an exact sequence $0->shf.f'->shf.f->shf.f''->0$
    identifies $shf.f'$ with a subsheaf of $shf.f$ and $shf.f''$ with its quotient.
]

#proof[
  + Let $q:shf.f->shf.f\/shf.f'$ be the canonical map.  At a point $P$, it is
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

#block(sticky: true)[#strong[Application: II.1.7]] <sup-proof-1-7>

#exercise(title: "Exercise 1.7")[
  For a sheaf morphism $phi:shf.f->shf.g$, show
  $ops.im phi simeq shf.f\/ops.ker phi$ and $ops.coker phi simeq shf.g\/ops.im phi$.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the quotient with the image.* The morphism $phi$ factors through its image,
    $shf.f->shf.f\/ops.ker phi->ops.im phi arrow.r.hook shf.g$.
    On every stalk, the middle map is the ordinary first-isomorphism-theorem map
    $shf.f_P\/ops.ker(phi_P)->ops.im(phi_P)$, hence is an isomorphism.  By
    Proposition 1.1, it is an isomorphism of sheaves, proving
    $shf.f\/ops.ker phi simeq ops.im phi$.

  + *Identify the cokernel with the quotient.* By definition, $ops.coker phi$ is the sheafification of the presheaf
    $U mapsto shf.g (U)\/ops.im(phi_U)$.  The quotient morphism
    $shf.g->shf.g\/ops.im phi$ kills the presheaf
    image, so it induces a canonical morphism from $ops.coker phi$ to this
    quotient.  On every stalk, this is the identity of the quotient group:
    both sides are
    $shf.g_P\/ops.im(phi_P)$.  Thus
    $ops.coker phi simeq shf.g\/ops.im phi$.
]

#block(sticky: true)[#strong[Application: II.1.8]] <sup-proof-1-8>

#exercise(title: "Exercise 1.8")[
  Show that $Gamma(U, dot)$ is left exact: if
  $0->shf.f'->shf.f->shf.f''$ is exact, then
  $0->Gamma(U, shf.f')->Gamma(U, shf.f)->Gamma(U, shf.f'')$ is exact. It need not be
  right exact; compare Exercise 1.21.
]

#proof[
  #set enum(numbering: "1.")

  + *Check injectivity and one inclusion.* Write the sequence as
    $0->shf.f'->^i shf.f->^q shf.f''$ and fix an open set $U$.
    Since $i$ is an injective sheaf morphism, Exercise 1.2 shows that
    $i_U$ is injective.  Also $q_U compose i_U=0$, so
    $ops.im(i_U) subset.eq ops.ker(q_U)$.

  + *Glue lifts for the reverse inclusion.* For the reverse inclusion, let $s in shf.f (U)$ satisfy $q_U(s)=0$.
    Exactness on stalks gives, near every $P in U$, a section
    $t_P in shf.f'(V_P)$ with $i(t_P)=s|_(V_P)$.  On overlaps, the sections
    $t_P$ agree because $i$ is injective there.  They glue to
    $t in shf.f'(U)$, and the separatedness axiom for $shf.f$ gives
    $i_U(t)=s$.  Hence $ops.im(i_U)=ops.ker(q_U)$.

    There is generally no reason for $q_U$ to be surjective: the counterexample
    in Exercise 1.3 already supplies a surjective sheaf morphism which is not
    surjective on global sections.
]

#block(sticky: true)[#strong[Application: II.1.9]] <sup-proof-1-9>

#exercise(title: "Exercise 1.9 (Direct Sum)")[
  For sheaves $shf.f$ and $shf.g$ on $X$, show that
  $U mapsto shf.f (U) times shf.g (U)$ is a sheaf. Show that the resulting
  $shf.f plus.o shf.g$ is both a direct sum and a direct product in the category
  of sheaves of abelian groups.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the sheaf.* Put $shf.h (U)=shf.f (U) times shf.g (U)$, with restrictions taken componentwise.
    Suppose $(s_i,t_i) in shf.h (U_i)$ are compatible on a cover of $U$.  The
    sections $s_i$ glue uniquely to $s in shf.f (U)$, and the $t_i$ glue uniquely
    to $t in shf.g (U)$.  Then $(s,t)$ is the unique section of $shf.h (U)$ which
    restricts to every $(s_i,t_i)$.  Hence $shf.h$ is a sheaf.

  + *Verify the product property.* Let $i_f(s)=(s,0)$ and $i_g(t)=(0,t)$ be the inclusions, and let $p_f,p_g$
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
]

#block(sticky: true)[#strong[Application: II.1.10]] <sup-proof-1-10>

#exercise(title: "Exercise 1.10 (Direct Limit)")[
  For a direct system of sheaves $shf.f_i$, define $ops.colim shf.f_i$ as the sheaf
  associated to $U mapsto ops.colim shf.f_i (U)$. Prove its universal property as a
  direct limit in the category of sheaves.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the canonical cocone.* Let $cal(P)$ be the presheaf $cal(P)(U)=ops.colim_i shf.f_i (U)$, and let
    $cal(P)^+$ be its associated sheaf.  The canonical maps
    $shf.f_i (U)->cal(P)(U)->cal(P)^+(U)$ commute with restrictions and with the
    transition maps, so they form a cocone $shf.f_i->cal(P)^+$.

  + *Factor through the presheaf colimit.* Now let $(u_i:shf.f_i->shf.g)$ be any compatible cocone whose target
    $shf.g$ is a sheaf.  For each open $U$, the universal property of the
    colimit of abelian groups gives a unique map
    $
      u_U:cal(P)(U)=ops.colim_i shf.f_i (U) -> shf.g (U)
    $
    whose composite with every canonical map is $(u_i)_U$.  Naturality of the
    $u_i$ and uniqueness of the colimit map show that the $u_U$ commute with
    restrictions.  Hence they form a presheaf morphism $u:cal(P)->shf.g$.

  + *Extend uniquely through sheafification.* Because $shf.g$ is a sheaf, the universal property of sheafification extends
    $u$ uniquely to $u^+:cal(P)^+->shf.g$.  This map factors the original cocone,
    and any other such factorization restricts to the same map on $cal(P)$, so
    it is equal to $u^+$.  Therefore $cal(P)^+$ has the universal property of
    $ops.colim_i shf.f_i$.
]

#block(sticky: true)[#strong[Application: II.1.11]] <sup-proof-1-11>

#exercise(title: "Exercise 1.11")[
  If $X$ is noetherian and $shf.f_i$ is a direct system of sheaves, show that
  $U mapsto ops.colim shf.f_i (U)$ already is a sheaf. In particular,
  $Gamma(X, ops.colim shf.f_i)=ops.colim Gamma(X, shf.f_i)$.
]

#proof[
  #set enum(numbering: "1.")

  + *Reduce the sheaf axiom to a finite cover.* Write $cal(P)(U)=ops.colim_i shf.f_i (U)$.  Because $X$ is noetherian,
    every open subset of $X$ is quasi-compact.  We check the sheaf axiom for an
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
    stage.  There are only finitely many overlaps $U_a inter U_b$, so filteredness
    again gives one index $k$ at which all overlap equalities hold simultaneously.

  + *Glue and prove uniqueness.* The resulting compatible sections in $shf.f_k (U_a)$ glue uniquely to a
    section $t in shf.f_k (U)$.  Its image in $cal(P)(U)$ restricts to every
    $s_a$, proving existence.  For uniqueness, if two elements of $cal(P)(U)$
    have equal restrictions, represent them at a common stage.  Their
    restrictions become equal at finitely many later stages, hence at one common
    stage; uniqueness in that sheaf then makes the two elements equal in the
    colimit.  Thus $cal(P)$ is already a sheaf.

  + *Identify the sections of the colimit sheaf.* Exercise 1.10 therefore requires no further sheafification.  Taking $U=X$
    in its pointwise definition gives
    $
      Gamma(X, ops.colim_i shf.f_i)
      = ops.colim_i Gamma(X, shf.f_i).
    $
]

#block(sticky: true)[#strong[Application: II.1.12]] <sup-proof-1-12>

#exercise(title: "Exercise 1.12 (Inverse Limit)")[
  For an inverse system $shf.f_i$, show that $U mapsto op("lim") shf.f_i (U)$ is a sheaf
  and has the universal property of $op("lim") shf.f_i$ in the category of sheaves.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the presheaf of compatible tuples.* Put $cal(L)(U)=op("lim")_i shf.f_i (U)$, with restrictions defined
    componentwise.  Thus a section of $cal(L)(U)$ is a compatible tuple
    $(s_i)_i$ with $s_i in shf.f_i (U)$.

  + *Verify the sheaf axiom componentwise.* Given compatible sections $s_a=(s_(a,i))_i in cal(L)(U_a)$ on a cover of
    $U$, fix $i$.  The sections $s_(a,i)$ glue uniquely in the sheaf $shf.f_i$
    to a section $s_i in shf.f_i (U)$.  For every arrow $i->j$ in the inverse
    system, the image of $s_i$ and the section $s_j$ have identical restrictions
    to every $U_a$; uniqueness in $shf.f_j$ makes them equal.  Hence $(s_i)_i$
    is a section of $cal(L)(U)$, and componentwise uniqueness proves the sheaf
    axiom.

  + *Verify the limit property.* The projections $cal(L)->shf.f_i$ form a limiting cone.  If a sheaf $shf.g$
    has a compatible cone $u_i:shf.g->shf.f_i$, define
    $u_U(s)=((u_i)_U(s))_i$.  These maps commute with restrictions, so they form
    a sheaf morphism $u:shf.g->cal(L)$.  Its composites with the projections are
    the $u_i$, and those equations determine every component of $u$, proving
    uniqueness.  This is the universal property of the inverse limit.
]

#block(sticky: true)[#strong[Application: II.1.15]] <sup-proof-1-15>

#exercise(title: "Exercise 1.15 (Sheaf Hom)")[
  Show that $ops.hom(shf.f|_U, shf.g|_U)$ is naturally an abelian group and that
  $U mapsto ops.hom(shf.f|_U, shf.g|_U)$ is a sheaf, denoted
  $shf.hom (shf.f,shf.g)$.
]

#proof[
  #set enum(numbering: "1.")

  + *Define sections, restrictions, and operations.* Put
    $shf.hom (shf.f,shf.g)(U)=
    ops.hom(shf.f|_U, shf.g|_U)$.
    If $V subset.eq U$, restriction sends a morphism $alpha$ to
    $alpha|_V$.  Addition and inverses are defined componentwise:
    $(alpha+beta)_W=alpha_W+beta_W$ for every $W subset.eq U$.  Naturality of
    $alpha$ and $beta$ shows that these operations again give sheaf morphisms,
    so every $shf.hom (shf.f,shf.g)(U)$ is an abelian group and every
    restriction map is a homomorphism.

  + *Glue compatible local morphisms.* It remains to check the sheaf axiom.  Let $U=union_i U_i$ and suppose that
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

  + *Prove uniqueness.* If two such morphisms exist, their values on every section over every
    $W subset.eq U$ agree on the cover ${W inter U_i}$ and hence agree by the
    uniqueness axiom for $shf.g$.  The gluing is therefore unique, proving that
    $shf.hom (shf.f,shf.g)$ is a sheaf of abelian groups.
]

#block(sticky: true)[#strong[Application: II.1.18]] <sup-proof-1-18>

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

  #set enum(numbering: "1.")

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
]

#block(sticky: true)[#strong[Application: II.5.1]] <sup-proof-5-1>

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
  - *Restriction to opens.* We first isolate the local-to-global step used below.  If
    $j_i:U_i arrow.r.hook X$ is an open cover, then a morphism of sheaves is
    an isomorphism if and only if every $j_i^*$-restriction is an isomorphism.
    Moreover, restriction to an open subset commutes with finite direct sums,
    tensor products, and sheaf Hom:
    $
       j_i^* tensor(shf.f, shf.g) & simeq
                                    tensor(j_i^*shf.f, j_i^*shf.g), \
      j_i^* shf.hom (shf.f,shf.g) & simeq
                                    shf.hom (j_i^*shf.f,j_i^*shf.g).
    $
    Indeed, the open subsets of $U_i$ are exactly the open subsets of $X$
    contained in $U_i$, so the two definitions of sheaf Hom agree on every
    such open; in the tensor case one additionally uses the universal property
    of sheafification.

  - *Choose affine trivializations.* Thus, after constructing a
    canonical morphism, we may test whether it is an isomorphism on any
    trivializing cover of $shf.e$.  Since affine opens form a basis of a
    scheme, this cover may be refined so that
    $
      U_i=ops.spec A_i
      quad "and" quad
      shf.e|_(U_i) simeq tildeOf(A_i^(r_i)).
    $
    On a fixed member, write $r=r_i$; the rank may vary
    between members of the cover.  This is the precise sense in which
    the parts relying on local freeness
    reduce to finite-free algebra.  We leave the elementary restriction
    assertions to the reader.

  - *Glue the local inverses.* For the isomorphism assertion,
    local inverses agree on overlaps because they invert the same morphism;
    Exercise 1.15 glues them to a global inverse.

  #set enum(numbering: "a)", spacing: 1em)

  + *The double-dual comparison.*

    - *Construct the canonical morphism.* There is an evaluation morphism
      $
        shf.e -> (shf.e^or)^or,
        quad e mapsto (lambda mapsto lambda(e)).
      $

    - *Restrict to an affine trivialization.* Restrict this map to one of the affine opens $U_i$ above.  Under
      $shf.e|_(U_i) simeq tildeOf(A_i^r)$ and the restriction--Hom
      identification, it becomes exactly
      $
        A_i^r -> ((A_i^r)^or)^or,
        quad m mapsto (lambda mapsto lambda(m)).
      $

    - *Compute the finite-free inverse.* If $e_1,dots.c,e_r$ is the standard basis and
      $e_1^or,dots.c,e_r^or$ its dual basis, the inverse is
      $
        Phi mapsto sum_(k=1)^r Phi(e_k^or)e_k.
      $

    - *Compare restrictions and glue.* The same formula over $shf.o_X(W)$ for every open $W subset.eq U_i$
      commutes with restriction, since the basis and its dual restrict to
      the corresponding bases on $W$.  Thus it gives a sheaf inverse, and
      the restricted evaluation map is an isomorphism.  The
      local-to-global step gives $(shf.e^or)^or simeq shf.e$.

  + *The dual–tensor–Hom comparison.*

    - *Construct the canonical morphism.* Define
      $
        alpha:tensor(shf.e^or, shf.f, over: shf.o_X)
        -> shf.hom_(shf.o_X)(shf.e,shf.f)
      $
      by $alpha(tensor(lambda, s))(e)=lambda(e)s$.

    - *Restrict the source and target.* Restricting to $U_i$ turns
      its source and target into
      $
        tensor((shf.o_(U_i)^r)^or, shf.f|_(U_i), over: shf.o_(U_i))
        quad "and" quad
        shf.hom (shf.o_(U_i)^r,shf.f|_(U_i)).
      $

    - *Identify the local comparison.* Both are canonically $(shf.f|_(U_i))^r$: the first by distributing
      tensor product over the finite direct sum, and the second because a map
      out of a finite free module is determined by the images of its basis.
      Under these identifications, $alpha|_(U_i)$ is the identity.  It is
      therefore an isomorphism on the cover and hence on $X$.

    - *Write its inverse on sections.* Explicitly,
      on any open $W subset.eq U_i$ put $R=shf.o_X(W)$ and
      $N=shf.f (W)$.  The inverse finite-free map sends $v:R^r->N$ to
      $sum_(k=1)^r tensor(e_k^or, v(e_k))$.  This formula commutes with
      restriction.  It applies even when $shf.f$ is not quasi-coherent, so no
      affine module presentation of $shf.f$ is needed.

  + *The tensor–Hom adjunction.*

    - *Describe maps from the tensor sheaf.* This part does not use local freeness and need not be reduced to affine
      opens.  Since the sheaf tensor product is the sheafification of the
      presheaf tensor product, specifying a morphism
      $u:tensor(shf.e, shf.f)->shf.g$ is equivalent to specifying compatible
      balanced maps
      $
        beta_U:shf.e (U) times shf.f (U) -> shf.g (U),
        quad beta_U(e,s)=u_U(tensor(e, s)).
      $

    - *Curry the compatible bilinear family.* Here $u_U$ is the map on sections induced by $u$.  For
      $s in shf.f (U)$, the resulting element of sheaf Hom is the entire
      family $e mapsto beta_V(e,s|_V)$ for opens $V subset.eq U$;
      compatibility of $beta$ with restrictions is precisely what makes
      this family a morphism of restricted sheaves.  Currying $beta_U$ for
      every $U$ gives
      $
        tildeOf(u):shf.f -> shf.hom (shf.e,shf.g),
        quad tildeOf(u)(s)(e)=u(tensor(e, s)).
      $

    - *Construct the inverse correspondence.* Conversely, from $v:shf.f->shf.hom (shf.e,shf.g)$ define
      $u_v(tensor(e, s))=v(s)(e)$.  Bilinearity gives a morphism from the tensor
      product.  Checking on local sections shows that the two constructions
      are inverse and natural.  Therefore
      $
        ops.hom(tensor(shf.e, shf.f, over: shf.o_X), shf.g)
        simeq ops.hom(shf.f, shf.hom (shf.e,shf.g)).
      $

  + *The projection formula.*

    - *Construct the canonical morphism.* In this part, $f:X->Y$, $shf.f$ is an $shf.o_X$-module, and
      $shf.e$ is a locally free $shf.o_Y$-module of finite rank.
      There is a natural morphism
      $
        theta:tensor(f_*shf.f, shf.e, over: shf.o_Y)
        -> f_*tensor(shf.f, f^*shf.e, over: shf.o_X),
        quad tensor(s, e) mapsto tensor(s, f^*e).
      $

    - *Restrict to a trivializing cover of the target.* Let $j:V arrow.r.hook Y$ be a member of a trivializing cover for
      $shf.e$, and write $f_V:f^(-1)(V)->V$ for the restriction of $f$.  Directly
      from the definition of pushforward,
      $
        (f_*shf.f)|_V simeq (f_V)_*(shf.f|_(f^(-1)(V))),
      $
      while functoriality of pullback gives
      $
        (f^*shf.e)|_(f^(-1)(V))
        simeq f_V^*(shf.e|_V)
        simeq shf.o_(f^(-1)(V))^r.
      $

    - *Identify both sides as a finite direct sum.* Consequently, after restricting $theta$ to $V$, its two sides reduce as
      follows:
      $
           (tensor(f_*shf.f, shf.e))|_V & simeq tensor((f_V)_*(shf.f|_(f^(-1)(V))), shf.o_V^r)
                                          simeq ((f_V)_*(shf.f|_(f^(-1)(V))))^r, \
        (f_*tensor(shf.f, f^*shf.e))|_V & simeq (f_V)_* tensor(shf.f|_(f^(-1)(V)), shf.o_(f^(-1)(V))^r) \
                                        & simeq (f_V)_*((shf.f|_(f^(-1)(V)))^r)
                                          simeq ((f_V)_*(shf.f|_(f^(-1)(V))))^r.
      $

    - *Check the comparison and conclude.* The final isomorphism is checked on every open $W subset.eq V$:
      both sides are $shf.f (f^(-1)(W))^r$.  Under the displayed chain,
      $theta|_V$ is the identity on this finite direct sum.  Hence $theta$ is
      locally, and therefore globally, an isomorphism.  Inverting it gives the
      formula in the exercise.
]
