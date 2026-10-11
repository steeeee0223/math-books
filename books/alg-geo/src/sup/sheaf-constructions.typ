#import "@preview/fletcher:0.5.8" as fletcher: *
#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

#supplement-numbering("SC")

== SC — Sheaf constructions and exactness <sup-sc>

Throughout this section, $X$ is a topological space. Unless rings are specified,
we work in the categories $cat.ab(X)$ and $cat.mod(X)$, with modules over a fixed sheaf of commutative rings $shf.o$. Sheafification is denoted by $shf.f^+$.
The definitions in #book-link(<text-ii-1>)[II.1, D5\~D7] and the local
representative and equality criteria of SL will be used throughout.

#proposition(key: "sup-sc-1", title: "Exactness calculus")[

  Let $u:shf.f to shf.g$ be a morphism of $cat.ab(X)$ or $cat.mod(X)$. Recall the definitions in #book-link(<text-ii-1>)[(II.1, D5\~D7)].

  + _Subsheaf & quotient sheaf._ Let $shf.f'$ be a subsheaf of $shf.f$.

    + The stalk $shf.f'_x$ of the subsheaf $shf.f'$ is a sub-object of $shf.f_x$.
    + The stalk of $shf.f\/shf.f'$ is $(shf.f\/shf.f')_x simeq shf.f_x\/shf.f'_x$.

  + _Kernel, image & cokernel._

    + The stalk of $ops.ker u$ is $(ops.ker u)_x simeq ops.ker(u_x)$.
    + The stalk of $ops.im u$ is $(ops.im u)_x simeq ops.im(u_x)$.
    + The stalk of $ops.coker u$ is $(ops.coker u)_x simeq ops.coker(u_x)$.
    + $ops.im u$ is a subsheaf of $shf.g$.
    + The canonical maps give
      $shf.f\/(ops.ker u) simeq ops.im u$ and $ops.coker u simeq shf.g\/(ops.im u)$.

  + _Injectivity, surjectivity & isomorphisms._

    + The following conditions are equivalent:
      - $u$ is injective.
      - $u_U$ is injective for every open $U subset X$.
      - $u_x$ is injective for every $x in X$.
    + The following conditions are equivalent:
      - $u$ is surjective.
      - $u_x$ is surjective for every $x in X$.
      - For every open $U$ and $s in shf.g\(U)$, there are a cover $U=union_i U_i$ and $t_i in shf.f\(U_i)$ with $u(t_i)=s|_(U_i)$ for every $i$.
    + In general, if $u$ is surjective, the morphism $u(U):shf.f\(U) to shf.g\(U)$ may not be surjective.
    + $u$ is an isomorphism if and only if it is injective and surjective.

  + _Exact sequences._

    + For every subsheaf $shf.f' subset shf.f$, the canonical sequence
      $0 to shf.f' to shf.f to shf.f\/shf.f' to 0$ is exact.
    + A sequence is exact if and only if its sequence of stalks is exact at every point.
    + $0 to shf.f' morph(phi, "") shf.f morph(psi, "") shf.f'' to 0$ is exact if and only if its maps
      identify $shf.f'$ with a subsheaf and $shf.f''$ with the quotient.
  (Ex. II.1.2\~7)
]

#proof[
  + _Subsheaf and quotient sheaf._

    + The inclusion $shf.f' to shf.f$ induces an injection on stalks:
      if a section of $shf.f'$ becomes zero as a germ in $shf.f$, it is
      zero on a smaller neighborhood by SL-1, and hence zero there in $shf.f'$.
    + The quotient presheaf has sections $shf.f\(U)\/shf.f'\(U)$.
      Its germs map onto $shf.f_x\/shf.f'_x$ by taking representatives.
      A representative maps to zero precisely when, after shrinking, it is
      a section of $shf.f'$, by SL-1. This identifies its stalk with the
      algebraic quotient. Sheafification preserves that stalk by SL-5.

  + _Kernel, image and cokernel._

    + A germ in $ops.ker(u_x)$ is represented by a section whose image
      vanishes on a smaller neighborhood. That representative lies in the
      sectionwise kernel. This proves the kernel stalk formula by SL-1.
    + Every element of $ops.im(u_x)$ is represented by the image of a
      local section. Equality of two such germs is equality after shrinking.
      Thus the image presheaf has stalk $ops.im(u_x)$, and SL-5 gives
      the same stalk for its sheafification.
    + The cokernel presheaf has sections
      $shf.g\(U)\/ops.im(u_U)$. Representing a germ in $shf.g_x$ gives
      surjectivity onto $shf.g_x\/ops.im(u_x)$; a germ in the kernel
      belongs to the image on a smaller neighborhood by SL-1.
      Sheafification again preserves these stalks.
    + The inclusion of the image presheaf into $shf.g$ extends to a
      sheaf morphism $ops.im u to shf.g$. Its stalk maps are the
      inclusions $ops.im(u_x) to shf.g_x$. A section mapping to zero
      therefore has every germ zero, and is zero by SL-1. Thus the map
      is sectionwise injective. Its sectionwise image is a subsheaf:
      local sections glue in $ops.im u$, and their images glue in $shf.g$.
    + The canonical maps
      $
        shf.f\/(ops.ker u) & to ops.im u, \
               ops.coker u & to shf.g\/(ops.im u)
      $
      induce respectively the first-isomorphism map
      $shf.f_x\/ops.ker(u_x) to ops.im(u_x)$ and the identity of
      $shf.g_x\/ops.im(u_x)$. The first-isomorphism theorem (Check!)
      and II.1, Proposition 1.1 show that both sheaf maps are isomorphisms.

  + _Injectivity, surjectivity and isomorphisms._

    + By definition, injectivity means $ops.ker u=0$. The sectionwise
      kernel vanishes exactly when every $u_U$ is injective. The kernel
      stalk formula and SL-1 identify this with injectivity of every $u_x$.
    + Surjectivity means $ops.im u=shf.g$. By the image stalk formula,
      this implies surjectivity of every $u_x$. Conversely, if every $u_x$
      is surjective, lift the germ of $s in shf.g\(U)$ at each point.
      Represent the lift on a neighborhood and shrink by SL-1 until its
      image equals the restriction of $s$. These neighborhoods give the
      required lifting cover. A lifting cover makes every germ lift and
      makes every section locally belong to $ops.im u$; these local
      sections glue in that subsheaf. This proves all three equivalences.
    + For failure on sections, take $X=sch.p^1_k$ and distinct $k$-points
      $p,q$. Let $shf.k$ be the subsheaf of $shf.o_X$ consisting of
      regular functions vanishing at whichever of $p,q$ lie in the open.
      The quotient map $shf.o_X to shf.o_X\/shf.k$ is surjective by
      the quotient stalk formula. The local classes of $0$ on
      $X minus \{q\}$ and $1$ on $X minus \{p\}$ agree on their overlap,
      where the quotient is zero, and hence glue. A global lift would
      be a regular function with values $0$ at $p$ and $1$ at $q$.
      Such a function does not exist: the two affine charts identify
      $Gamma(sch.p^1_k, shf.o_X)$ with $k[t] inter k[t^(-1)]=k$
      inside $k[t,t^(-1)]$ (Check!).
    + Injectivity and surjectivity together mean that every stalk map
      is bijective. A bijective homomorphism is an isomorphism (Check!),
      so II.1, Proposition 1.1 gives the sheaf isomorphism. The converse
      follows by applying an inverse on stalks.

  + _Exact sequences._

    + The quotient stalk formula identifies the canonical sequence
      with $0 to shf.f'_x to shf.f_x to shf.f_x\/shf.f'_x to 0$.
      Alternatively, the image of the inclusion is $shf.f'$ and the
      kernel of the quotient map is $shf.f'$ by the same germ calculation;
      the quotient map is surjective by the preceding part. Thus the
      canonical sheaf sequence is exact.
    + Two subsheaves with equal stalks are equal: each section of either
      belongs locally to the other by SL-1, and these local sections glue.
      Apply this to the image and kernel at each term of a complex.
      Their stalk formulas identify sheaf exactness with algebraic exactness
      at every stalk. The complex condition itself can also be checked
      on stalks by SL-1.
    + In a short exact sequence, $phi$ is injective and identifies
      $shf.f'$ with $ops.ker psi$. The first-isomorphism map for $psi$
      identifies its quotient with $ops.im psi=shf.f''$.
      Conversely, these identifications give the canonical exact
      sequence from the first part.

  All constructions respect the induced scalar actions in the module case.
  For ring sheaves the same germ calculations give ideals, images and
  quotients by ideals; the ring first-isomorphism theorem gives the
  corresponding quotient-to-image comparison (Check!).
]

For ring sheaves, kernels are ideal sheaves, images are subring sheaves,
and quotients by ideals are sheafified sectionwise quotients. Their stalks
are the corresponding algebraic ideals, images, and quotients. Here
surjectivity means surjectivity on stalks; a categorical epimorphism of
rings need not be surjective.

#proposition(key: "sup-sc-2", title: "Limits and colimits")[
  Let $(shf.f_i)_i$ be a small diagram of sheaves in $cat.ab(X)$,
  $cat.ring(X)$, or $cat.mod(X)$, with a fixed sheaf of scalars in the module case.

  + _Direct limit._ Define the _direct limit_ $ops.colim_i shf.f_i$ to be
    the sheafification of the presheaf $U mapsto ops.colim_i shf.f_i (U)$,
    with restrictions induced by those of the $shf.f_i$.

    + This construction satisfies the universal property of the colimit in
      the chosen category of sheaves. (See CAT-6.)
    + For every sheaf $shf.g$ in that category, there is a natural bijection
      $ops.hom(ops.colim_i shf.f_i, shf.g) simeq lim_i ops.hom(shf.f_i, shf.g)$,
      where the limit on the right uses the induced contravariant diagram.
    + The stalk of the direct limit is
      $(ops.colim_i shf.f_i)_x simeq ops.colim_i (shf.f_i)_x$.
    + If the diagram is filtered and $X$ is Noetherian, the presheaf
      $U mapsto ops.colim_i shf.f_i (U)$ is already a sheaf. In particular,
      $Gamma(X, ops.colim_i shf.f_i) simeq ops.colim_i Gamma(X, shf.f_i)$.

  + _Inverse limit._ Define the _inverse limit_ $lim_i shf.f_i$ to be
    the sheafification of the presheaf $U mapsto lim_i shf.f_i (U)$,
    with componentwise restrictions. This presheaf is already a sheaf.

    + This construction satisfies the universal property of the limit in
      the chosen category of sheaves. (See CAT-6.)
    + For every sheaf $shf.g$ in that category, there is a natural bijection
      $ops.hom(shf.g, lim_i shf.f_i) simeq lim_i ops.hom(shf.g, shf.f_i)$.
    + For every open $U subset X$, the sections of the inverse limit are
      $Gamma(U, lim_i shf.f_i) simeq lim_i Gamma(U, shf.f_i)$.
    + For a finite diagram, the stalk of the inverse limit is
      $(lim_i shf.f_i)_x simeq lim_i (shf.f_i)_x$.
      The canonical comparison need not be an isomorphism for an infinite diagram.

  (Ex. II.1.10\~12)
]

#proof[
  + _Direct limit._ Write $shf.h^-\(U)=ops.colim_i shf.f_i (U)$.

    + A cocone from $(shf.f_i)_i$ to a sheaf $shf.g$ gives, on each open,
      a unique map $shf.h^-\(U) to shf.g\(U)$. Uniqueness makes these maps
      commute with restrictions. Sheafification extends the resulting
      presheaf map uniquely to $(shf.h^-)^+ to shf.g$ by SL-5.
      This is the colimit property in the chosen category. Ring operations
      and module scalar actions extend through local representatives;
      their identities hold locally and hence globally by SL-1.
      #align(center)[#diagram(
        cell-size: 20mm,
        $shf.h^- edge("r", ->) edge("dr", ->) & (shf.h^-)^+ edge("d", ->, stroke: #(dash: "dashed")) \ & shf.g$,
      )]
    + Composition with the colimit structure maps identifies a morphism
      to $shf.g$ with a compatible family of morphisms $shf.f_i to shf.g$.
      These families form the limit of the contravariant Hom diagram.
      The factorization just constructed is its inverse, and the formulas
      commute with morphisms in $shf.g$.
    + Sheafification leaves stalks unchanged by SL-5. For abelian groups
      and rings, the stalk of $shf.h^-$ is an iterated colimit, first over
      the diagram and then over neighborhoods of $x$. A map out of either
      order is the same compatible family of maps, so the two colimits
      agree. For modules, the scalars pass from $shf.o\(U)$ to $shf.o_x$.
      Present the colimit by generators and additive, scalar and diagram
      relations. Each element and each derivation of a relation uses only
      finitely many sections and scalars. SL-1 represents them on a common
      neighborhood. This gives both surjectivity and injectivity of
      $
        ops.colim_i (shf.f_i)_x to ((shf.h^-)^+)_x.
      $
    + Suppose the diagram is filtered and $X$ is Noetherian. Every open
      is quasi-compact (Check!), so a cover of $U$ has a finite subcover.
      First check separatedness: represent two sections of $shf.h^-\(U)$
      at one stage. Equality on each member of a finite subcover holds
      at a later stage by CAT-8. Filteredness supplies one stage at which
      all these equalities hold, and separatedness in that sheaf gives
      equality on $U$.

      Now take compatible sections on a cover and retain a finite subcover.
      Represent its finitely many sections at a common stage. Their
      equalities on the finitely many overlaps hold at one further common
      stage by CAT-8 and filteredness. They glue in that sheaf, giving a
      section of $shf.h^-\(U)$. On any omitted cover member, the glued
      section has the prescribed restriction by separatedness on its
      intersections with the finite subcover. The empty open has the
      terminal group, ring or module. Thus $shf.h^-$ is a sheaf.
      For rings, the finite-stage equality criterion follows from the
      underlying filtered colimit of sets: addition and multiplication
      are computed at a common stage (Check!). For modules the analogous
      computation uses the fixed ring $shf.o\(U)$ on each open.
      No sheafification changes the sections, and taking $U=X$ proves
      the global-sections formula.

  + _Inverse limit._ Write $shf.l^-\(U)=lim_i shf.f_i (U)$.

    + Compatible families on an open cover glue componentwise in each
      $shf.f_i$. Every diagram relation holds on that cover and hence for
      the glued sections by uniqueness. Thus $shf.l^-$ is already a sheaf.
      A cone induces sectionwise maps to $shf.l^-$; their composites with
      the projections determine them uniquely. They commute with
      restrictions and preserve the operations, proving the limit property.
      #align(center)[#diagram(
        cell-size: 20mm,
        $shf.g edge("r", ->, stroke: #(dash: "dashed")) edge("dr", ->) & lim_i shf.f_i edge("d", ->) \ & shf.f_i$,
      )]
    + Composition with the projections identifies a morphism from
      $shf.g$ with a compatible family $shf.g to shf.f_i$. The cone
      factorization is the inverse, and gives the natural Hom bijection.
    + The section formula follows from the construction of $shf.l^-$,
      since its sheafification is canonically itself.
    + For a finite diagram, represent its finitely many component germs
      on one neighborhood. Its finitely many arrow equations hold as
      germs, and hence on a smaller common neighborhood by SL-1.
      These sections define a section of the limit, proving surjectivity
      of the comparison. Equal component germs become equal on a common
      neighborhood, proving injectivity. The maps preserve all operations.
      For failure with infinite limits, take the sheaf of continuous
      real functions $shf.h$ on $RR$. At $0$, the section $(s_n)_n$ of
      $product_(n>=1) shf.h$, where $s_n(t)=max(0, abs(t)-1/n)$,
      has zero germ in each component. It has nonzero product germ,
      since every neighborhood contains a point where some $s_n$ is
      nonzero. Products are sectionwise limits by the first part, so
      the comparison is not injective.
]

#proposition(key: "sup-sc-3", title: "Direct and inverse image")[
  Let $f:X to Y$ be continuous, $shf.f$ a sheaf on $X$, and $shf.g$ a sheaf on $Y$.

  + _Direct image._ Define the _direct image_ sheaf $f_*shf.f$ on $Y$ to be the sheafification of the presheaf $V mapsto shf.f\(f^(-1)(V))$. It is already a sheaf (Check!).

    + The stalk of the direct image sheaf is $(f_*shf.f)_y=ops.colim_(y in V) shf.f\(f^(-1)(V))$.
    + For $x in X$ there is a canonical map $(f_*shf.f)_(f(x)) to shf.f_x$.
      It need not be an isomorphism. It is an isomorphism if $f$ is an open embedding.
    + For abelian groups, $f_*$ is left exact.

  + _Inverse image._ Define the _inverse image_ sheaf $f^(-1)shf.g$ on $X$ to be the sheafification of the presheaf $U mapsto ops.colim_(f(U) subset V) shf.g\(V)$.

    + The stalk of the inverse image sheaf is $(f^(-1)shf.g)_x simeq shf.g_(f(x))$ for every $x in X$.
    + For abelian groups, $f^(-1)$ is exact.

  + Adjunction of direct and inverse image.

    + There is a natural bijection
      $
        ops.hom(f^(-1)shf.g, shf.f) simeq ops.hom(shf.g, f_*shf.f).
      $
      The unit is $shf.g to f_*f^(-1)shf.g$ and the counit is
      $f^(-1)f_*shf.f to shf.f$.
    + For $g:Y to Z$, $(g compose f)_* simeq g_*f_*$ and
      $(g compose f)^(-1) simeq f^(-1)g^(-1)$, compatibly with the adjunctions.

  + For abelian-group sheaves, $Gamma(V, dot)$ is left exact.
    It need not be right exact.
  (Ex. II.1.8, II.1.18)
]

#proof[
  + _Direct image._

    + Apply the definition of a stalk to the direct-image section formula.
      This gives the displayed neighborhood colimit.
    + Restriction to neighborhoods of $x$ gives the comparison on germs
      $
        (f_*shf.f)_(f(x)) to shf.f_x, quad [s,V] mapsto [s,f^(-1)(V)].
      $
      For a discrete two-point source mapping to one point, take the
      sheaf assigning $product_(x in U) ZZ$ to $U$. Its source stalks
      are $ZZ$, whereas its direct-image stalk is $ZZ times ZZ$.
      The comparison is a coordinate projection, which is not injective.
      If $f$ is an open embedding, every neighborhood of $x$ contains
      one of the form $f^(-1)(V)$ with $V$ a neighborhood of $f(x)$.
      These neighborhoods are cofinal, so the stalk comparison is an
      isomorphism.
    + Let $0 to shf.f' to shf.f to shf.f''$ be exact. On an open $U$,
      a section of $shf.f$ mapping to zero lifts locally to $shf.f'$ by
      SC-1. Injectivity makes these lifts agree on overlaps, so they glue
      uniquely. The map on sections from $shf.f'$ is also injective.
      Apply this to $U=f^(-1)(V)$ for every open $V$ to prove left
      exactness of $f_*$.

  + _Inverse image._ Write $(f^(-1)shf.g)^-$ for the presheaf in the statement.

    + Its stalk at $x$ consists of representatives $s in shf.g\(V)$,
      with $x in U$ and $f(U) subset V$. Send such a representative to
      $s_(f(x))$. Conversely, a representative on a neighborhood $V$
      of $f(x)$ is admissible on $U=f^(-1)(V)$. Equality of germs is
      realized by shrinking $V$, and then $U$, by SL-1. These maps are
      inverse; SL-5 preserves this identification after sheafification.
    + The stalk maps of an inverse-image sequence are the original stalk
      maps at $f(x)$. Hence SC-1 proves exactness for abelian groups.

  + _Adjunction and composition._

    + For $s in shf.g\(V)$, write $s^f$ for its canonical image on
      $f^(-1)(V)$ in the inverse-image sheaf. Given
      $beta:shf.g to f_*shf.f$, define
      $
        (f^(-1)shf.g)^- (U) & to shf.f\(U), \
           [s in shf.g\(V)] & mapsto beta_V(s)|_U,
                              quad U subset f^(-1)(V).
      $
      Compatibility with restrictions makes this well-defined on the
      colimit. Sheafification extends it uniquely to
      $Psi(beta):f^(-1)shf.g to shf.f$. Conversely, define
      $
        Phi(alpha)_V:shf.g\(V) & to shf.f\(f^(-1)(V)), \
                             s & mapsto alpha_(f^(-1)(V))(s^f)
      $
      for $alpha:f^(-1)shf.g to shf.f$. These maps commute with
      restrictions. Their composites recover $beta_V(s)$ and
      $alpha(s^f|_U)$, respectively. Every inverse-image section is
      locally of the latter form by SL-5, so the sheaf axiom proves
      that $Phi$ and $Psi$ are inverse. The formulas commute with
      precomposition and postcomposition, proving naturality.
      The identity maps give the unit and counit: the unit sends $s$
      to $s^f$, and the counit sends $t^f|_U$ to $t|_U$.
    + Direct images compose because inverse images of open sets compose.
      Applying the two adjunctions successively gives
      $
        ops.hom(f^(-1)g^(-1)shf.h, shf.f)
        simeq ops.hom(shf.h, g_*f_*shf.f)
        simeq ops.hom((g compose f)^(-1)shf.h, shf.f).
      $
      Thus CAT-2 gives the natural inverse-image isomorphism. The
      displayed identifications use the same adjunction bijections, so
      their units and counits are the corresponding composites.

  + The sectionwise argument in the direct-image part proves left
    exactness of $Gamma(V, dot)$. To see failure of right exactness,
    use $X=sch.p^1_k$ and the quotient by functions vanishing at two
    distinct $k$-points constructed in the proof of SC-1. Its canonical
    map is surjective on stalks, but the glued class with respective
    values $0$ and $1$ has no global lift. Thus global sections need
    not preserve surjectivity.
]

#proposition(key: "sup-sc-4", title: "Direct sums")[
  Let $(shf.f_i)_(i in I)$ be abelian-group sheaves or $shf.o$-modules.

  + _Direct sum._ Define the _direct-sum sheaf_ $bigOPlus(shf.f_i, i in I)$
    to be the sheafification of the presheaf $U mapsto bigOPlus(shf.f_i (U), i in I)$,
    with componentwise restrictions.

    + The sections of the direct-sum sheaf on $U$ identify with families
      $(s_i) in product_i shf.f_i(U)$ such that every $x in U$ has a
      neighborhood $W subset U$ on which all but finitely many $s_i$ vanish.
    + The stalk of the direct-sum sheaf is
      $(bigOPlus(shf.f_i, i in I))_x simeq bigOPlus((shf.f_i)_x, i in I)$.

  + If $I$ is finite, the canonical injections and projections identify
    $bigOPlus(shf.f_i, i in I) simeq product_i shf.f_i$.
  (Ex. II.1.9)
]

#proof[
  + _Direct sum._ Write $(bigOPlus(shf.f_i, i in I))^-$ for the
    sectionwise direct-sum presheaf.

    + The component maps give a morphism from its sheafification to
      the product sheaf of SC-2. By SL-5 a section is locally represented
      by a finite-support family, so its image has the stated property.
      If all components of such a local representative vanish, the
      representative is zero; SL-1 therefore proves injectivity.
      Conversely, a family with the stated property gives, near each
      point, a section of the direct-sum presheaf. The images of these
      representatives in the sheafification agree on overlaps by the
      established injectivity, so they glue. This proves the section formula.
    + The direct-sum presheaf is the filtered colimit of the finite
      sectionwise sums. Finite algebraic sums are finite products,
      and their stalks are the corresponding finite sums by SC-2.
      Commuting the neighborhood colimit with the colimit over finite
      subsets of $I$, and applying SL-5, gives the direct sum of the stalks.
      The comparison sends a local finite-support family to its component germs.

  + If $I$ is finite, the sectionwise direct sum is the sectionwise
    product, which is already a sheaf by SC-2. Its coordinate injections
    and projections satisfy
    $p_i compose i_j=0$ for $i!=j$, $p_i compose i_i=ops.id$, and
    $sum_i i_i compose p_i=ops.id$ (Check!). These identities give both
    universal properties and the claimed canonical identification.
    All maps respect the scalar actions for modules.
]

#proposition(key: "sup-sc-5", title: "Sheaf Hom")[
  Let $shf.f,shf.g$ be sheaves of sets, abelian groups, rings, or $shf.o$-modules on $X$.

  + _Sheaf Hom._ Define the _Hom sheaf_ $shf.hom\(shf.f,shf.g)$ to be
    the sheafification of the presheaf $U mapsto ops.hom(shf.f|_U, shf.g|_U)$,
    with restriction $u mapsto u|_V$ for $V subset U$. This presheaf is
    already a sheaf of sets. For abelian-group morphisms it is an
    abelian-group sheaf, and for $shf.o$-linear morphisms it is an $shf.o$-module.

    + The global sections of the Hom sheaf are
      $Gamma(X, shf.hom\(shf.f, shf.g))=ops.hom(shf.f, shf.g)$.
    + The restriction of the Hom sheaf to an open $U$ is
      $shf.hom\(shf.f,shf.g)|_U simeq shf.hom\(shf.f|_U,shf.g|_U)$.

  + _Stalk comparison._ For modules, define the _Hom stalk comparison_
    by sending a germ of a local morphism to its induced map on stalks:
    $
      shf.hom_(shf.o)(shf.f,shf.g)_x to ops.hom(shf.f_x, shf.g_x, over: shf.o_x).
    $

    + This map is an isomorphism if $shf.f$ has a finite presentation on a neighborhood of $x$.
    + This map need not be an isomorphism for arbitrary $shf.f$.
  (Ex. II.1.15)
]

#proof[
  + _Sheaf Hom._ Apply SL-3 on each open $U$ to compatible local
    morphisms. They glue uniquely, proving that the Hom presheaf is
    already a sheaf. Addition and scalar multiplication of local
    morphisms commute with restrictions and satisfy the abelian-group
    and module identities sectionwise (Check!).

    + Its sections on $X$ are precisely morphisms $shf.f to shf.g$,
      by the defining assignment.
    + On an open $W subset U$, both restricted constructions have
      sections $ops.hom(shf.f|_W, shf.g|_W)$, with the same restrictions.
      These identities give the canonical restriction isomorphism.

  + _Stalk comparison._ Taking the induced map on stalks is unchanged
    by shrinking a representative of a local morphism, so defines the
    stated comparison.

    + Choose a neighborhood of $x$ with a finite presentation
      $shf.o^m to shf.o^n to shf.f to 0$. A morphism from $shf.f$
      is exactly a morphism from $shf.o^n$ killing the relations.
      Evaluation on the standard basis identifies the Hom sheaf with
      the kernel of $shf.g^n to shf.g^m$ on that neighborhood.
      At $x$ the same cokernel universal property identifies
      $ops.hom(shf.f_x, shf.g_x, over: shf.o_x)$ with the corresponding
      kernel of finite module powers. SC-1 and SC-4 commute these
      kernels and finite powers with stalks. The resulting kernel
      isomorphism sends a local map to its induced stalk map, so it
      is the comparison in the statement.
    + On $ops.spec ZZ$, let $shf.f=bigOPlus(shf.o, n>=0)$ and $shf.g=shf.o$.
      By SC-4, at the generic point the source stalk is a direct sum
      of copies of $QQ$. Define a $QQ$-linear map by $e_n mapsto 1/p_n$,
      where the $p_n$ enumerate the positive primes. If it were a germ
      of a local sheaf morphism, restrict its representative to a
      distinguished neighborhood $D(a)$ with $a!=0$. The image of each
      basis section would be an element of $ZZ[1/a]$ whose generic germ
      is $1/p_n$, since the map $ZZ[1/a] to QQ$ is injective.
      A prime not dividing $a$ divides no power of $a$, so its inverse
      is not in $ZZ[1/a]$ (Check!). Such a prime exists by the infinitude
      of primes (Check!), giving a contradiction. The comparison is
      therefore not surjective in this example.
]

#proposition(key: "sup-sc-6", title: "Tensor sheaves and the tensor–Hom adjunction")[
  Let $shf.e,shf.f,shf.g$ be $shf.o$-modules.

  + _Tensor product._ Define the _tensor-product sheaf_
    $tensor(shf.e, shf.f, over: shf.o)$ to be the sheafification of the presheaf
    $U mapsto tensor(shf.e (U), shf.f (U), over: shf.o (U))$,
    with restrictions induced by those of the modules and the ring of scalars.

    + Composition with the pure-tensor map identifies morphisms
      $tensor(shf.e, shf.f) to shf.g$ with $shf.o$-balanced bilinear maps
      $shf.e times shf.f to shf.g$.
    + The stalk of the tensor-product sheaf is
      $(tensor(shf.e, shf.f, over: shf.o))_x simeq tensor(shf.e_x, shf.f_x, over: shf.o_x)$.

  + The tensor–Hom adjunction gives a natural bijection
    $
      ops.hom(tensor(shf.e, shf.f), shf.g) simeq
      ops.hom(shf.f, shf.hom_(shf.o)(shf.e,shf.g)).
    $
  (Ex. II.5.1(c))
]

#proof[
  + _Tensor product._

    + An $shf.o$-balanced bilinear sheaf map gives, on each open, a
      linear map from the sectionwise tensor product. The algebraic
      tensor universal property makes these maps commute with
      restrictions. SL-5 extends the presheaf map uniquely through
      sheafification. Conversely, composition with the pure-tensor map
      recovers the bilinear map; uniqueness proves that these operations
      are inverse.
      #align(center)[#diagram(
        cell-size: 22mm,
        $shf.e times shf.f edge("r", ->) edge("dr", b, ->) & tensor(shf.e, shf.f) edge("d", tilde(b), ->, stroke: #(dash: "dashed")) \ & shf.g$,
      )]
    + The balanced map on germs induces
      $
        tensor(shf.e_x, shf.f_x, over: shf.o_x) & to
                                                  (tensor(shf.e, shf.f, over: shf.o))_x, \
                               tensor(s_x, t_x) & mapsto (tensor(s, t))_x.
      $
      SL-5 represents every target germ by a section of the tensor
      presheaf, hence by a finite sum of pure tensors, proving
      surjectivity. Any equality in a tensor product is a finite
      consequence of additive and balanced relations. Represent the
      finitely many sections and scalars in such a consequence on a
      common neighborhood, and realize their germ equalities there
      by SL-1. The equality then holds in the tensor presheaf on that
      neighborhood, proving injectivity.

  + Given a bilinear sheaf map $b:shf.e times shf.f to shf.g$ and
    $t in shf.f\(U)$, assign the local morphism on $U$ whose section map
    on $W subset U$ sends $s$ to $b_W(s,t|_W)$. This defines
    $shf.f to shf.hom_(shf.o)(shf.e,shf.g)$ by SC-5. Conversely,
    evaluation of such a Hom section on an $shf.e$ section gives a
    balanced bilinear map. The two assignments commute with
    restrictions and are inverse by the algebraic tensor universal
    property (Check!). Together with the first part they give the
    stated natural tensor–Hom adjunction.
]

Inverse image retains the inverse-image ring of scalars; module pullback
extends scalars to $shf.o_X$. For the algebraic symmetric and exterior powers,
use #supplement-link(<sup-al-6>)[AL-6].

#proposition(key: "sup-sc-7", title: "Module pullback and scalar extension")[
  Let $f:(X,shf.o_X) to (Y,shf.o_Y)$ be a morphism of ringed spaces and
  $shf.g$ an $shf.o_Y$-module.

  + _Module pullback._ Define the _pullback sheaf_
    $f^*shf.g=tensor(shf.o_X, f^(-1)shf.g, over: f^(-1)shf.o_Y)$
    to be the sheafification of the presheaf
    $
      U mapsto tensor(shf.o_X(U), (f^(-1)shf.g)(U), over: (f^(-1)shf.o_Y)(U)),
    $
    with the induced restrictions.

    + The stalk of the pullback sheaf is
      $(f^*shf.g)_x simeq tensor(shf.o_(X,x), shf.g_(f(x)), over: shf.o_(Y,f(x)))$.
    + For every $shf.o_X$-module $shf.f$, the pullback adjunction gives a natural bijection
      $ops.hom(f^*shf.g, shf.f, over: shf.o_X) simeq ops.hom(shf.g, f_*shf.f, over: shf.o_Y)$.
    + The functor $f^*$ is right exact. If every $shf.o_(X,x)$ is flat over
      $shf.o_(Y,f(x))$, then $f^*$ is exact.

  + _Symmetric and exterior powers._ For $n>=0$, define the
    _symmetric-power sheaf_ $ops.sym^n shf.g$ and the
    _exterior-power sheaf_ $Lambda^n shf.g$ to be the sheafifications
    of the respective presheaves
    $
      V & mapsto ops.sym^n_(shf.o_Y(V))(shf.g\(V)), \
      V & mapsto Lambda^n_(shf.o_Y(V))(shf.g\(V)),
    $
    with induced restrictions.

    + The stalk of the symmetric-power sheaf is
      $(ops.sym^n shf.g)_y simeq ops.sym^n_(shf.o_(Y,y))(shf.g_y)$.
    + The stalk of the exterior-power sheaf is
      $(Lambda^n shf.g)_y simeq Lambda^n_(shf.o_(Y,y))(shf.g_y)$.

  + Compatibility of pullback with tensor products and powers.

    + For $shf.o_Y$-modules $shf.g,shf.h$, the canonical map gives an isomorphism
      $f^*(tensor(shf.g, shf.h)) simeq tensor(f^*shf.g, f^*shf.h)$.
    + For every $n>=0$, the canonical maps give isomorphisms
      $
        f^*(ops.sym^n shf.g) & simeq ops.sym^n(f^*shf.g), \
         f^*(Lambda^n shf.g) & simeq Lambda^n(f^*shf.g).
      $
]

#proof[
  + _Module pullback._

    + Apply the tensor stalk formula of SC-6, then the inverse-image
      stalk formula of SC-3, to the defining scalar extension. The
      scalar map becomes $shf.o_(Y,f(x)) to shf.o_(X,x)$, and the result
      is the displayed pullback stalk formula.
    + Extension of scalars identifies an $shf.o_X$-linear map
      $f^*shf.g to shf.f$ with an $f^(-1)shf.o_Y$-linear map
      $f^(-1)shf.g to shf.f$. Apply the bijection in SC-3: its explicit
      formulas identify these linear maps with $shf.o_Y$-linear maps
      $shf.g to f_*shf.f$. On pure tensors the scalar-extension map
      sends $tensor(a, s)$ to $a$ times the image of $s$.
      All identifications commute with morphisms, proving naturality.
    + The adjunction makes $f^*$ a left adjoint, so it preserves
      cokernels by CAT-10 and is right exact. If each indicated stalk
      ring is flat over the target stalk ring, the stalk formula makes
      pullback exact at every point by the algebraic flatness criterion
      (Check!). SC-1 then proves exactness of the sheaf sequence.

  + _Symmetric and exterior powers._

    + Iterate SC-6 to identify the stalk of a tensor power with the
      tensor power of the stalk. The symmetric-power presheaf is the
      quotient by permutation relations. Each relation involves
      finitely many sections. SL-1 represents those sections and any
      equality among their germs on one neighborhood, so the relation
      subpresheaf has stalk exactly the algebraic relation submodule.
      The quotient germ calculation of SC-1 and SL-5 therefore identify
      the symmetric-power stalk with $ops.sym^n_(shf.o_(Y,y))(shf.g_y)$.
    + Apply the same argument to the exterior-power quotient, using
      the alternating relations of AL-6. These also involve finitely
      many sections, so their stalk submodule is precisely the algebraic
      alternating relation submodule. Taking the quotient gives the
      exterior-power stalk formula. For $n=0$ both formulas reduce to
      the stalk of the structure sheaf.

  + _Compatibility with pullback._

    + The canonical tensor comparison is induced locally by
      $
        tensor(a, tensor(s, t)) mapsto tensor(tensor(a, s), tensor(1, t)).
      $
      Balanced relations and restriction maps respect this assignment,
      so it extends through sheafification. At each $x$ the comparison
      is scalar extension of a tensor product along
      $shf.o_(Y,f(x)) to shf.o_(X,x)$ by the stalk formulas above and SC-6.
      The algebraic scalar-extension isomorphism of AL-7 identifies
      this stalk map as an isomorphism. SC-1 gives the sheaf isomorphism.
    + Iterate the tensor comparison. Permutation and alternating
      relations map to the corresponding relations after scalar
      extension, giving canonical comparisons on the two powers.
      The power stalk formulas identify their stalks with the
      scalar-extension isomorphisms of AL-7, including degree zero.
      They are isomorphisms by SC-1.
]

#proposition(key: "sup-sc-8", title: "Constant sheaves")[
  Let $A$ be an abelian group. Define the _constant sheaf_ $shf.a$ to be
  the sheafification of the presheaf $U mapsto A$ for nonempty opens and
  $emptyset mapsto 0$, with identity restrictions between nonempty opens
  and zero restrictions to the empty open.

  + The sections of the constant sheaf on $U$ are
    $shf.a\(U)=\{s:U to A : s " is locally constant"\}$,
    with restriction of functions.
  + The stalk of the constant sheaf is $shf.a_x simeq A$ by evaluation at $x$.
  (Ex. II.1.1)
]

#proof[
  + Let $shf.a^-$ denote the presheaf in the statement, and let $shf.h$
    be the sheaf of locally constant $A$-valued functions. Compatible
    functions glue uniquely, and local constancy holds on an open cover,
    so $shf.h$ is a sheaf. The constant-function maps define
    $
      theta:shf.a^- & to shf.h, \
                  a & mapsto (x mapsto a),
    $
    with the unique map on the empty open. For a presheaf morphism
    $u:shf.a^- to shf.g$ to a sheaf, choose a cover on which a locally
    constant function $s$ has constant values $a_i$. The sections
    $u_(U_i)(a_i)$ agree on overlaps, including empty overlaps, so glue
    uniquely. Refining the cover gives the same section by uniqueness.
    The glued maps commute with restrictions and are uniquely determined
    by $u$, since every locally constant function is locally in the image of $theta$.
    Thus $(shf.h,theta)$ has the sheafification property, identifying
    $shf.a\(U)$ with the stated functions and restrictions.

  + Evaluation on a germ is well-defined, since representatives agreeing
    near $x$ have the same value at $x$. Every $a in A$ is represented
    by a constant function. Any locally constant function is constant
    on a neighborhood of $x$, so two germs with the same value agree
    there by SL-1. Evaluation is therefore an isomorphism $shf.a_x simeq A$.
]

#proposition(key: "sup-sc-9", title: "Skyscraper sheaves")[
  Let $P in X$, let $A$ be an abelian group, and let $i_P:\{P\} to X$.
  Define the _skyscraper sheaf_ $shf.s=i_(P*)A$ to be the sheafification
  of the presheaf $U mapsto A$ if $P in U$ and $U mapsto 0$ otherwise,
  with identity restrictions between opens containing $P$ and zero
  restrictions otherwise. This presheaf is already a sheaf.

  + The stalk of the skyscraper sheaf is $shf.s_x simeq A$ if
    $x in overline(\{P\})$, and $shf.s_x=0$ otherwise.
  + For $j:overline(\{P\}) to X$, the skyscraper sheaf is
    $shf.s simeq j_*shf.a$, where $shf.a$ is the constant sheaf
    with value $A$ on $overline(\{P\})$.
]

#proof[
  + If $x in overline(\{P\})$, every neighborhood of $x$ contains $P$,
    so the stalk system is constantly $A$ with identity maps.
    Otherwise, choose a neighborhood avoiding $P$; its smaller
    neighborhoods form a cofinal zero system. These computations give
    the two stalk formulas.

  + Put $Z=overline(\{P\})$. Every nonempty relatively open subset of
    $Z$ contains $P$, so any two such opens intersect. Thus every
    nonempty relatively open subset is irreducible, hence connected.
    A locally constant function on a connected space is constant (Check!).
    By SC-8, sections of the constant sheaf on $U inter Z$ are therefore
    $A$ when $U inter Z$ is nonempty and zero otherwise. For open $U$,
    meeting $Z$ is equivalent to containing $P$. The direct-image section
    formula of SC-3 now gives exactly the skyscraper assignment, with
    the same restriction maps. These identifications give the sheaf
    isomorphism $shf.s simeq j_*shf.a$.
]

#proposition(key: "sup-sc-10", title: "Finite locally free duality and projection formula")[
  Let $shf.e$ be finite locally free on a ringed space $X$.

  + _Dual sheaf._ Define the _dual sheaf_
    $shf.e^or=shf.hom_(shf.o_X)(shf.e,shf.o_X)$ to be the sheafification
    of the presheaf $U mapsto ops.hom(shf.e|_U, shf.o_X|_U, over: shf.o_X|_U)$,
    with restriction of morphisms. This presheaf is already a sheaf by SC-5.

    + The canonical evaluation map $shf.e to (shf.e^or)^or$ is an isomorphism.
    + The stalk of the dual sheaf is
      $(shf.e^or)_x simeq ops.hom(shf.e_x, shf.o_(X,x), over: shf.o_(X,x))$.
    + For every $shf.o_X$-module $shf.f$, the canonical map
      $
        tensor(shf.e^or, shf.f, over: shf.o_X) & to shf.hom_(shf.o_X)(shf.e,shf.f), \
                             tensor(lambda, s) & mapsto (e mapsto lambda(e)s)
      $
      is an isomorphism.

  + _Projection formula._ Let $f:(X,shf.o_X) to (Y,shf.o_Y)$ be a morphism
    of ringed spaces, $shf.f$ an $shf.o_X$-module, and $shf.e$ finite
    locally free on $Y$. The canonical map
    $
      tensor(f_*shf.f, shf.e, over: shf.o_Y) & to
                                               f_*(tensor(shf.f, f^*shf.e, over: shf.o_X)), \
                                tensor(s, e) & mapsto tensor(s, f^*e)
    $
    is an isomorphism.
  (Ex. II.5.1)
]

#proof[
  + _Dual sheaf._ Choose an open cover trivializing $shf.e$, with finite
    rank $r$ on each member. Sheaf Hom and tensor sheaves restrict to
    the corresponding constructions on each open by SC-5 and their
    defining presheaves. The evaluation maps commute with restrictions.

    + On a trivializing open, the double-dual evaluation has inverse
      $
        Phi mapsto sum_(i=1)^r Phi(e_i^or)e_i
      $
      in a basis and its dual. These are the finite-free identities
      over the ring of sections on every smaller open, as in AL-5
      (Check!). Thus they give inverse sheaf maps on that open.
      The local inverses agree on overlaps because they invert the
      same canonical map; SL-3 glues them to a global inverse.
    + Finite locally free sheaves have a finite presentation on a
      neighborhood of each point. Apply the Hom stalk comparison of
      SC-5 with target $shf.o_X$ to obtain the dual stalk formula.
    + On a trivializing open the dual-tensor map has inverse
      $
        v mapsto sum_(i=1)^r tensor(e_i^or, v(e_i)).
      $
      Evaluation identifies both sides with the finite power of
      $shf.f$ there, by SC-4 and SC-5. The finite-free identities of
      AL-5 (Check!) hold on every smaller open, so these are inverse
      sheaf maps. Again uniqueness makes the local inverses agree
      on overlaps, and SL-3 gives a global inverse.

  + _Projection formula._ The pure-tensor rule in the statement is
    balanced and commutes with restrictions, so SC-6 gives the
    canonical sheaf morphism $theta$. Choose a trivializing open cover
    of $Y$ for $shf.e$; on a member $V$ of rank $r$, put
    $f_V:f^(-1)(V) to V$ and $shf.f_V=shf.f|_(f^(-1)(V))$.
    The direct-image section formula identifies the restricted direct
    image with $(f_V)_*shf.f_V$, and SC-7 gives
    $(f^*shf.e)|_(f^(-1)(V)) simeq shf.o_(f^(-1)(V))^r$.
    Tensoring with a finite free module gives a finite sum by the
    algebraic tensor universal property and SC-4 (Check!).
    Direct image preserves these finite sums: on each $W subset V$
    both sides have sections $shf.f\(f^(-1)(W))^r$.
    Consequently both sides of $theta|_V$ identify with
    $((f_V)_*shf.f_V)^r$, and its pure-tensor formula becomes the
    identity on the basis components. Its inverse is therefore a
    sheaf morphism on $V$. These inverses agree on overlaps because
    they invert the same $theta$; SL-3 glues them to a global inverse.
]

#metadata(none) <sup-sc-examples>
#example(key: "sup-sc-11")[
  Let $X=NN union {infinity}$, with isolated natural numbers and tail
  neighborhoods at $infinity$. Let $shf.f_n$ be the skyscraper sheaf
  with coefficient $ZZ$ at $n$.

  + The stalk of each skyscraper sheaf at $infinity$ is $(shf.f_n)_infinity=0$.
  + The germ of $(1,1,dots)$ in $(product_n shf.f_n)_infinity$ is nonzero.
    Consequently, the canonical comparison
    $(product_n shf.f_n)_infinity to product_n (shf.f_n)_infinity$ is not injective.
]

#proof[
  + For a fixed $n$, a sufficiently small tail neighborhood of
    $infinity$ avoids $n$. All its smaller neighborhoods have zero
    sections in $shf.f_n$, so the stalk is zero.

  + Products are sectionwise by SC-2. The section with value $1$ in
    every skyscraper component remains nonzero on every tail, since
    each tail contains a natural number. Its germ is nonzero by SL-1.
    Its component germs all vanish by the first part, so the
    canonical comparison is not injective.
]

#example(key: "sup-sc-12")[
  Let $X$ and $(shf.f_n)_n$ be as in SC-11. Define $shf.g_m=product_(n<=m) shf.f_n$,
  with truncation maps $shf.g_(m+1) to shf.g_m$.

  + The stalk of each finite product at $infinity$ is $(shf.g_m)_infinity=0$.
  + The germ from SC-11 is nonzero in $(lim_m shf.g_m)_infinity$.
    Consequently, the canonical comparison
    $(lim_m shf.g_m)_infinity to lim_m (shf.g_m)_infinity$ is not injective.
]

#proof[
  + By the finite-limit comparison in SC-2, the stalk of the finite
    product is the product of the stalks. Each factor is zero by
    SC-11, so $(shf.g_m)_infinity=0$.

  + A compatible sequence of truncated finite tuples is uniquely an
    infinite tuple of coordinates (Check!). This identification
    commutes with restrictions, so the sectionwise inverse-limit
    construction of SC-2 gives $lim_m shf.g_m simeq product_n shf.f_n$.
    The germ from SC-11 remains nonzero under this isomorphism,
    whereas the inverse limit of the zero stalks is zero. Thus the
    stalk comparison is not injective.
]

#example(key: "sup-sc-13")[
  Let $Z$ consist of two distinct $k$-points on $sch.p^1_k$, with their
  reduced induced scheme structure, and let $i:Z to sch.p^1_k$ be the inclusion.

  + The restriction morphism $shf.o_(sch.p^1_k) to i_*shf.o_Z$ is surjective.
  + The induced map on global sections is the diagonal
    $k to k times k$, $a mapsto (a,a)$, and is not surjective.
  (Ex. II.1.3(b), II.1.21(c))
]

#proof[
  + At either chosen point, take neighborhoods avoiding the other
    point. Their intersections with $Z$ are the single reduced point,
    so the direct-image section formula identifies the stalk map
    with the residue-field quotient. Away from these two closed points, a neighborhood
    avoids $Z$ and the target stalk is zero. Thus the morphism is
    surjective on every stalk, and SC-1 gives sheaf surjectivity.

  + The two affine charts identify the global regular functions on
    $sch.p^1_k$ with $k[t] inter k[t^(-1)]=k$ inside $k[t,t^(-1)]$
    (Check!). Since $Z$ is the disjoint union of two reduced $k$-points,
    its global sections are $k times k$. Restriction sends a constant
    $a$ to $(a,a)$, so $(1,0)$ has no preimage.
]

#example(key: "sup-sc-14")[
  Regard $ZZ to QQ$ as a morphism of ring sheaves on a one-point space.

  + This morphism is a categorical epimorphism.
  + This morphism is not surjective on sections or stalks.
]

#proof[
  + Let two ring maps from $QQ$ to a ring agree on $ZZ$. The image of
    $a/b$ is the image of $a$ times the inverse of the image of $b$,
    so the maps agree on every rational number. This is precisely
    the categorical epimorphism property. Ring sheaves and their
    morphisms on a one-point space are the corresponding rings
    and ring maps, so the same conclusion holds for sheaves.

  + The element $1/2$ is not an integer, so the map is not surjective
    on the nonempty open. On a one-point space the stalk is the
    value on that open, proving failure of stalk surjectivity as well.
]

#example(key: "sup-sc-15")[
  Let $f$ be the morphism of one-point ringed spaces corresponding to
  $ZZ to ZZ\/2ZZ$. (See #supplement-link(<sup-al-12>)[AL-12].)

  + Multiplication by $2$ is an injective morphism of $ZZ$-modules.
  + Its pullback along $f$ is the zero endomorphism of $ZZ\/2ZZ$,
    which is not injective. Thus $f^*$ need not be left exact.
]

#proof[
  + If $2a=2b$ in $ZZ$, cancellation gives $a=b$ (Check!). Hence
    multiplication by $2$ is injective.

  + On one-point ringed spaces, SC-7 identifies pullback with scalar
    extension along $ZZ to ZZ\/2ZZ$. By AL-12 this sends the given
    endomorphism to multiplication by $2$ on $ZZ\/2ZZ$, which is zero.
    The source module is nonzero, since the classes of $0$ and $1$
    are distinct (Check!), so this map is not injective. Pullback
    therefore does not preserve the injection from the first part
    and need not be left exact.
]
