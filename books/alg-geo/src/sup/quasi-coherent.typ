#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#import "@preview/fletcher:0.5.8": diagram, edge, node
#show: show-theorion

== QC — Quasi-coherent and coherent operations <sup-qc>

This section applies #book-link(<sup-sc>)[SC] and #book-link(<sup-al>)[AL] through
the affine correspondence. The following results remain in
#book-link(<text-ii-5>)[II.5] and serve as the main-text index:

- Proposition 5.1: stalks, principal-open sections, and global sections of the associated sheaf.
- Proposition 5.2: exactness, fully faithfulness, tensor products, direct sums, and affine pushforward and pullback.
- Lemma 5.3, Proposition 5.4, and Corollary 5.5: clearing denominators, affine locality, and the affine equivalence.
- Propositions 5.6–5.7: exactness of affine sections and preservation under kernels, cokernels, images, and extensions.
- Proposition 5.8: the stated pullback and pushforward preservation results.
- Proposition 5.9 and Corollary 5.10: ideals and closed subschemes.

When applying the affine dictionary, specify the canonical map and check
its restrictions on principal opens before using SL-1. Abstractly isomorphic
stalks do not show that a specified morphism is an isomorphism.

#metadata(none) <sup-qc-1>
#proposition(number: "QC-1", title: "Associated sheaf and global sections")[
  For $X=ops.spec A$, an $A$-module $M$, and any $shf.o_X$-module $shf.f$,
  there is a natural adjunction
  $ops.hom(tildeOf(M), shf.f, over: shf.o_X) simeq
  ops.hom(M, Gamma(X, shf.f), over: A)$.
  (Ex. II.5.3)
]

#proof[

  + *Construct the sheaf morphism.* Given $u:M->Gamma(X, shf.f)$, define a morphism
    $tildeOf(u):tildeOf(M)->shf.f$ as follows.  On a distinguished open
    $D(a)$, a section of $tildeOf(M)$ is a fraction $m/a^n$, and we put
    $
      tildeOf(u)_(D(a))(m/a^n)
      = a^(-n) u(m)|_(D(a)).
    $
    The section $a$ is a unit in $shf.o_X\(D(a))$, so it acts invertibly
    on $shf.f\(D(a))$; the universal property of $M_a$ makes the formula
    well-defined. The dashed arrow is this unique localized map:
    #align(center)[#diagram(
      cell-size: 23mm,
      $M edge("r", ->) edge("dr", u_a, ->) & M_a edge("d", ->, stroke: #(dash: "dashed")) \ & shf.f\(D(a))$,
    )]
    Here $u_a(m)=u(m)|_(D(a))$. For $D(b) subset.eq D(a)$, restricting the formula to
    $D(b)$ gives the unique localized linear map extending
    $m mapsto u(m)|_(D(b))$.  Thus the formulas commute with restrictions
    and agree on $D(a) inter D(b)=D(a b)$.  They define a sheaf morphism
    because distinguished opens form a basis.

  + *Take global sections.* Conversely, a morphism $v:tildeOf(M)->shf.f$ gives on global sections an
    $A$-linear map
    $
      M isoBy("5.1d") Gamma(X, tildeOf(M))
      morph(Gamma(X, v), cat.mod(A)) Gamma(X, shf.f).
    $

  + *Check inverses and naturality.* Starting with $u$ and taking global sections recovers $u$.  Starting with
    $v$, the preceding formula recovers $v$ on every $D(a)$, hence on all
    opens.  The two constructions are natural, giving the required
    bijection.
]


#metadata(none) <sup-qc-2>
#proposition(number: "QC-2", title: "Colimits")[
  A small colimit of quasi-coherent sheaves, computed in all $shf.o_X$-modules,
  is quasi-coherent. On an affine open, the canonical map
  $ops.colim_i tildeOf(M_i) -> tildeOf(ops.colim_i M_i)$ is an isomorphism.
  This assertion does not extend to arbitrary ambient products or inverse
  limits; see QC-10.
]

#proof[

  + *Restrict the diagram to an affine open.* Restrict the given diagram to an affine $U=ops.spec A$. Restriction
    commutes with sheaf colimits, since it commutes with their presheaf
    construction and sheafification. By the affine equivalence, write its
    objects as $tildeOf(M_i)$ and its arrows as the associated module maps.

  + *Verify the colimit comparison.* Their structure maps to $tildeOf(ops.colim_i M_i)$ define the stated
    comparison. QC-1's adjunction says that the associated-sheaf functor is
    a left adjoint even when the target sheaf is arbitrary. It therefore
    preserves these colimits. More explicitly, on stalks the comparison is
    $ops.colim_i (M_i)_idl.p -> (ops.colim_i M_i)_idl.p$;
    localization, a left adjoint on modules, makes this an isomorphism.
    SL-1 applies to this specified map.
    #align(center)[#diagram(
      cell-size: 21mm,
      $tildeOf(M_i) edge("r", ->) edge("dr", ->) & ops.colim_i tildeOf(M_i) edge("d", ->) \ & tildeOf(ops.colim_i M_i)$,
    )]

  + *Return to the scheme.* Quasi-coherence on the affine cover
    proves the global assertion; all comparisons are induced by the same
    colimit structure maps, so they agree under restriction.
]

#metadata(none) <sup-qc-3>
#proposition(number: "QC-3", title: "Hom and finite presentation")[
  + For $M$ finitely presented over $A$ and $N$ arbitrary, the canonical map
    $tildeOf(ops.hom(M, N, over: A))->shf.hom_(shf.o)(tildeOf(M),tildeOf(N))$
    is an isomorphism on $ops.spec A$. Its principal-open comparisons are
    #book-link(<sup-al-4>)[AL-4].

  + Consequently, on a scheme, if $shf.f$ is a
    finitely presented module sheaf and $shf.g$ is quasi-coherent, then
    $shf.hom (shf.f,shf.g)$ is quasi-coherent.
]

#proof[

  + *Compute on principal opens.* Evaluation defines the comparison by QC-1. On a distinguished open
    $D(a)$ its source has sections $ops.hom(M, N, over: A)_a$, while its
    target has sections $ops.hom(M_a, N_a, over: A_a)$ by affine full
    faithfulness. The map is
    $u/a^n mapsto (m/a^q mapsto u(m)/a^(n+q))$. AL-4 proves that this map is an
    isomorphism when $M$ is finitely presented. These formulas commute
    with further localization, so SL-1 gives the sheaf isomorphism.

  + *Apply the affine calculation locally.* For the global assertion, refine finite-presentation neighborhoods to
    affine opens. A finite presentation by free sheaves is the associated
    sheaf of a finite module presentation by QC-7. On these charts, the
    preceding computation applies to the quasi-coherent restriction of
    $shf.g$, proving quasi-coherence of the sheaf Hom.
]

#metadata(none) <sup-qc-4>
#corollary(number: "QC-4", title: "Hom and pullback")[
  For $f:X->Y$, finite locally free $shf.e$ on $Y$, and any module
  $shf.g$, the canonical map
  $f^*shf.hom (shf.e,shf.g)->shf.hom (f^*shf.e,f^*shf.g)$ is an
  isomorphism. It is induced by pulling back evaluation. Use the finite
  locally free duality of #book-link(<sup-sc-11>)[SC-11];
  finite presentation alone does not suffice
  for arbitrary base change.
]

#proof[

  + *Construct the comparison.* Pull evaluation back and use the tensor--Hom adjunction to form the
    canonical map.
    #align(center)[#diagram(
      cell-size: 36mm,
      $
        f^*shf.hom (shf.e,shf.g) times.o f^*shf.e edge("r", ->) edge("d", ->, stroke: #(dash: "dashed")) & f^*shf.g edge("d", ops.id, ->) \
        shf.hom (f^*shf.e,f^*shf.g) times.o f^*shf.e edge("r", ->) & f^*shf.g
      $,
    )]

  + *Compute on a trivializing cover.* Cover $Y$ by opens $V$ trivializing $shf.e$ with finite
    rank $r$, and restrict to $f^(-1)(V)$. On these opens, both Hom sheaves
    identify with $r$ copies of the respective second argument. Pullback
    preserves finite direct sums, and evaluation in a basis shows that the
    comparison is the identity on these copies. Thus it is an isomorphism
    on a source open cover.

  + *Glue the local inverses.* Since it was defined by evaluation, these local
    comparisons are restrictions of one morphism; their inverses agree on
    overlaps by uniqueness. This proves the claim without requiring
    $shf.g$ to be quasi-coherent.
]

#metadata(none) <sup-qc-5>
#proposition(number: "QC-5", title: "Pushforward under a qcqs morphism")[
  + For a quasi-compact, quasi-separated morphism of schemes $f:X->Y$,
    the direct image of a quasi-coherent module is quasi-coherent. This is the
    qcqs version of #book-link(<text-ii-5>)[II.5, Proposition 5.8(c)]; see also
    #link("https://stacks.math.columbia.edu/tag/01LA")[Stacks, Section 26.24].

  + For an affine morphism, use the affine pushforward formula of Proposition
    5.2. A closed immersion is finite by #book-link(<sup-cs-1>)[CS-1] and the
    finite ring-map criterion. (Ex. II.5.5(b))
]

#proof[

  + *Choose finite affine covers and the section kernel.* Fix $V=ops.spec A$ in $Y$ and a finite affine cover $U_i$ of
    $f^(-1)(V)$, supplied by quasi-compactness. Quasi-separatedness gives
    a finite affine cover $W_(i j l)$ of every $U_i inter U_j$: apply the
    target criterion to the diagonal over $V$ and its affine product charts.
    Write $M_i=Gamma(U_i, shf.f)$ and
    $N_(i j l)=Gamma(W_(i j l), shf.f)$, with their induced $A$-module
    structures. The sheaf axiom identifies $M=Gamma(f^(-1)(V), shf.f)$
    as the kernel of the difference of restrictions
    $product_i M_i -> product_(i,j,l) N_(i j l)$.

  + *Localize the kernel.* For $a in A$, intersect every chart with $f^(-1)(D(a))$. These are
    the principal opens given by the images of $a$ in their coordinate
    rings. Quasi-coherence identifies their sections with $(M_i)_a$ and
    $(N_(i j l))_a$. All products are finite, so exact localization of
    the preceding kernel gives the canonical isomorphism
    $M_a -> Gamma(f^(-1)(D(a)), shf.f)$,
    $m/a^n mapsto m|_(f^(-1)(D(a)))/(f^*a)^n$; hence
    it respects every further restriction.

  + *Identify the direct image.* SL-1 on the distinguished basis
    identifies $(f_*shf.f)|_V$ with $tildeOf(M)$. Affine opens cover $Y$,
    giving the result. When $f$ is affine the cover has a single affine
    inverse image, and this is precisely restriction of scalars in II.5.2.

  + *Apply the quotient dictionary.* For a closed immersion, CS-1 writes
    each entire inverse image of an affine target $ops.spec A$ as
    $ops.spec(A/I)$. The module $A/I$ is generated by $1$ (Check!).
    Target locality of finite morphisms, LP-25, therefore proves finiteness.
]

#metadata(none) <sup-qc-6>
#corollary(number: "QC-6", title: "Coherence and finiteness")[
  Here coherence is used on Noetherian schemes, as in Hartshorne.

  + Finite direct sums, kernels, cokernels, images, extensions, tensor products,
    and sheaf Hom of coherent modules remain coherent by the main-text results
    above and QC-3. Infinite sums need not remain coherent.

  + If $f:X->Y$ is finite between Noetherian schemes, $f_*$ preserves
    coherence: the affine dictionary uses restriction of scalars from a finite
    $A$-algebra $B$, under which a finite $B$-module is finite over $A$.
    (Ex. II.5.5(c))

  The projection formula has its more general ringed-space form in
  #book-link(<sup-sc-11>)[SC-11].
]

#proof[

  + *Check finiteness of the module operations.* On a Noetherian affine chart, coherent sheaves correspond to finite
    modules. Submodules and quotients of finite modules are finite; a
    finite set of lifts of generators of a quotient together with generators
    of the kernel generates an extension. Finite sums and tensor products
    are finite. A finite presentation of $M$ realizes
    $ops.hom(M, N, over: A)$ as a submodule of a finite power of $N$, so
    this Hom is finite too. The finite-generation assertions in this
    step are purely algebraic checks over a Noetherian ring (Check!).

  + *Identify the sheaf operations.* The main-text exactness and tensor comparisons,
    together with QC-3 for Hom, identify these actual sheaf operations with
    their module operations on every chart. They consequently remain
    coherent.

  + *Finite pushforward preserves coherence.*

    + *Choose affine charts and a finite module.* Let $V=ops.spec A subset.eq Y$ be affine.  Because $f$ is finite,
      $f^(-1)(V)=ops.spec B$ is affine and $B$ is a finite $A$-module.  Write
      $
        shf.f|_(f^(-1)(V)) simeq tildeOf(M),
      $
      where $M$ is a finite $B$-module.

    + *Identify the direct-image sheaf.* Proposition 5.2(d) identifies
      $
        (f_*shf.f)|_V simeq tildeOf(attach(M, bl: A)).
      $
      Indeed, restriction of pushforward is pushforward by $f|_(f^(-1)(V))$:
      both evaluate on $W subset.eq V$ as $shf.f\(f^(-1)(W))$.  On a
      distinguished $D(a) subset.eq V$, this is $M_a$, with $A$ acting
      through $A->B$.  These localization identifications commute with
      restriction and hence identify the sheaves on the entire basis.

    + *Check finiteness over the base ring.* If $b_1,dots.c,b_r$ generate $B$ over $A$ and
      $m_1,dots.c,m_s$ generate $M$ over $B$, then the finitely many elements
      $b_i m_j$ generate $M$ over $A$ (Check!).  Thus $M$ is finite as an $A$-module,
      so $(f_*shf.f)|_V$ is coherent.  The affine opens $V$ cover $Y$;
      therefore $f_*shf.f$ is coherent.
]

#metadata(none) <sup-qc-7>
#proposition(number: "QC-7", title: "Local presentations")[
  Let $shf.f$ be an $shf.o_X$-module on a scheme $X$.

  + The sheaf $shf.f$ is quasi-coherent if and only if every $x in X$
    has an open neighborhood $U$ on which there is an exact sequence
    $
      shf.l_1 -> shf.l_0 -> shf.f|_U -> 0,
    $
    with $shf.l_0,shf.l_1$ free $shf.o_U$-modules, possibly of infinite rank.

  + If $X$ is Noetherian, then $shf.f$ is coherent if and only if such
    presentations exist around every point with both free modules of
    finite rank. (Ex. II.5.4)
]

#proof[

  + *Reduce to affine presentation neighborhoods.* Restriction to an open set preserves sheaf cokernels, since these are
    sheafified presheaf cokernels, and preserves direct sums by the same
    construction.  Refine any given presentation cover by affine opens.
    Quasi-coherence and coherence are defined by such local presentations
    by associated modules, so it suffices to establish the assertions on
    these refined opens.

  + *Present a quasi-coherent sheaf.* First suppose that $shf.f$ is quasi-coherent.  On a suitable affine open
    $U=ops.spec A$, we may write $shf.f|_U simeq tildeOf(M)$.  Choose generators
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

  + *Recover quasi-coherence from a presentation.* Conversely, suppose on an affine open $U=ops.spec A$ that
    $shf.f|_U$ is the cokernel of a morphism
    $
      bigOPlus(shf.o_U, j in J) -> bigOPlus(shf.o_U, i in I).
    $
    By the full faithfulness in Proposition 5.2(a), this morphism comes from
    an $A$-linear map
    $bigOPlus(A, j in J)->bigOPlus(A, i in I)$.  Exactness of the tilde functor
    identifies its sheaf cokernel with the tilde of the module cokernel.
    Hence $shf.f|_U$ is quasi-coherent, and so is $shf.f$.

  + *Prove the finite-presentation criterion for coherence.* Now assume $X$ is noetherian.  If $shf.f$ is coherent, on an affine open
    $U=ops.spec A$ it has the form $tildeOf(M)$ with $A$ noetherian and $M$
    finite.  Choose a surjection $A^r->M$.  Its kernel is a submodule of the
    finite $A$-module $A^r$, hence is finite (Check!); choosing finitely many generators
    gives an exact sequence
    $
      A^s -> A^r -> M -> 0.
    $
    Sheafification gives the required finite-free cokernel presentation.
    Conversely, the cokernel of $shf.o_U^s->shf.o_U^r$ is the tilde of the
    cokernel of $A^s->A^r$, which is a finite $A$-module.  It is therefore
    coherent.  This proves both equivalences.
]

#metadata(none) <sup-qc-8>
#remark(number: "QC-8", title: "Closed-subscheme index")[
  For ideals, quotients, and the classical vanishing-ideal application, use
  #book-link(<sup-cs-1>)[CS-1] and #book-link(<sup-cs-6>)[CS-6]. The identification
  of a classical variety with its scheme is in #book-link(<sup-vs>)[VS].
]

#metadata(none) <sup-qc-9>
#proposition(number: "QC-9", title: "The two-point DVR model")[
  + Let $R$ be a DVR with fraction field $K$. A module sheaf on
    $ops.spec R$ is specified by an $R$-module $M$, a $K$-vector space $L$,
    and a $K$-linear map $tensor(M, K, over: R)->L$, which determines the only
    nontrivial restriction.

  + It is quasi-coherent if and only if this map is an
    isomorphism. (Ex. II.5.2)
]

#proof[

  + *Describe the space and its rings.* Let $eta=(0)$ be the generic point and let $x=(pi)$ be the closed point,
    where $pi$ is a uniformizer.  The only open subsets of $X$ are
    $nothing$, ${eta}=D(pi)$, and $X$ (Check! using the prime ideals
    of a DVR).  Moreover
    $
      shf.o_X (X)=R, quad shf.o_X ({eta})=K,
    $
    and the restriction map is the inclusion $R->K$.

  + *Extract the module data.* An $shf.o_X$-module $shf.f$ therefore gives
    $
      M=shf.f\(X), quad L=shf.f\({eta}),
    $
    where $M$ is an $R$-module, $L$ is a $K$-vector space, and restriction is
    an $R$-linear map $rho:M->L$.  By the universal property of localization,
    $rho$ is equivalently a $K$-linear map
    #align(center)[#diagram(
      cell-size: 20mm,
      $M edge("r", ->) edge("dr", rho, ->) & tensor(M, K, over: R) edge("d", bar(rho), ->, stroke: #(dash: "dashed")) \ & L$,
    )]
    $
      bar(rho):tensor(M, K, over: R) -> L,
      quad tensor(m, a) mapsto a rho(m).
    $

  + *Recover the sheaf from the data.* Conversely, such data define an $shf.o_X$-module by assigning $M$ to
    $X$, $L$ to ${eta}$, zero to the empty set, and using the associated map
    $M->L$ for restriction.  There are no other nontrivial covers, so the
    sheaf axiom is automatic.  These constructions are inverse, also on
    morphisms: a morphism of triples is a pair of linear maps on $M$ and
    $L$ commuting with $bar(rho)$.  Every cover of a nonempty open contains
    that open itself (Check!), which justifies the sheaf assertion above.

  + *Characterize quasi-coherence.* If $shf.f$ is quasi-coherent, the affine characterization of
    quasi-coherent sheaves gives
    $shf.f simeq tildeOf(M)$, where $M=Gamma(X, shf.f)$.  On $D(pi)={eta}$,
    $
      tildeOf(M)({eta})=M_pi=tensor(M, K, over: R).
    $
    Thus $bar(rho)$ is an isomorphism.  Conversely, if $bar(rho)$ is an
    isomorphism, the identity on $M$ and $bar(rho)$ on ${eta}$ give an
    isomorphism $tildeOf(M) simeq shf.f$.  Hence $shf.f$ is quasi-coherent.
]

#metadata(none) <sup-qc-examples>
#metadata(none) <sup-qc-10>
#example(number: "QC-10")[
  On $ops.spec ZZ$, take $shf.f=product_(n>=0) shf.o_X$ in
  all module sheaves. On $D(2)$, its localization comparison is AL-13,
  so it is not quasi-coherent and is not $tildeOf(product_(n>=0) ZZ)$.
]

#proof[
  Products of sheaves are computed on sections, so the map on $D(2)$ is $(product_n ZZ)_2 -> product_n ZZ[1/2]$. Its image has one common bounded power of $2$ as denominator. The tuple $(1/2^n)_n$ has no such bound by AL-13. The affine criterion for quasi-coherence fails for this actual localization map.
]

#metadata(none) <sup-qc-11>
#example(number: "QC-11")[
  On $ops.spec k$, the infinite direct sum of copies of $k$ is
  not finite-dimensional, hence its sheaf is not coherent.
]

#proof[
  The coordinate vectors are linearly independent, and every finite list of vectors involves only finitely many coordinates. It cannot span the next coordinate vector. Coherence over the field would require a finite-dimensional module.
]

#metadata(none) <sup-qc-12>
#example(number: "QC-12")[
  For $A=ZZ$, $B=ZZ\/2ZZ$, $M=ZZ\/2ZZ$, and $N=ZZ$,
  the Hom base-change map has zero source and nonzero target, although $M$
  is finitely presented.
]

#proof[
  Every homomorphism $ZZ\/2ZZ->ZZ$ is zero, since its value at $1$ is killed by $2$. After base change, both $M$ and $N$ become $B$, and $ops.hom(B, B, over: B)=B!=0$. Thus the canonical comparison is the map from zero to $B$, although the presentation $ZZ ->^(2) ZZ -> M ->0$ is finite.
]

#metadata(none) <sup-qc-13>
#example(number: "QC-13")[
  The structure-sheaf pushforward along $sch.a^1_k->ops.spec k$
  corresponds to $k[t]$ and is not coherent. (Ex. II.5.5(a))
]

#proof[
  Affine pushforward is restriction of scalars, so its module is $k[t]$ over $k$. The monomials are linearly independent and no finite list spans them. Hence this pushforward is not coherent.
]

#metadata(none) <sup-qc-14>
#example(number: "QC-14")[
  On $sch.p^1_k$, the tensor of the global sections of
  $shf.o (-1)$ and $shf.o (1)$ is zero, while the global sections of their
  tensor product are $k$. Use the twisting-sheaf computations in
  #book-link(<text-ii-5>)[II.5].
]

#proof[
  The standard two affine charts compute $Gamma(shf.o (-1))=0$, while $tensor(shf.o (-1), shf.o (1)) simeq shf.o$ has global sections $k$. Thus the canonical global-sections tensor map has source zero and target $k$; it is not an isomorphism.
]
