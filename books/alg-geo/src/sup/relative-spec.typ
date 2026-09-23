#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== RV — Relative Spec and vector bundles <sup-rv>

This construction uses #book-link(<sup-xl>)[XL] for gluing,
#book-link(<sup-qc>)[QC] for quasi-coherent modules, and
#book-link(<sup-al-6>)[AL-6] and #book-link(<sup-sc-7>)[SC-7] for symmetric algebras.

#metadata(none) <sup-rv-1>
#definition(number: "RV-1", title: "Relative spectrum")[
  + Let $shf.a$ be a quasi-coherent $shf.o_Y$-algebra. The relative spectrum
    $ops.spec_Y shf.a$ is obtained from $ops.spec Gamma(U, shf.a)$ over
    affine opens $U$ of $Y$.

  + The canonical localization identifications over
    principal opens identify the overlaps; for general overlaps refine to
    principal opens. These identifications satisfy the cocycle condition and
    give an affine morphism to $Y$.
]

#proof[

  + *Compare principal opens.* For $U=ops.spec A$, put $B_U=Gamma(U, shf.a)$, with its specified
    $A$-algebra map. If $D(a) subset.eq U$, quasi-coherence gives the
    canonical algebra isomorphism $B_(D(a)) simeq (B_U)_a$. It identifies
    its spectrum with the inverse image of $D(a)$ in $ops.spec B_U$.

  + *Compare affine subopens.* More generally let $W$ be an affine open contained in $U$. Restriction
    $B_U->B_W$ gives a map of spectra over $W->U$. Cover $W$ by
    principal opens $D_U(a)$ contained in $W$. Each is also the principal
    open $D_W(a|_W)$, so quasi-coherence identifies both $(B_U)_a$ and
    $(B_W)_(a|_W)$ with $Gamma(D_U(a), shf.a)$. Thus this map is an
    isomorphism over every member of that cover. XL identifies
    $ops.spec B_W$ with the entire inverse image of $W$ in $ops.spec B_U$.

  + *Identify pairwise overlaps.* For two affine opens $U,V$ of $Y$, cover their intersection by affine
    opens $W$. The preceding comparison identifies the two inverse images
    over each $W$ with $ops.spec B_W$. On a smaller affine open, all these
    comparisons are induced by restriction of sections, so transitivity of
    restriction makes them agree. XL glues the comparisons on the overlap.

  + *Check the cocycle and glue.* On triple overlaps, both composites have these same restrictions, so
    they coincide. Scheme gluing in XL gives a scheme and a morphism to
    $Y$. Its inverse image over $U$ is $ops.spec B_U$; LP's affine target
    criterion makes this morphism affine. The construction also supplies
    its canonical algebra map by restriction to these charts.
]

#metadata(none) <sup-rv-2>
#proposition(number: "RV-2", title: "Universal property")[
  + For $g:T->Y$, there is a natural bijection
    $ops.hom(T, ops.spec_Y shf.a, over: Y) simeq
    ops.hom(shf.a, g_*shf.o_T, over: shf.o_Y)$,
    where the right side consists of algebra homomorphisms.
    It sends a morphism to the induced map on the algebra of functions.

  + The structural map $shf.a->f_*shf.o_(ops.spec_Y shf.a)$ is an
    isomorphism.
]

#proof[

  + *Construct the two assignments.* A $Y$-map induces the displayed algebra map on functions. Conversely,
    from $u:shf.a->g_*shf.o_T$ and an affine $U subset.eq Y$ obtain
    $B_U->Gamma(g^(-1)(U), shf.o_T)$. The affine-target adjunction of II.2
    gives a unique morphism $g^(-1)(U)->ops.spec B_U$. It is over $U$
    because the algebra map respects the structural map from $Gamma(U, shf.o_Y)$.

  + *Glue the local morphisms.* Over a principal open these maps coincide by localization; refining
    overlaps as in RV-1 gives equality there. XL glues them to a $Y$-map.

  + *Check inverse assignments and naturality.* The same adjunction proves that both composites of these constructions
    are identities on each open, hence globally. Their formulas commute
    with composition in $T$ and with algebra maps, proving naturality.

  + *Identify the structural algebra.* Finally, on $U$ the structural algebra comparison is the identity of
    $B_U$ and on $D(a)$ it is the identity of $(B_U)_a$. SL-1 makes it
    an isomorphism of sheaves of algebras.
]

#metadata(none) <sup-rv-3>
#corollary(number: "RV-3", title: "Affine morphisms and algebras")[
  + The assignments $shf.a mapsto ops.spec_Y shf.a$ and
    $(f:X->Y) mapsto f_*shf.o_X$ give a contravariant equivalence between
    quasi-coherent $shf.o_Y$-algebras and affine schemes over $Y$.
  + The comparison $X->ops.spec_Y f_*shf.o_X$ is the canonical
    isomorphism for affine $f$.

  Affine locality, quasi-compactness, and separatedness are in
  #book-link(<sup-lp>)[the locality calculus]; this is the relative identification
  used in II.5.17(b)–(d).
]

#proof[

  + *Identify the quasi-coherent algebra.* For affine $f$, the algebra $f_*shf.o_X$ is quasi-coherent by affine
    pushforward in II.5.2: over $U=ops.spec A$, with inverse image
    $ops.spec B$, its sections on $D(a)$ are $B_a$.

  + *Identify the scheme comparison.* RV-2 applied to its
    identity algebra map gives the comparison from $X$. On this chart, it
    is the canonical affine identification $ops.spec B->ops.spec B$,
    hence an isomorphism; XL's cover criterion gives a global isomorphism.

  + *Obtain the contravariant equivalence.* In the opposite direction, the structural comparison is RV-2's algebra
    isomorphism. RV-2 is natural and bijective on morphisms, so these
    comparisons give the asserted contravariant equivalence, including
    its action on arrows.
]

#metadata(none) <sup-rv-4>
#proposition(number: "RV-4", title: "Modules over an affine morphism")[
  + For affine $f:X->Y$, pushforward gives an equivalence between
    quasi-coherent modules on $X$ and modules over $f_*shf.o_X$ whose
    underlying $shf.o_Y$-modules are quasi-coherent.

  + On an affine open $U$, the inverse takes the associated sheaf of the
    $Gamma(U, f_*shf.o_X)$-module and glues these sheaves.

  + The target category retains the algebra action; it is not just the category
    of quasi-coherent modules on $Y$.
]

#proof[

  + *Verify the affine equivalence with its algebra action.* Over $U=ops.spec A$ write $f^(-1)(U)=ops.spec B$. A quasi-coherent
    sheaf there is $tildeOf(M)$ for a $B$-module $M$; pushforward is its
    associated $A$-module with the retained $B$-action. Conversely, a
    quasi-coherent $A$-module sheaf with an action of $tildeOf(B)$ gives
    on global sections a $B$-module. The action on all principal opens is
    its localization, by the tensor comparison and affine full faithfulness
    in II.5.2. Thus these operations are inverse on objects and on linear
    morphisms over $U$.

  + *Glue the inverse and comparison maps.* On $D(a)$, the inverse replaces $M$ by $M_a$ as a $B_a$-module.
    Localization is transitive and respects the action, so the local inverses
    agree on principal refinements of intersections of target charts. SL
    glues the module sheaves and their morphisms. Their two comparison maps
    are the affine identity comparisons, hence are global isomorphisms by
    SL-1. Forgetting the algebra action would lose the $B$-module structure
    needed for this inverse.
]

#metadata(none) <sup-rv-5>
#corollary(number: "RV-5", title: "Base change")[
  For $g:Y'->Y$, the canonical map identifies
  $fiber(ops.spec_Y shf.a, Y', base: Y)$ with
  $ops.spec_(Y') g^*shf.a$ over $Y'$.
  On affine charts, this is the tensor-product comparison of
  #book-link(<sup-mg-1>)[MG-1], with its specified algebra maps.
]

#proof[

  + *Construct the canonical comparison.* Pull back the structural algebra map and use RV-2 to obtain the
    canonical comparison to the relative spectrum of $g^*shf.a$.

  + *Compute on affine charts.* Cover $Y'$ by affines $U'=ops.spec A'$ whose images lie in affines
    $U=ops.spec A$ of $Y$, and write $B=Gamma(U, shf.a)$. On $U'$,
    the pulled-back algebra is associated to $tensor(B, A', over: A)$
    by II.5.2's pullback formula. MG-1 identifies the fiber product with
    its spectrum; the comparison sends $b$ and $a'$ to their specified
    tensor factors and is that very identification.

  + *Check the global comparison.* These charts cover
    $Y'$, so the comparison is an isomorphism. Its construction from the
    structural map ensures compatibility on overlaps and naturality.
]

#metadata(none) <sup-rv-6>
#definition(number: "RV-6", title: "Vector bundles")[
  + A finite locally free module $shf.e$ determines a vector bundle by the
    relative spectrum of its symmetric algebra.

  + On a rank-$r$ trivializing
    open, its total space is relative affine $r$-space, and changes of basis give
    linear transition maps satisfying the same overlap cocycle.

  + Conversely,
    linear bundle trivializations and their transition maps give a finite
    locally free module, with the dual convention in RV-8.
]

#proof[

  + *Identify each trivial bundle.* On a trivializing open $U$, the symmetric algebra of
    $shf.o_U^r$ is $shf.o_U[t_1,dots,t_r]$ by AL-6's universal property,
    sending basis sections to polynomial variables. RV-1 therefore gives
    relative affine $r$-space there.

  + *Transport the transition cocycle.* A basis change acts on degree one,
    extends uniquely to a symmetric-algebra isomorphism, and hence induces
    a linear change of fiber coordinates. Uniqueness on the generators
    carries the basis cocycle to the gluing cocycle.

  + *Recover the locally free module.* Conversely, dualize the linear transition maps of local trivial bundles
    to obtain transitions on their modules of linear functions. These are
    invertible matrices satisfying a cocycle, so SL glues the finite free
    module sheaves to $shf.e$. Their symmetric algebras and spectra recover
    the original trivial bundles and transitions by the same generator
    calculation. Thus the two constructions are inverse with the stated
    convention.
]

#metadata(none) <sup-rv-7>
#remark(number: "RV-7", title: "Transition matrices and fiber coordinates")[
  More explicitly, if ordered bases, written as rows, satisfy $e_j=e_i G_(i j)$, then coordinate
  columns of a linear functional satisfy $z_j=G_(i j)^t z_i$; these are the
  fiber coordinates for the convention below.
]

#proof[

  + *Compute the coordinates.* A linear functional $lambda$ has coordinate $z_(i,a)=lambda(e_(i,a))$.
    The equation $e_(j,b)=sum_a e_(i,a)(G_(i j))_(a b)$ gives
    $z_(j,b)=sum_a (G_(i j))_(a b) z_(i,a)$, exactly the transpose formula.

  + *Check the cocycle.* If $G_(i k)=G_(i j)G_(j k)$, transposition gives
    $G_(i k)^t=G_(j k)^t G_(i j)^t$, the composition law for these
    coordinate changes. Check this matrix-transpose identity (Check!).
    It verifies agreement on triple overlaps.
]

#metadata(none) <sup-rv-8>
#corollary(number: "RV-8", title: "Sections and the dual convention")[
  We use $V(shf.e)=ops.spec_X ops.sym (shf.e)$.

  + Its sections over an open $U$ correspond to linear maps
    $shf.e|_U->shf.o_U$, so its sheaf of sections is $shf.e^or$.

  + To obtain a bundle whose sheaf of sections is $shf.e$, use $V(shf.e^or)$.
    This convention is part of the comparison with II.5.18.
]

#proof[

  + *Identify the section sheaf.* Apply RV-2 to the inclusion $U->X$. Algebra maps from
    $ops.sym (shf.e|_U)$ to $shf.o_U$ correspond by the symmetric-algebra
    universal property to linear maps $shf.e|_U->shf.o_U$; the bijection
    restricts an algebra map to degree one. It commutes with restrictions
    in $U$, so the section sheaf is the dual sheaf.

  + *Apply double-dual evaluation.* Finite local freeness
    makes evaluation $shf.e->shf.e^(or or)$ an isomorphism by SC-11:
    on each trivialization it is the usual finite free double-dual map.
    Applying the first assertion to $shf.e^or$ gives the final convention.
]

#metadata(none) <sup-rv-examples>
#metadata(none) <sup-rv-9>
#example(number: "RV-9", title: "Examples")[
  + The algebra $shf.o_Y[t_1,dots,t_n]$ gives relative affine $n$-space.

  + For a quasi-coherent ideal, $shf.o_Y\/shf.i$ gives the closed subscheme
    of #book-link(<sup-cs-1>)[CS-1].

  + Over $ops.spec k[t]$, the module
    $tildeOf(k[t]\/(t))$ has a symmetric-algebra spectrum, but its fibers
    have varying dimensions, so it is not a vector bundle of fixed rank.
]

#proof[

  + *Relative affine space.* The polynomial-algebra case follows from its coordinates on every
    affine base chart.

  + *The closed subscheme.* For the quotient algebra, these charts are
    $ops.spec(A/I)$, with their quotient maps, so they glue to the closed
    subscheme defined by the ideal.

  + *A symmetric-algebra spectrum of varying fiber dimension.* Finally, put $A=k[t]$ and
    $M=A\/(t)$. Its symmetric algebra is $A[z]\/(t z)$: the degree-one
    generator is killed by $t$, which is the sole module relation. At a
    point where $t$ is nonzero the fiber ring is the residue field, while
    at $t=0$ it is $k[z]$. The fiber dimensions are respectively zero and
    one. Since $ops.spec k[t]$ is connected, a vector bundle would have
    constant rank; this example does not.
]
