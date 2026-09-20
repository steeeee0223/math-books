#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== CAT — Categorical language <sup-cat>

The constructions below use categories and functors in their usual sense. Only small diagrams are considered. The existence of a limit or colimit must be checked in the category in use.

#metadata(none) <sup-cat-1>
#definition(number: "CAT-1", title: "Natural transformations")[
  + For functors $F,G:C->D$, a natural transformation $alpha:F->G$ is a family
    $alpha_X:F(X)->G(X)$ satisfying
    $G(u) compose alpha_X=alpha_Y compose F(u)$ for every $u:X->Y$.

    The naturality condition is the commutativity of the square
    #align(center)[
      #diagram(
        cell-size: 20mm,
        $
          F(X) edge("r", alpha_X, ->) edge("d", F(u), ->) & G(X) edge("d", G(u), ->) \
                              F(Y) edge("r", alpha_Y, ->) & G(Y)
        $,
      )
    ]
  + A natural transformation $alpha$ is a natural isomorphism if and only if
    every component $alpha_X$ is an isomorphism.
  + A diagram commutes when composites along paths with the same endpoints
    agree.
  + For presheaves, naturality is compatibility with restriction maps.
]

#metadata(none) <sup-cat-2>
#definition(number: "CAT-2", title: "Universal properties")[
  A universal object is specified together with its structure maps and a unique factorization property.

  For localization, the unique factorization has the form
  #align(center)[
    #diagram(
      cell-size: 20mm,
      $
        A edge("r", iota, ->) edge("dr", phi, ->) & S^(-1)A edge("d", overline(phi), ->, stroke: #(dash: "dashed")) \
                                                  & B
      $,
    )
  ]
  The dashed arrow denotes the map whose existence and uniqueness are asserted.
]

#metadata(none) <sup-cat-3>
#proposition(number: "CAT-3", title: "Uniqueness of universal objects")[
  + Two solutions of the same universal problem have a unique isomorphism preserving those maps. This does not assert that the underlying object has no other automorphisms.
  + For a multiplicative subset $S$ of a ring $A$, the map $A->S^(-1)A$ is initial among ring maps from $A$ sending every element of $S$ to a unit: any such $A->B$ factors uniquely through $S^(-1)A$.
]

#proof[

  + *Compare universal solutions.* Regard the universal problem as a category of objects with their prescribed structure maps. If $P,Q$ are initial solutions, let $u:P->Q$ and $v:Q->P$ be their unique structure-preserving maps. Both $v compose u$ and $ops.id_P$ are endomorphisms in this category, so they are equal; likewise $u compose v=ops.id_Q$. Any structure-preserving isomorphism must equal $u$. For terminal solutions, reverse the arrows.

  + *Verify the localization property.* For localization, let $phi:A->B$ send $S$ to units. Define $overline(phi)(a/s)=phi(a)phi(s)^(-1)$. If $a/s=a'/s'$, some $t in S$ satisfies $t(s' a-s a')=0$. Applying $phi$ and cancelling its unit factors proves that the displayed values agree. The fraction formulas for addition and multiplication make $overline(phi)$ a ring map. It extends $phi$, and every extension must send $a/s$ to that value. This proves existence and uniqueness, including the case where the localization is the zero ring.
]

#metadata(none) <sup-cat-4>
#definition(number: "CAT-4", title: "Objects, products, and coproducts")[

  + An initial object has exactly one morphism to each object.
  + A terminal object has exactly one morphism from each object.
  + A product $P$ of objects $X_i$ has projections $P->X_i$ and natural bijections $ ops.hom(T, P) simeq product_i ops.hom(T, X_i). $
  + A coproduct $Q$ has injections $X_i->Q$ and natural bijections $ ops.hom(Q, T) simeq product_i ops.hom(X_i, T). $
  + The empty product is terminal, and the empty coproduct is initial.
  + For a binary product, maps $a:T->X$ and $b:T->Y$ determine $u:T->P$ by $p_X compose u=a$ and $p_Y compose u=b$: #align(center)[
      #diagram(
        cell-size: 18mm,
        $   & T edge("dl", a, ->) edge("d", u, ->, stroke: #(dash: "dashed")) edge("dr", b, ->) \
        X & P edge("l", p_X, ->) edge("r", p_Y, ->)                                           & Y $,
      )
    ] Reversing the arrows gives the coproduct property.
]

#metadata(none) <sup-cat-5>
#example(number: "CAT-5", title: "Products and coproducts in familiar categories")[
  + In sets, these constructions are cartesian product and disjoint union.

  + For $cat.ab$, finite direct sums are both products and coproducts;
    an infinite direct sum consists of finite-support families, whereas a product allows all families.

  + For $cat.ring$, the product is the componentwise ring and the binary coproduct is $tensor(A, B, over: ZZ)$.

  + In $cat.sch$, the empty scheme is initial and $ops.spec ZZ$ is terminal; see #book-link(<sup-xl-2>)[XL-2].
]

#proof[

  + *Sets.* A map into a cartesian product is uniquely its tuple of component maps; a map out of a disjoint union is uniquely its restrictions to the summands.

  + *Abelian groups.* For abelian groups, a homomorphism from a direct sum sends a finite-support tuple $(a_i)$ to $sum_i u_i(a_i)$, and this formula gives the unique map with restrictions $u_i$. For finitely many indices, the direct sum and product have identical underlying groups.

  + *Rings.* A map into a product of rings is similarly a tuple of ring maps. Given ring maps $u:A->R$ and $v:B->R$ into a ring, the balanced map $(a,b) mapsto u(a)v(b)$ induces $tensor(A, B, over: ZZ)->R$; pure tensors generate it and their products show that this is the unique ring map extending both.

  + *Schemes.* The assertions for schemes follow from the global-sections bijection in #book-link(<sup-xl-2>)[XL-2] and its unique map $ZZ->Gamma(X, shf.o_X)$; there is a unique morphism from the empty scheme because both its point map and sheaf map are forced.
]

#metadata(none) <sup-cat-6>
#definition(number: "CAT-6", title: "Limits and colimits")[
  + For a diagram $D:I->C$, a cone with vertex $T$ consists of maps $T->D(i)$ compatible with every arrow of $I$. A limit is a cone through which every cone factors uniquely.

  + A cocone consists of maps $D(i)->T$; a colimit is a cocone with the dual unique factorization property.

  + A map of diagrams induces a map of their limits, or of their colimits, by composing the structure maps and applying these properties.

  + The fiber product of #book-link(<text-ii-3>)[II.3, D10] is a limit of two maps with common target; its definition and existence theorem remain there.

  + A cone to an arrow $a:i->j$ satisfies the triangular equation below; a map of limiting cones is specified by the square on the right.
    #align(center)[
      #diagram(
        cell-size: 18mm,
        $
          T edge("d", lambda_i, ->) edge("dr", lambda_j, ->)
          & & L_D edge("r", ->) edge("d", lambda_i, ->)
          & L_E edge("d", mu_i, ->) \
          D(i) edge("r", D(a), ->) & D(j)
          & D(i) edge("r", alpha_i, ->) & E(i)
        $,
      )
    ]
]

#proof[

  + *Construct the limit comparison.* For a natural transformation $alpha:D->E$ and a limiting cone $lambda_i:L_D->D(i)$, the maps $alpha_i compose lambda_i$ form a cone to $E$: for $a:i->j$, naturality gives $E(a) compose alpha_i compose lambda_i=alpha_j compose lambda_j$. The universal property of $L_E$ therefore gives a unique map $L_D->L_E$ with these composites.

  + *Check functoriality.* Identity transformations induce identities, and composite transformations induce composite maps, since their projections agree and the limit property detects equality.

  + *Dualize to colimits.* For colimits, compose $D(i)->E(i)$ with the colimit injections of $E$ and apply the dual argument.
]

#metadata(none) <sup-cat-7>
#definition(number: "CAT-7", title: "Directed and inverse systems")[
  + A directed poset is nonempty, and every finite subset has an upper bound.

  + A direct system has maps $M_i->M_j$ for $i<=j$, with identity and composition compatibility; an inverse system has maps $M_j->M_i$. Their direct and inverse limits mean the corresponding colimit and limit.

  + A category is filtered when it is nonempty, any two objects map to a common object, and any two parallel arrows become equal after a further arrow.
]

#metadata(none) <sup-cat-8>
#lemma(number: "CAT-8", title: "Equality in a filtered colimit")[
  Let $D:I->C$ be a filtered diagram of sets or modules, with colimit maps $iota_i:D(i)->ops.colim D$. For $x in D(i)$ and $y in D(j)$, the equality $iota_i(x)=iota_j(y)$ holds if and only if there are an object $k$ and arrows $a:i->k$, $b:j->k$ such that $D(a)(x)=D(b)(y)$.

  For a directed poset, this means that the two representatives become equal at some stage $k>=i,j$. The criterion does not apply to arbitrary colimits.
]

#proof[

  + *Define the comparison relation.* Take the disjoint union of the underlying sets $D(i)$. Put $(i,x) tilde.op (j,y)$ when some arrows $a:i->k$, $b:j->k$ have $D(a)(x)=D(b)(y)$.

  + *Check equivalence.* This relation is reflexive and symmetric. For transitivity, map the two witness objects to a common object and then equalize the two resulting arrows from the middle object. The two witnessed equalities now hold in one object and imply the required third equality. Thus $tilde.op$ is an equivalence relation.

  + *Identify the set colimit.* Every diagram arrow identifies an element with its image. Conversely, every witnessed equality follows from such identifications. The quotient consequently has the universal property of the colimit of sets.

  + *Add the module structure.* For modules, define addition by sending two representatives to a common object and adding there; define scalar multiplication in any representative. To compare two choices, send their objects to a common object and equalize the finitely many parallel arrows. This proves independence of choices and all module identities (Check!). Compatible linear maps descend uniquely to the quotient, so this is also the module colimit, with exactly the asserted equality relation. For a directed poset, all parallel arrows are already equal.
]

#metadata(none) <sup-cat-9>
#definition(number: "CAT-9", title: "Adjunctions")[
  An adjunction $L:C->D$, $R:D->C$ is a bijection $ ops.hom(L(X), Y) simeq ops.hom(X, R(Y)), $ natural in $X,Y$.
]

#metadata(none) <sup-cat-10>
#proposition(number: "CAT-10", title: "Unit, counit, and preservation of limits")[
  + The identity maps give the unit $eta_X:X->R(L(X))$ and counit
    $epsilon_Y:L(R(Y))->Y$.

  + They satisfy $epsilon_(L(X)) compose L(eta_X)=ops.id_(L(X))$ and $R(epsilon_Y) compose eta_(R(Y))=ops.id_(R(Y))$.

    The triangle identities express the commutativity of
    #align(center)[
      #diagram(
        cell-size: 22mm,
        $
          L(X) edge("r", L(eta_X), ->) edge("dr", ops.id, ->, label-side: #right)
          & L(R(L(X))) edge("d", epsilon_(L(X)), ->, label-side: #left) \
          & L(X)
        $,
      )
      #h(8mm)
      #diagram(
        cell-size: 22mm,
        $
          R(Y) edge("r", eta_(R(Y)), ->) edge("dr", ops.id, ->, label-side: #right)
          & R(L(R(Y))) edge("d", R(epsilon_Y), ->, label-side: #left) \
          & R(Y)
        $,
      )
    ]

  + The bijection sends $u$ to $R(u) compose eta_X$; its inverse sends $v$ to $epsilon_Y compose L(v)$.

  + Left adjoints preserve existing colimits and right adjoints preserve existing limits.

  Sheafification is the left adjoint specified in #book-link(<text-ii-1>)[II.1, Proposition 1.2]. Direct and inverse images are defined in II.1, D7; their adjunction, and the distinction between inverse image and module pullback, are treated in #book-link(<sup-sc-6>)[SC-6~SC-8].
]

#proof[

  + *Construct the unit and counit.* Write $Phi_(X,Y)$ for the adjunction bijection and set $eta_X=Phi_(X,L(X))(ops.id_(L(X)))$ and $epsilon_Y=Phi_(R(Y),Y)^(-1)(ops.id_(R(Y)))$. Naturality in $Y$ gives $Phi(u)=R(u) compose eta_X$; naturality in $X$ gives $Phi^(-1)(v)=epsilon_Y compose L(v)$. Applying these inverse bijections to the two identity maps proves the two triangle identities. Applying naturality to a map $X->X'$ or $Y->Y'$ also proves that $eta$ and $epsilon$ are natural transformations.

  + *Preserve colimits.* Let $K:I->C$ have colimit $Q$, with injections $iota_i$. A cocone $L(K(i))->Y$ corresponds under $Phi$ to maps $K(i)->R(Y)$.
    Naturality says precisely that these maps are a cocone. They factor uniquely through $Q->R(Y)$, hence uniquely through $L(Q)->Y$. This correspondence sends the factorization equations to the equations for $L(iota_i)$, so $L(Q)$ with these injections is the required colimit.

  + *Preserve limits.* Applying the same argument to cones, using $ops.hom(X, R(K(i))) simeq ops.hom(L(X), K(i))$, shows that $R$ preserves limits. Every comparison is natural because each map is characterized by its composites with the specified structure maps.
]
