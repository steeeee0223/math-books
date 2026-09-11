#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *

#show: show-theorion
#set list(indent: 1em)
#set enum(numbering: "(a)", indent: 1em)

== Sheaves

// Hartshorne II.1, Definition D1
#definition(number: none, title: "Presheaf")[
  Let $X$ be a topological space. A *presheaf* $shf.f$ of abelian groups on
  $X$ consists of the data

  - for every open subset $U subset.eq X$, an abelian group $shf.f (U)$, and
  - for every inclusion $V subset.eq U$ of open subsets, a homomorphism of abelian group $rho_(U V): shf.f (U) -> shf.f (V)$,

  subject to the conditions

  #set enum(numbering: "(PS1)", indent: 1em)
  + $shf.f (emptyset)=0$,
  + $rho_(U U)=ops.id_U$,
  + $rho_(U W)=rho_(V W) compose rho_(U V)$ whenever $W subset.eq V subset.eq U$.

  Presheaves of rings, sets, or objects of a fixed category are defined in the same way.
]

// Hartshorne II.1, Definition D2
#definition(number: none, title: "Sheaf")[
  A presheaf $shf.f$ on $X$ is a *sheaf* if, for every open cover
  $U=union_i V_i$:

  #set enum(numbering: "(S1)", indent: 1em)

  + a section $s in shf.f (U)$ whose restrictions to all $V_i$ vanish is zero;
  + compatible sections $s_i in shf.f (V_i)$, meaning
    $s_i|_(V_i inter V_j)=s_j|_(V_i inter V_j)$, glue to a section
    $s in shf.f (U)$ with $s|_(V_i)=s_i$ for every $i$.

  The first condition makes the glued section unique.
]

// Hartshorne II.1, Definition D3
#definition(number: none, title: "Stalk")[
  If $shf.f$ is a presheaf on $X$ and $P in X$, its *stalk* at $P$ is
  $shf.f_P=ops.colim_(P in U) shf.f (U)$. Its elements are germs: $(U,s)$ and $(V,t)$
  represent the same germ when their restrictions agree on some open
  neighborhood of $P$ contained in $U inter V$.
]

// Hartshorne II.1, Definition D4
#definition(number: none, title: "Morphism of Presheaves or Sheaves")[
  A morphism $phi:shf.f -> shf.g$ consists of homomorphisms
  $phi(U):shf.f (U)->shf.g (U)$ commuting with every restriction map. The same
  definition applies to sheaves. An isomorphism is a morphism with a
  two-sided inverse. Every morphism induces maps $phi_P:shf.f_P->shf.g_P$ on
  stalks.
]

// Hartshorne II.1, Proposition 1.1
#proposition(number: "1.1")[
  A morphism $phi:shf.f -> shf.g$ of sheaves on $X$ is an isomorphism if and only
  if $phi_P:shf.f_P -> shf.g_P$ is an isomorphism for every $P in X$.
]

// Hartshorne II.1, Definition D5
#definition(number: none, title: "Presheaf Kernel, Cokernel, and Image")[
  For a morphism $phi:shf.f -> shf.g$ of presheaves, we can define

  - the presheaf kernel $U mapsto ops.ker phi(U)$,
  - the presheaf cokernel $U mapsto ops.coker phi(U)$,
  - the presheaf image $U mapsto ops.im phi(U)$.
]

// Hartshorne II.1, Proposition-Definition 1.2
#proposition(number: "1.2", title: "Sheafification")[
  Given a presheaf $shf.f$, there are a sheaf $shf.f^+$ and a morphism
  $theta:shf.f -> shf.f^+$ such that every morphism $phi:shf.f -> shf.g$ to a sheaf
  factors uniquely as $shf.f ->^(theta) shf.f^+ ->^(psi) shf.g$. The pair
  $(shf.f^+,theta)$ is unique up to unique isomorphism and is called the
  *sheaf associated to* $shf.f$.
]

// Hartshorne II.1, Definition D6
#definition(number: none, title: "Subsheaves, Images, Quotients, and Exactness")[

  - A *subsheaf* $shf.f'$ of $shf.f$ has subgroups $shf.f'(U) subset.eq shf.f (U)$ and the induced restrictions.
  - For a sheaf morphism $phi:shf.f->shf.g$, its *kernel* is the presheaf kernel, while its *image* and *cokernel* are the sheaves associated to the corresponding presheaves.
  - The morphism is *injective* if $ops.ker phi=0$ and *surjective* if $ops.im phi=shf.g$.
  - A sequence is *exact* when the image at each term equals the next kernel.
  - If $shf.f'$ is a subsheaf of $shf.f$, the *quotient* $shf.f\/shf.f'$ is the sheaf associated to $U mapsto shf.f (U)\/shf.f'(U)$. In particular, $(shf.f\/shf.f')_P simeq shf.f_P\/shf.f'_P$.
]

// Hartshorne II.1, Definition D7
#definition(number: none, title: "Direct and Inverse Images")[

  Let $f:X->Y$ be continuous.
  - For a sheaf $shf.f$ on $X$, its direct image $f_*shf.f$ is sheaf $V mapsto shf.f (f^(-1) (V))$.
  - For a sheaf $shf.g$ on $Y$, its inverse image $f^(-1)shf.g$ is the sheaf associated to $U mapsto ops.colim_(V supset.eq f(U)) shf.g (V)$.
]

// Hartshorne II.1, Definition D8
#definition(number: none, title: "Restriction of a Sheaf")[

  If $i:Z arrow.r.hook X$ is the inclusion of a subspace, the
  *restriction* of a sheaf $shf.f$ to $Z$ is $i^(-1)shf.f$, also denoted $shf.f|_Z$.
  Its stalk at $P in Z$ is just $shf.f_P$.
]
