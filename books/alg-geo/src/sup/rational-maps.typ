#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== RM — Rational maps of schemes <sup-rm>

This supplement translates Chapter I's rational maps into scheme language.
The basic inputs are the generic-point dictionary in
#book-link(<sup-xp-generic-points>)[XP-1–XP-7], scheme gluing in
#book-link(<sup-xl>)[XL], and the dominance and dense-open criteria
#book-link(<sup-lp-59>)[LP-59–LP-64]. The extension results additionally use
normal local rings and the valuative criterion of II.4.

=== Domains, composition and function fields

#metadata(none) <sup-rm-1>
#definition(number: "RM-1", title: "A rational map and its representatives")[
  A representative of a rational map $X$ to $Y$ is a morphism $f:U->Y$
  on a dense open subscheme $U$ of $X$. Two representatives are equivalent
  if their restrictions agree on a common dense open of $X$ contained
  in both domains. A *rational map* $X arrow.r.dashed Y$ is an equivalence
  class of representatives. Over a fixed base $S$, use $S$-morphisms
  and this same equivalence relation. The *domain of definition* is the
  union of all domains of representatives; its closed complement is the
  *indeterminacy locus*.

  The intersection of finitely many dense open subsets is dense and open;
  this topological fact, whose proof is left to the reader, proves
  transitivity of the equivalence relation. The definition does not assert
  that there is a representative on the whole domain of definition.
  Compare #link("https://stacks.math.columbia.edu/tag/01RR")[Stacks, Rational maps].
]

#metadata(none) <sup-rm-2>
#proposition(number: "RM-2", title: "The maximal representative")[
  If $X$ is reduced and $Y\/S$ is separated, every $S$-rational map has a
  unique representative on its domain of definition.
]
#proof[
  Take the union $D$ of the domains of its $S$-representatives. Given
  representatives on $U,V$, their common dense agreement open remains
  dense in $U inter V$. The latter is reduced. By
  #book-link(<sup-lp-63>)[LP-63], their restrictions agree as morphisms on
  all of $U inter V$. The gluing theorem of XL therefore gives a unique
  map $D->Y$. Its structural composite to $S$ equals the structural map
  on the cover by representative domains, hence globally. Any other
  representative on $D$ agrees on that cover by LP-63. This proves both
  existence and uniqueness. For ordinary rational maps take
  $S=ops.spec ZZ$.
]

#metadata(none) <sup-rm-3>
#proposition(number: "RM-3", title: "When composition is defined")[
  Suppose $X,Y$ are integral and $f:X arrow.r.dashed Y$ is dominant,
  meaning that a representative has dense image. For any rational map
  $g:Y arrow.r.dashed Z$, there is a well-defined composite
  $g f:X arrow.r.dashed Z$. Dominant rational maps between integral schemes
  compose associatively and have identity maps.

  More generally, chosen representatives $f:U->Y$ and $g:V->Z$ can be
  composed whenever $f^(-1)(V)$ is dense in $X$. Independence under a
  change of representative requires that the inverse image of the
  common agreement open is also dense; dominance guarantees this condition.
]
#proof[
  By LP-60 every restriction to a nonempty open of $U$ is dominant, so
  dominance is independent of the representative. The generic point of
  $X$ maps to that of $Y$ by XP-1–XP-7; the latter belongs to $V$. Thus
  $W=f^(-1)(V)$ is an open containing the generic point of $X$, and is
  dense. Define the composite on $W$ by ordinary composition.
  On replacing the representatives, intersect the two agreement domains
  in $X$ and pull back the agreement domain in $Y$. This is again an
  open containing the generic point; the two composites are equal
  there. The equivalence class is therefore independent of choices.
  Three dominant representatives have a common dense domain on which
  both parenthesizations are ordinary composition. Associativity and
  the identity laws follow there and hence for the rational maps.
]

#metadata(none) <sup-rm-4>
#theorem(number: "RM-4", title: "The function-field dictionary")[
  Let $X,Y$ be integral separated schemes of finite type over a field
  $k$. Pullback gives a bijection between dominant $k$-rational maps
  $X arrow.r.dashed Y$ and $k$-embeddings $k(Y)->k(X)$, with composition
  in the reverse order. Consequently inverse rational maps, isomorphic
  dense open subschemes, and an isomorphism of the two function fields
  over $k$ are equivalent descriptions of birationality.
]
#proof[
  A dominant representative sends the generic point to the generic point,
  so its local-ring map is the specified field embedding by XP-1–XP-7.
  Equivalent representatives induce the same map. Conversely let
  $sigma:k(Y)->k(X)$ be a $k$-embedding. Choose nonempty affine opens
  $ops.spec A subset X$, $ops.spec B subset Y$, and finite algebra
  generators $b_1,dots,b_r$ of $B$ over $k$. Express all $sigma(b_i)$
  in $ops.frac A$. The product $a != 0$ of their denominators makes
  them elements of $A_a$. All relations hold there, since $A_a$ injects
  into $k(X)$. The resulting injective map $B->A_a$ induces
  $D(a)->ops.spec B->Y$, and XP-1–XP-7 proves dominance. Its generic map is
  $sigma$. Clearing finitely many denominators is the terminal algebraic
  assertion; its proof is left to the reader.

  To check uniqueness, intersect the two source domains and then the
  inverse images of a nonempty affine target chart. These are nonempty
  opens because the maps are dominant. On each affine source subchart,
  the two maps on $B$ agree after injection into $k(X)$, hence already
  in its coordinate ring. XL gives equality on that dense open. This
  proves the bijection and shows directly that it reverses composition.

  Inverse field embeddings give inverse rational maps by RM-3 and the
  bijection. Choose representatives $f:U->Y$, $g:V->X$, and shrink the
  domains on which $g f$ and $f g$ are defined until the identities hold.
  Put $U_0=U inter f^(-1)(V)$ and then shrink it so $g f=ops.id$ there.
  Shrink $V$ so $f g=ops.id$ on $V inter g^(-1)(U)$, and replace $U_0$
  by $U_0 inter f^(-1)(V)$. The open $V_0=V inter g^(-1)(U_0)$ is
  nonempty by dominance. The identities identify $V_0$ with
  $U_0 inter f^(-1)(V_0)$, giving isomorphic dense opens. Conversely,
  such an isomorphism gives inverse generic maps and hence inverse
  field embeddings. The finite-type hypothesis was used to extend a
  generic map using finitely many algebra generators.
]

#metadata(none) <sup-rm-5>
#proposition(number: "RM-5", title: "Generically finite morphisms")[
  Let $f:X->Y$ be a dominant morphism of integral separated finite-type
  $k$-schemes. The extension $k(X)\/k(Y)$ is finite if and only if some
  nonempty open $V subset Y$ has $f^(-1)(V)->V$ finite.
  (Ex. II.3.7, integral separated finite-type $k$-schemes)
]
#proof[
  Start with an affine $ops.spec A subset Y$ and a nonempty affine
  $U=ops.spec B subset f^(-1)(ops.spec A)$. The map $A->B$ is injective
  and of finite type. If the field extension is finite, its algebra
  generators satisfy monic equations over $ops.frac A$. Choose
  $a in A minus {0}$ clearing the finitely many coefficients. Then
  $B_a$ is finite over $A_a$. The algebraic statements that clearing
  these coefficients makes each generator integral and that finitely
  many integral generators give a finite module are left to the reader.

  It remains essential to control the *entire* inverse image. Write
  $V=D(a)$ and $X_V=f^(-1)(V)$. The open immersion $U_a->X_V$ is proper:
  its graph in $fiber(U_a, X_V, base: V)$ is closed because $X_V\/V$ is
  separated, and the projection to $X_V$ is a base change of the finite,
  hence proper, map $U_a->V$; use MG-5 and MG-11. Its image is thus both
  open and closed in the integral scheme $X_V$, and is nonempty. It is
  all of $X_V$, proving finiteness of the whole inverse image. Conversely,
  a finite dominant map on this open induces a finite extension after
  tensoring its finite coordinate module with $k(Y)$; the resulting
  finite-dimensional domain over $k(Y)$ is its fraction field $k(X)$.
  This last assertion is algebraic and is left to the reader.
]

=== Graphs and extension

#metadata(none) <sup-rm-6>
#proposition(number: "RM-6", title: "The closure of a graph")[
  Let $S$ be Noetherian, let $X$ be an integral Noetherian $S$-scheme,
  and let $Y\/S$ be separated and of finite type. For an $S$-rational map
  $f:X arrow.r.dashed Y$, take the reduced closure $Gamma_f$ of the graph
  of a representative in $fiber(X, Y, base: S)$. It is independent of the
  representative, is integral, and its projection $p:Gamma_f->X$ is
  an isomorphism over a dense open. If $Y\/S$ is proper, respectively
  projective, then $p$ is proper, respectively projective.
]
#proof[
  The graph of $U->Y$ is closed in $fiber(U, Y, base: S)$ by MG-5 and is
  isomorphic to the integral scheme $U$. Its reduced closure exists by
  CS and is integral by XP. Equivalent representatives coincide over a
  common dense open; that smaller graph is dense in either graph, so
  their closures and reduced structures agree. Restricting the closure
  to the open $fiber(U, Y, base: S)$ recovers the closed graph, with its
  reduced structure. Projection is therefore an isomorphism over $U$.
  Finally $p$ is the composite of the closed immersion into the product
  and its projection to $X$. Properness follows from base change and
  composition in LP; projectivity follows from LP-55. No assertion of
  finiteness follows merely from this properness.
]

#metadata(none) <sup-rm-7>
#theorem(number: "RM-7", title: "Extension at codimension one")[
  Let $S$ be locally Noetherian, let $X$ be integral and normal of finite
  type over $S$, and let $Y$ be proper over $S$. An $S$-rational map
  $X arrow.r.dashed Y$ extends to a neighborhood of every codimension-one
  point of $X$. Its maximal domain therefore contains all these points.
]
#proof[
  Fix a codimension-one point $x$. The normal Noetherian local domain
  $R=shf.o_(X,x)$ is a discrete valuation ring with fraction field
  $K=k(X)$, by the local algebra of II.6. This purely algebraic theorem
  is left to the reader. The generic-point map $ops.spec K->Y$ and
  the structural map $ops.spec R->S$ give a valuative diagram. The
  properness criterion of II.4 supplies its unique lift
  $h:ops.spec R->Y$.

  Choose an affine neighborhood $ops.spec A$ of $x$ mapping into an
  affine open $ops.spec R_0$ of $S$. An affine open $ops.spec B$ of
  $Y$ over that base containing the image of the closed point of
  $ops.spec R$ contains the image of all of $ops.spec R$, since every
  point of a local spectrum generalizes its closed point. The ring
  $B$ is finitely presented over $R_0$: properness gives finite type,
  and $R_0$ is Noetherian. For $x$ corresponding to $idl.p subset A$,
  the map $B->A_idl.p$ consequently factors through $A_s$ for some
  $s in.not idl.p$. Indeed, lift finitely many generators and then invert
  finitely many additional elements to make their finitely many relations
  vanish. This finite-presentation localization lemma is purely algebraic;
  its proof is left to the reader.

  The resulting morphism $D(s)->Y$ has the original generic map.
  On the intersection with the old domain, equality can be checked on
  affine charts by injection of regular functions into $K$, then on
  the whole intersection by MG-6. XL glues it to the representative.
  This constructs the requested extension, and RM-2 gives its uniqueness.
]

#metadata(none) <sup-rm-8>
#corollary(number: "RM-8", title: "Curves and affine targets")[
  In the setting of RM-7, if $ops.dim X=1$, every rational map in question
  extends everywhere. In particular, a birational map between normal
  proper integral $k$-curves is an isomorphism.

  If instead $X$ is integral normal Noetherian over $k$, $Z$ is a closed
  subset of codimension at least two and $Y=ops.spec B$ is affine over
  $k$, every $k$-morphism $X minus Z->Y$ extends uniquely to $X$.
]
#proof[
  A one-dimensional integral scheme has only its generic point and
  codimension-one points; the generic point already belongs to the
  domain. Apply RM-7 and glue by RM-2. For a birational map of normal
  proper curves, extend both rational inverses. Their composites equal
  the identity on a dense open and hence everywhere by MG-6.

  For the affine target, the given morphism is a $k$-algebra map
  $B->Gamma(X minus Z, shf.o_X)$. LP-64 identifies the latter ring
  canonically with $Gamma(X, shf.o_X)$. The affine-target adjunction in
  XL then constructs the required map to $ops.spec B$. Restriction
  recovers the given ring map, and injectivity of restriction proves
  uniqueness. This proof requires an affine target; a proper target
  alone does not give extension across codimension two.
]

=== Examples that distinguish the hypotheses

#metadata(none) <sup-rm-9>
#example(number: "RM-9", title: "A pencil with a base point")[
  Over an algebraically closed field $k$, consider
  $f:sch.p^2_k arrow.r.dashed sch.p^1_k$ given by
  $[x:y:z] mapsto [x:y]$. Its maximal domain is
  $sch.p^2 minus {p}$, $p=[0:0:1]$. Its graph closure is
  $ H=V(x v-y u) subset sch.p^2 times sch.p^1, $
  with $[u:v]$ the coordinates of the second factor.
]
#proof[
  The generating sections $x,y$ of $shf.o (1)$ define the map on
  $D_+(x) union D_+(y)$ by II.7.1. On the line $y=0$, its restriction
  away from $p$ is the constant $[1:0]$; on $x=0$ it is $[0:1]$.
  Any extension near $p$ must restrict to these constants on the two
  lines by MG-6, giving two different images at $p$. Thus no extension
  exists there, and RM-2 gives the stated maximal domain.

  On $u != 0$, put $a=v/u$. The equation is $y=a x$, giving a
  $sch.p^1$ with homogeneous coordinates $[x:z]$ over $ops.spec k[a]$.
  On $v != 0$, similarly put $b=u/v$ and use $x=b y$ with coordinates
  $[y:z]$. On the overlap $b=a^(-1)$ and $y=a x$, so the identifications
  are actual inverses and satisfy the gluing condition. These charts
  show that $H$ is reduced and integral. Over $sch.p^2 minus {p}$
  projection identifies $H$ with the graph, and that open is dense in
  each chart. Therefore $H$ is exactly the reduced graph closure of
  RM-6. Its fiber over $p$ is $sch.p^1$; BU identifies this projection
  with the blowup of the ideal $(x,y)$ near $p$.
]

#metadata(none) <sup-rm-10>
#example(number: "RM-10", title: "Birational is not everywhere invertible")[
  In characteristic zero, $t mapsto (t^2,t^3)$ gives a finite
  birational morphism $sch.a^1_k->V(y^2-x^3)$. Its rational inverse is
  $t=y/x$; it is not regular at the cusp, since
  $t in.not k[t^2,t^3]_(t^2,t^3)$. The finite-module assertion and this
  nonmembership are algebraic exercises, with proofs left to the reader.
  The latter can be checked using the least exponent of a nonzero
  polynomial: a denominator with nonzero constant term cannot make
  a term of degree one belong to $k[t^2,t^3]$.

  The proper target $sch.p^1$ in RM-9 still allows indeterminacy at the
  codimension-two point $p$. A constant map with image $p$ cannot be
  composed with that pencil by representatives, since the inverse image
  of its maximal domain is empty. In contrast, the Cremona map
  $[x:y:z] mapsto [y z:x z:x y]$ is dominant. On $x y z != 0$ its square is
  $[x:y:z] mapsto [x^2y z:x y^2z:x y z^2]=[x:y:z]$, so it is a rational
  involution. Its three coordinate base points and their blowups are
  treated in BU.

  Finally, on $ops.spec k[u,v]\/(u^2,u v)$ the maps to the affine line
  defined by $0$ and $u$ represent the same rational map but are distinct
  everywhere-defined morphisms. The dense domain $D(v)$ has forgotten
  the embedded point, as computed in LP-63. Thus the reduced-source
  hypothesis in RM-2 cannot simply be discarded.
]

#exercise(title: "Working with representatives")[
  For the pencil and the Cremona involution, write the inverse images
  of the standard affine target charts, the coordinate ring maps, and
  the agreement maps on their intersections. For the cusp, locate the
  largest open on which normalization is an isomorphism. Explain why
  equality of function fields does not recover the missing local ring.
]
