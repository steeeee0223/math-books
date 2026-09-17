#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

=== VS — Varieties and schemes <sup-vs>

Fix an algebraically closed field $k$ and use the Chapter I convention
for varieties. The construction and full faithfulness of $t$ remain in
#book-link(<text-ii-2>)[II.2, Proposition 2.6]. The scope of schemes arising
from those varieties, and the definition of abstract varieties, remain in
#book-link(<text-ii-4>)[II.4, Proposition 4.10 and D4].

#metadata(none) <sup-vs-1>
#proposition(number: "VS-1", title: "Classical points and residue fields")[
  - The points of a variety $V$ identify with the closed points of $t(V)$,
    which are exactly its points with residue field $k$.

  - The other scheme points include generic points of positive-dimensional
    irreducible closed subsets; see #book-link(<sup-xp-1>)[XP-1].
    The general description of field-valued points is #book-link(<sup-mg-7>)[MG-7].

  - For example, on $sch.a^1_k$, the classical point $a$ corresponds to
    $(t-a)$ in $ops.spec k[t]$, while $(0)$ is the generic point and is not
    $k$-rational.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify classical points on affine charts.* Choose an affine open subvariety with coordinate ring $A$, a finite type
    $k$-algebra. In its spectrum, the closed points are the maximal ideals.
    The Nullstellensatz identifies these with the classical points, and
    identifies each residue field with $k$ through its structural map.

  + *Prove the residue-field converse.* Conversely, if a prime $idl.p$ has residue field $k$ as a $k$-algebra,
    then $A\/idl.p$ embeds into $k$ and contains the image of $k$, so it
    equals $k$ and $idl.p$ is maximal.

  + *Pass from affine charts to the scheme.* These identifications commute with
    localization. The closed-point comparison for finite type schemes in
    #book-link(<sup-xp-1f>)[XP-1f] ensures that closedness on these affine charts
    is closedness in the whole scheme. They therefore glue to the claimed
    identification. The description of generic points follows from XP-1.

  + *Compute the affine-line example.* For $k[t]$, the maximal ideals are $(t-a)$; the residue field at $(0)$
    is $k(t)$, in which $t$ is transcendental over $k$, so it is not $k$.
]

#metadata(none) <sup-vs-2>
#proposition(number: "VS-2", title: "Affine and projective identifications")[
  - For an affine variety $V$, the canonical identification is
    $t(V) simeq ops.spec A(V)$.

  - For a projective variety, it is
    $t(V) simeq ops.proj S(V)$, with its homogeneous coordinate ring.

  - Use the affine chart and structure-sheaf formulas of
    #book-link(<text-ii-2>)[II.2, Propositions 2.2 and 2.5]: on standard charts
    regular functions identify with degree-zero localizations, compatibly
    with restriction. This is the comparison in II.2.14(d).

  - For the projective line, the charts have coordinates $t$ and $u$, with
    $u=1/t$ on the common punctured affine line.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the affine points and topology.* In the affine construction of II.2.6, the points added to $V$ are
    the generic points of its nonempty irreducible closed subsets $W$.
    Send such a point to the prime ideal of functions vanishing on $W$.
    The Nullstellensatz gives a bijection with $ops.spec A(V)$; the
    condition $W inter D(f)!=emptyset$ corresponds exactly to $f$ not
    belonging to this prime. Thus the bijection identifies the basic opens.

  + *Identify the affine structure sheaf.* On these opens, the regular functions are $A(V)_f$, and restriction
    to $D(f g)$ is the canonical localization map. The affine comparison
    of II.2.2 therefore also identifies the structure sheaves. In particular,
    a classical point corresponds to its maximal ideal.

  + *Compare the projective charts.* In the projective case, choose homogeneous coordinates $x_i$ and cover
    $V$ by $V inter D_+(x_i)$. Its affine coordinate ring is
    $(S(V)_(x_i))_0$, by dehomogenization $x_j mapsto x_j/x_i$.
    The preceding affine comparison identifies its associated scheme with
    the corresponding standard chart of $ops.proj S(V)$.

  + *Glue the projective identifications.* On the intersection of the $i$th and $j$th charts, both comparisons send
    a homogeneous fraction to that same regular function. Equivalently, they
    agree after localization at $x_j/x_i$ and at $x_i/x_j$, respectively.
    Scheme gluing in #book-link(<sup-xl>)[XL] therefore gives the canonical
    isomorphism.

  + *Compute the projective-line transition.* For two coordinates, these formulas read $t=x_1/x_0$ and
    $u=x_0/x_1$, hence $u=t^(-1)$ on the overlap.
]

#metadata(none) <sup-vs-3>
#remark(number: "VS-3", title: "Maps in both languages")[
  - For regular maps, the scheme map under the fully faithful functor of
    II.2.6 has the same pullback on regular functions on the affine charts.

  - Conversely, a $k$-scheme morphism between associated schemes preserves
    their $k$-rational points by #book-link(<sup-mg-7>)[MG-7]. Under VS-1, these
    are the classical points; its structure-sheaf map gives the corresponding
    regular map.

  - The natural Hom bijection is the one already proved in
    II.2.6, providing the entry for II.2.15(a)–(c).

  - The vanishing-ideal and quotient application is in #book-link(<sup-cs-4>)[CS-4].

  - The variety-product comparison of II.3.23 and computations over fields
    which are not algebraically closed are separate topics.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the scheme morphism from a regular map.* For a regular map, choose affine opens in its target and affine opens in
    their inverse images. The pullback of regular functions is a $k$-algebra
    homomorphism on each such pair of charts. VS-2 and the affine
    ring–scheme correspondence turn these into scheme morphisms.
    Their restrictions agree on overlaps because the original pullback is
    a morphism of sheaves; XL glues them uniquely.

  + *Recover the classical regular map.* Conversely, a $k$-scheme morphism carries a $k$-valued point to a
    $k$-valued point by composition with $ops.spec k$. VS-1 therefore
    restricts it to a map of classical points. On the same affine charts,
    its ring homomorphism sends each coordinate function to a regular
    function, so this map of points is regular.

  + *Check inverse constructions and naturality.* The two constructions are
    inverse on affine charts by the affine correspondence and the
    Nullstellensatz. Their compatibility with restrictions proves that they
    are inverse globally, and compatibility with composition proves naturality.
]
