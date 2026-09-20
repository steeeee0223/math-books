#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== SL — Sheaf locality and gluing <sup-sl>

Use the definitions and stalkwise isomorphism criterion of
#book-link(<text-ii-1>)[II.1, D1–D4 and Proposition 1.1]. Throughout this section, sheaves take values in sets, abelian groups, rings, or modules over a fixed sheaf of rings $shf.o$. No assertion about arbitrary category-valued sheaves is intended.

#metadata(none) <sup-sl-1>
#lemma(number: "SL-1", title: "Local equality")[
  Let $shf.f,shf.g$ be sheaves on $X$.

  #set enum(spacing: 0.8em)

  + For $s in shf.f (U)$, $t in shf.f (V)$, and $x in U inter V$,
    $s_x=t_x$ if and only if their restrictions agree on some open
    neighborhood of $x$ contained in $U inter V$. Finitely many equalities
    of germs at $x$ can be realized on one neighborhood; infinitely many
    need not admit such a common neighborhood.

  + For an open subset $U subset.eq X$, an open cover $U=union_i U_i$,
    and sections $s,t in shf.f (U)$, the following conditions are equivalent:

    + $s=t$.
    + $s|_(U_i)=t|_(U_i)$ for every $i$.
    + $s_x=t_x$ for every $x in U$.

  + For morphisms $u,v:shf.f->shf.g$ and an open cover $X=union_i U_i$,
    the following conditions are equivalent:

    + $u=v$.
    + $u|_(U_i)=v|_(U_i)$ for every $i$.
    + $u_x=v_x$ for every $x in X$.

  + Let $u:shf.f->shf.g$ be a morphism, and let $X=union_i U_i$ be an
    open cover. Then $u$ is an isomorphism if and only if
    $u|_(U_i)$ is an isomorphism for every $i$.
]

#proof[

  + *Realize equalities of germs.* The first equivalence is the defining
    relation on germs. For finitely many equalities, intersect their witness
    neighborhoods. A finite intersection of open neighborhoods of $x$ is
    again an open neighborhood of $x$ (Check!). The finite hypothesis is
    necessary: in the sheaf of continuous real functions, the sections
    $s_n(t)=max(0, abs(t)-1/n)$ all have zero germ at $0$, but no neighborhood
    of $0$ makes every $s_n$ zero. Check the continuity and this last
    topological assertion.

  + *Compare sections.* Equality on an open cover implies equality by the uniqueness clause of the
    sheaf axiom. If two sections have equal germs at each $x$, the definition
    of a germ supplies a neighborhood of $x$ on which their restrictions agree;
    these neighborhoods cover the original open.

  + *Compare morphisms.* Apply the same argument to
    the two images of each section to detect equality of sheaf morphisms on
    stalks or on an open cover.

  + *Glue local inverses.* Finally, the inverses of locally invertible
    restrictions agree on overlaps: each is inverse to the same restricted map.
    They glue by SL-3, and the two inverse equations hold on a cover and hence
    globally. The proof of SL-3 uses only the sectionwise equality just proved.
]

#metadata(none) <sup-sl-2>
#proposition(number: "SL-2", title: "Sheaves on a basis")[
  Let $cal(B)$ be an open basis of $X$. Suppose objects $F(B)$ and
  restriction maps are given for inclusions of basis opens, and satisfy
  the identity and composition laws. Assume that every compatible family
  on a basis cover of $B$ has a unique gluing in $F(B)$.

  Compatibility on $B_1 inter B_2$ means equality after restriction to
  every basis open contained in $B_1 inter B_2$; the intersection need not
  itself belong to $cal(B)$.

  Then these data extend to a sheaf $F^e$ on $X$, unique up to the unique
  isomorphism preserving the specified basis data. For each open subset
  $U subset.eq X$, $F^e (U)$ consists of the compatible families
  $(s_B)_(B in cal(B), B subset.eq U)$, where $s_B in F(B)$.
  For open subsets $V subset.eq U$, the restriction map is
  $
                    rho_(U V): F^e (U) & -> F^e (V), \
    (s_B)_(B in cal(B), B subset.eq U) & mapsto (s_B)_(B in cal(B), B subset.eq V).
  $

  Every family of maps between two such sets of basis data that commutes
  with restriction extends to a unique morphism of the resulting sheaves.
]

#proof[

  + *Construct the extension.* For an open $U$, let $F^e (U)$ consist of families $(s_B)_(B subset.eq U)$,
    where $s_B in F(B)$ and restriction sends $s_B$ to $s_C$ whenever
    $C subset.eq B$. For $V subset.eq U$, define $rho_(U V)$ by the formula
    above. The resulting family is compatible because every basis open
    contained in $V$ is also contained in $U$. Moreover,
    $rho_(U U)=ops.id$ and
    $rho_(U W)=rho_(V W) compose rho_(U V)$ whenever
    $W subset.eq V subset.eq U$. Thus $F^e$ is a presheaf.

  + *Verify the sheaf axiom.* Given compatible such
    families on a cover $U_i$ of $U$, cover each basis open $B subset.eq U$
    by basis opens $C subset.eq B inter U_i$. Their specified sections agree
    on every basis open in an overlap. Basis gluing gives a unique $s_B$.
    For $B' subset.eq B$, uniqueness on a basis cover of $B'$ identifies the
    restriction of $s_B$ with $s_(B')$. Thus the $s_B$ form the desired family,
    and the same uniqueness proves the sheaf axiom for $F^e$.

  + *Identify the basis values and prove uniqueness.* For a basis open $B$, projection $F^e (B)->F(B)$ is inverse to taking all
    restrictions of a section of $F(B)$. If $G$ is any other extension,
    restriction gives $G(U)->F^e (U)$. Gluing over all basis opens in $U$
    constructs its inverse. These maps commute with restriction.

  + *Extend morphisms and operations.* Applying a
    compatible map of basis data componentwise gives the unique sheaf morphism
    extending it. All operations are componentwise, so the argument applies to
    the stated algebraic categories as well as sets.
]

#metadata(none) <sup-sl-3>
#lemma(number: "SL-3", title: "Gluing morphisms")[
  Let $U_i$ cover $X$ and let $u_i:shf.f|_(U_i)->shf.g|_(U_i)$ agree on
  every overlap.

  + There is a unique $u:shf.f->shf.g$ restricting to $u_i$.

  + It preserves the given group, ring, or module structure when each $u_i$
    does.

  See also #book-link(<sup-sc-5>)[SC-5] for the sheaf of these morphisms.
]

#proof[

  + *Glue the images of sections.* For $s in shf.f (V)$, the sections
    $u_i\(s|_(V inter U_i))$ agree on the overlaps $V inter U_i inter U_j$.
    Glue them in $shf.g$ and call the result $u_V\(s)$.

  + *Check restriction compatibility.* To compare restriction
    to $W subset.eq V$ with $u_W\(s|_W)$, restrict both to $W inter U_i$;
    they are equal there by the naturality of $u_i$, hence equal on $W$.
    Thus the $u_V$ define a sheaf morphism.

  + *Preserve the algebraic structure.* Addition, multiplication, units,
    and scalar multiplication are respected because the corresponding equations
    hold on this same cover.

  + *Prove uniqueness.* Any other extension has identical restrictions
    on $V inter U_i$ for every $V$, so is equal to $u$.
]

#metadata(none) <sup-sl-4>
#proposition(number: "SL-4", title: "Gluing sheaves")[
  Let $X=union_i U_i$ be an open cover. Suppose sheaves $shf.f_i$ on $U_i$
  are equipped with isomorphisms
  $phi_(i j):shf.f_i|_(U_i inter U_j)->shf.f_j|_(U_i inter U_j)$ such that
  $phi_(i i)=ops.id$ and
  $phi_(j k) compose phi_(i j)=phi_(i k)$ on every triple overlap.

  Then there are a sheaf $shf.f$ on $X$ and isomorphisms
  $rho_i:shf.f|_(U_i)->shf.f_i$ satisfying
  $rho_j=phi_(i j) compose rho_i$ on $U_i inter U_j$.
  The pair consisting of $shf.f$ and the maps $rho_i$ is unique up to
  a unique isomorphism compatible with all $rho_i$.

  For modules over a fixed $shf.o$, assume that each transition map is
  linear over $shf.o|_(U_i inter U_j)$. If the sheaf of rings is also
  obtained by gluing, assume instead that the module transitions respect
  the specified ring transitions and scalar actions.
  (Ex. II.1.22)
]

#proof[

  + *Construct the compatible-family presheaf.* For an open set $V subset.eq X$, define $shf.f (V)$ to be the set
    of compatible families
    $
      (s_i)_i,
      quad s_i in shf.f_i\(V inter U_i),
    $
    satisfying, on $V inter U_i inter U_j$,
    $
      phi_(i j)(s_i)=s_j.
    $
    The restriction maps are componentwise.  The identity and cocycle
    conditions imply that compatibility is preserved by restriction. For
    groups and rings, use componentwise operations. For modules, use the
    specified scalar action; if the rings are glued, their compatible
    families act componentwise. The algebraic operations preserve the
    compatibility equations (Check!). Thus these are presheaves in each
    of the stated categories.

  + *Verify the sheaf axiom.* To verify the sheaf axiom, cover $V$ by opens $V_a$ and take compatible
    sections $s^a=(s_i^a)_i$.  For each fixed $i$, the sections $s_i^a$ glue in
    the sheaf $shf.f_i$ to a unique
    $s_i in shf.f_i\(V inter U_i)$.  On a pairwise overlap, the equality
    $phi_(i j)(s_i)=s_j$ holds after restriction to every $V_a$; separatedness
    of $shf.f_j$ makes it hold globally.  Hence $(s_i)_i$ is a section of
    $shf.f\(V)$, and componentwise uniqueness proves uniqueness in $shf.f$.

  + *Identify the local pieces.* The construction also handles empty intersections, whose section objects
    are terminal.  Fix $i$.  Projection to the $i$-th component gives
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

  + *Prove uniqueness of the glued sheaf.* Finally, suppose $shf.g$ has another compatible family of isomorphisms
    $sigma_i:shf.g|_(U_i) simeq shf.f_i$.  The local maps
    $rho_i^(-1) compose sigma_i:shf.g|_(U_i)->shf.f|_(U_i)$ agree on overlaps,
    so SL-3 glues them to an isomorphism
    $shf.g simeq shf.f$.  Its restrictions are prescribed, hence the same
    separatedness argument makes it unique.
]

#metadata(none) <sup-sl-5>
#proposition(number: "SL-5", title: "Local representatives in sheafification")[
  Let $shf.f$ be a presheaf, and let $eta:shf.f->shf.f^+$ be the canonical map of
  #book-link(<text-ii-1>)[II.1, Proposition 1.2].

  + For every open $U$ and $sigma in shf.f^+(U)$, there are an open cover
    $U=union_i U_i$ and sections $s_i in shf.f\(U_i)$ such that
    $eta_(U_i)(s_i)=sigma|_(U_i)$ for every $i$.

  + For $s,t in shf.f\(U)$, the equality $eta_U\(s)=eta_U\(t)$ holds if and only
    if there is an open cover $U=union_i U_i$ such that
    $s|_(U_i)=t|_(U_i)$ for every $i$.

  + For every $x in X$, the canonical map $shf.f_x->(shf.f^+)_x$ is an isomorphism.

  These assertions apply to each of the algebraic structures specified
  above. Exactness and local lifting are treated in
  #book-link(<sup-sc-4>)[SC-4].
]

#proof[

  + *Find local representatives.* Use the construction in II.1, Proposition 1.2: a section of $shf.f^+$ is a
    family of germs locally induced by a section of $shf.f$. This immediately gives
    local representatives.

  + *Detect equality locally.* The images of $s,t in shf.f\(U)$ agree if and only if
    their germs agree at every point. By the germ relation, each point then has
    a neighborhood on which $s,t$ restrict equally, which proves the local
    equality criterion.

  + *Compare stalks.* Every germ of $shf.f^+$ is represented near its point by
    an original section, so $shf.f_x->(shf.f^+)_x$ is surjective. If two original
    germs have the same image, choose a common neighborhood on which their
    images agree; the local equality criterion, at the specified point, makes
    the original germs equal. This proves injectivity. The construction respects
    the original operations, and the bijection is consequently an isomorphism
    in each of the stated categories.
]
