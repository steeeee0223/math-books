#import "@steee-book/blocks:0.1.0": *
#import "@steee-book/symbols:0.1.0": *

#show: show-blocks

#supplement-numbering("SL")

== SL — Sheaf locality and gluing <sup-sl>

Use the definitions and stalkwise isomorphism criterion of
#book-link(<text-ii-1>)[II.1, D1–D4 and Proposition 1.1]. Throughout this section, sheaves take values in sets, abelian groups, rings, or modules over a fixed sheaf of rings $shf.o$.

#set enum(numbering: "a.i.", spacing: 0.7em)

#lemma(key: "sup-sl-1", title: "Local equality")[
  Let $shf.f,shf.g$ be sheaves on $X$.

  + Equality of germs.

    + For $s in shf.f\(U)$, $t in shf.f\(V)$, and $x in U inter V$,
      $s_x=t_x$ if and only if there is an open neighborhood
      $x in W subset U inter V$ with $s|_W=t|_W$.
    + Any finite family of germ equalities at $x$ holds on a common neighborhood of $x$.
    + An infinite family need not hold on a common neighborhood.

  + If $U=union_i U_i$ and $s,t in shf.f\(U)$, then
    $
      s=t & arrow.l.r.double s|_(U_i)=t|_(U_i) " for every " i \
          & arrow.l.r.double s_x=t_x " for every " x in U.
    $

  + Equality and isomorphisms of sheaf morphisms on a cover $X=union_i U_i$.

    + For $u,v:shf.f to shf.g$,
      $
        u=v & arrow.l.r.double u|_(U_i)=v|_(U_i) " for every " i \
            & arrow.l.r.double u_x=v_x " for every " x in X.
      $
    + $u$ is an isomorphism if and only if $u|_(U_i)$ is an isomorphism for every $i$.
]

#proof[

  + The first equivalence is the defining
    relation on germs. For finitely many equalities, intersect their witness
    neighborhoods. A finite intersection of open neighborhoods of $x$ is
    again an open neighborhood of $x$ (Check!). The finite hypothesis is
    necessary: in the sheaf of continuous real functions, the sections
    $s_n(t)=max(0, abs(t)-1/n)$ all have zero germ at $0$, but no neighborhood
    of $0$ makes every $s_n$ zero. Check the continuity and this last
    topological assertion.

  + Equality on an open cover implies equality by the uniqueness clause of the
    sheaf axiom. If two sections have equal germs at each $x$, the definition
    of a germ supplies a neighborhood of $x$ on which their restrictions agree;
    these neighborhoods cover the original open.

  + Apply the same argument to
    the two images of each section to detect equality of sheaf morphisms on
    stalks or on an open cover.

  + If each restriction is invertible, then each stalk map is
    invertible, since every point lies in a member of the cover. The stalkwise
    isomorphism criterion of II.1, Proposition 1.1 makes $u$ invertible.
    Conversely, restriction preserves an inverse and its two identities.
]

#proposition(key: "sup-sl-2", title: "Sheaves on a basis")[
  Let $cal(B)$ be an open basis of $X$, with objects $F(B)$ and restrictions
  $rho_(B C):F(B) to F(C)$ for $C subset B$ in $cal(B)$. Assume
  $rho_(B B)=ops.id$, $rho_(C D) compose rho_(B C)=rho_(B D)$, and unique
  gluing for basis covers. On an overlap, compatibility means equality on
  every basis open contained in that overlap.

  + Define the _extension presheaf_ $F^e$ by
    $
      F^e(U)=\{(s_B)_(B in cal(B), B subset U): s_B in F(B),\
      rho_(B C)(s_B)=s_C " whenever " C subset B subset U\}.
    $

    It is already a sheaf, the _extension sheaf_ of the basis data.

    + For $V subset U$, restriction is
      $
         rho_(U V): F^e(U) & to F^e(V), \
        (s_B)_(B subset U) & mapsto (s_B)_(B subset V).
      $
    + $F^e(B) simeq F(B)$, naturally in $B in cal(B)$.
    + The extension is unique up to a unique isomorphism inducing the identity on the basis data.

  + A family $u_B:F(B) to G(B)$ commuting with restrictions
    extends uniquely to $u:F^e to G^e$.
]

#proof[

  + For an open $U$, let $F^e (U)$ consist of families $(s_B)_(B subset U)$,
    where $s_B in F(B)$ and restriction sends $s_B$ to $s_C$ whenever
    $C subset B$. For $V subset U$, define $rho_(U V)$ by the formula
    above. The resulting family is compatible because every basis open
    contained in $V$ is also contained in $U$. Moreover,
    $rho_(U U)=ops.id$ and
    $rho_(U W)=rho_(V W) compose rho_(U V)$ whenever
    $W subset V subset U$. Thus $F^e$ is a presheaf.

  + Given compatible such
    families on a cover $U_i$ of $U$, cover each basis open $B subset U$
    by basis opens $C subset B inter U_i$. Their specified sections agree
    on every basis open in an overlap. Basis gluing gives a unique $s_B$.
    For $B' subset B$, uniqueness on a basis cover of $B'$ identifies the
    restriction of $s_B$ with $s_(B')$. Thus the $s_B$ form the desired family,
    and the same uniqueness proves the sheaf axiom for $F^e$.

  + For a basis open $B$, projection $F^e (B)->F(B)$ is inverse to taking all
    restrictions of a section of $F(B)$. If $G$ is any other extension,
    restriction gives $G(U)->F^e (U)$. Gluing over all basis opens in $U$
    constructs its inverse. These maps commute with restriction.

  + Applying a
    compatible map of basis data componentwise gives the unique sheaf morphism
    extending it. All operations are componentwise, so the argument applies to
    the stated algebraic categories as well as sets.
]

#lemma(key: "sup-sl-3", title: "Gluing sheaf morphisms")[
  Let $X=union_i U_i$ and let $u_i:shf.f|_(U_i) to shf.g|_(U_i)$ satisfy
  $u_i|_(U_i inter U_j)=u_j|_(U_i inter U_j)$ for all $i,j$. There is a unique $u:shf.f to shf.g$ with $u|_(U_i)=u_i$ for every $i$.
  If each $u_i$ preserves the group, ring, or module operations, so does $u$.
]

#proof[

  + For $s in shf.f\(V)$, the sections
    $u_i\(s|_(V inter U_i))$ agree on the overlaps $V inter U_i inter U_j$.
    Glue them in $shf.g$ and call the result $u_V\(s)$.

  + To compare restriction
    to $W subset V$ with $u_W\(s|_W)$, restrict both to $W inter U_i$;
    they are equal there by the naturality of $u_i$, hence equal on $W$.
    Thus the $u_V$ define a sheaf morphism.

  + Addition, multiplication, units,
    and scalar multiplication are respected because the corresponding equations
    hold on this same cover.

  + Any other extension has identical restrictions
    on $V inter U_i$ for every $V$, so is equal to $u$.
]

#proposition(key: "sup-sl-4", title: "Gluing sheaves")[
  Let $X=union_i U_i$. Let $shf.f_i$ be sheaves on $U_i$ with isomorphisms
  $phi_(i j):shf.f_i|_(U_i inter U_j) to shf.f_j|_(U_i inter U_j)$ satisfying
  $
    phi_(i i)=ops.id, quad
    phi_(j k) compose phi_(i j)=phi_(i k) " on " U_i inter U_j inter U_k.
  $

  For modules over $shf.o$, assume each $phi_(i j)$ is
  $shf.o|_(U_i inter U_j)$-linear. If the rings are also glued, assume
  $phi_(i j)(a s)=psi_(i j)(a) phi_(i j)(s)$ for the ring transitions $psi_(i j)$.

  Define the _gluing presheaf_ by assigning to each open $V subset X$
  the families $s_i in shf.f_i(V inter U_i)$ satisfying
  $
    phi_(i j)(s_i|_(V inter U_i inter U_j))=s_j|_(V inter U_i inter U_j),
  $
  with componentwise restriction. It is already a sheaf, the _glued sheaf_ $shf.f$.

  + Projection gives isomorphisms $rho_i:shf.f|_(U_i) to shf.f_i$ with
    $rho_j=phi_(i j) compose rho_i$ on $U_i inter U_j$.
  + $(shf.f,(rho_i)_i)$ is unique up to a unique isomorphism respecting every $rho_i$.

  (Ex. II.1.22)
]

#proof[

  + For an open set $V subset X$, define $shf.f\(V)$ to be the set
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

  + To verify the sheaf axiom, cover $V$ by opens $V_a$ and take compatible
    sections $s^a=(s_i^a)_i$.  For each fixed $i$, the sections $s_i^a$ glue in
    the sheaf $shf.f_i$ to a unique
    $s_i in shf.f_i\(V inter U_i)$.  On a pairwise overlap, the equality
    $phi_(i j)(s_i)=s_j$ holds after restriction to every $V_a$; separatedness
    of $shf.f_j$ makes it hold globally.  Hence $(s_i)_i$ is a section of
    $shf.f\(V)$, and componentwise uniqueness proves uniqueness in $shf.f$.

  + The construction also handles empty intersections, whose section objects
    are terminal.  Fix $i$.  Projection to the $i$-th component gives
    $rho_i:shf.f|_(U_i)->shf.f_i$.  It is an isomorphism.  Indeed, if
    $t in shf.f_i(V)$ for $V subset U_i$, its inverse image has $j$-th
    component
    $
      phi_(i j)(t|_(V inter U_j)).
    $
    The cocycle condition makes these components compatible, and the identity
    condition makes the $i$-th component equal to $t$.  The same computation
    shows that on $U_i inter U_j$ one has
    $rho_j=phi_(i j) compose rho_i$.

  + Finally, suppose $shf.g$ has another compatible family of isomorphisms
    $sigma_i:shf.g|_(U_i) simeq shf.f_i$.  The local maps
    $rho_i^(-1) compose sigma_i:shf.g|_(U_i)->shf.f|_(U_i)$ agree on overlaps,
    so SL-3 glues them to an isomorphism
    $shf.g simeq shf.f$.  Its restrictions are prescribed, hence the same
    separatedness argument makes it unique.
]

#proposition(key: "sup-sl-5", title: "Local representatives in sheafification")[
  Let $eta:shf.f to shf.f^+$ be the sheafification of a presheaf on $X$.

  + For $sigma in shf.f^+(U)$, there exist a cover
    $U=union_i U_i$ and $s_i in shf.f\(U_i)$ with
    $eta_(U_i)(s_i)=sigma|_(U_i)$.

  + For $s,t in shf.f\(U)$, $eta_U(s)=eta_U(t)$ if and only if there is
    a cover $U=union_i U_i$ with $s|_(U_i)=t|_(U_i)$ for every $i$.

  + For every $x in X$, $eta_x:shf.f_x to (shf.f^+)_x$ is an isomorphism.
]

#proof[

  + Use the construction in II.1, Proposition 1.2: a section of $shf.f^+$ is a
    family of germs locally induced by a section of $shf.f$. This immediately gives
    local representatives.

  + The images of $s,t in shf.f\(U)$ agree if and only if
    their germs agree at every point. By the germ relation, each point then has
    a neighborhood on which $s,t$ restrict equally, which proves the local
    equality criterion.

  + Every germ of $shf.f^+$ is represented near its point by
    an original section, so $shf.f_x->(shf.f^+)_x$ is surjective. If two original
    germs have the same image, choose a common neighborhood on which their
    images agree; the local equality criterion, at the specified point, makes
    the original germs equal. This proves injectivity. The construction respects
    the original operations, and the bijection is consequently an isomorphism
    in each of the stated categories.
]
