#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

=== SE — Support, extension and local freeness <sup-se>

Use #book-link(<sup-sc>)[SC] for exactness and restriction,
#book-link(<sup-al>)[AL] for finite presentation and Nakayama, and
#book-link(<sup-qc>)[QC] for the affine dictionary. The section-extension result
for powers of an invertible-sheaf section remains in
#book-link(<text-ii-5>)[II.5, Lemma 5.14 and Remark 5.14.1].

#metadata(none) <sup-se-1>
#definition(number: "SE-1", title: "Two notions of support")[
  - For an abelian-group or module sheaf $shf.f$ and $s in shf.f (U)$, its
    support is ${x in U:s_x!=0}$; this is closed in $U$.

  - The support of the sheaf is ${x in X:shf.f_x!=0}$ and need not be closed.

  - A section with zero germs everywhere is zero by #book-link(<sup-sl-1>)[SL-1].
]

#proof[
  #set enum(numbering: "1.")

  + *Section support.* A zero germ has a representative that is zero on a neighborhood. Hence
    the zero-germ locus of $s$ is open in $U$, and its complement is closed.

  + *Sheaf support.* For sheaf support, there is no single section or finite list of sections
    to which this argument applies. Example SE-E1 below shows the
    failure of closedness; SL-1 proves the last assertion.
]

#metadata(none) <sup-se-2>
#proposition(number: "SE-2", title: "Annihilators")[
  - On $ops.spec A$, a section corresponding to $m in M$ has support
    $V(ops.ann(m))$, without a finiteness hypothesis on $M$.

  - If $M$ is finite, $ops.supp(tildeOf(M))=V(ops.ann(M))$.
    The assertion for the entire module need not hold without finite generation.
    These give the affine forms of II.5.6(a)–(c).
]

#proof[
  #set enum(numbering: "1.")

  + *The support of a section.* At the prime $idl.p$, the germ $m/1$ is zero exactly when some
    $a in.not idl.p$ kills $m$, by the localization zero criterion.
    Negating this says $ops.ann(m) subset.eq idl.p$, proving the first
    formula.

  + *The support of a finite module.* If $m_1,dots,m_r$ generate $M$, then $M_idl.p=0$ precisely
    when all their localized images vanish. Choose annihilators outside
    $idl.p$ for these finitely many generators and multiply them; their
    product annihilates all of $M$ and remains outside $idl.p$. Conversely,
    such an annihilator forces $M_idl.p=0$. This proves the second formula
    and identifies exactly where finite generation is needed.
]

#metadata(none) <sup-se-3>
#definition(number: "SE-3", title: "Sections with support")[
  For a closed subset $Z$ and $j:U=X minus Z->X$, let $shf.h_Z(shf.f)$
  be the subsheaf of sections whose support is contained in $Z$.
]

#proposition(number: "SE-3.1", title: "The restriction sequence for sections with support")[
  - There is a left-exact sequence
    $0->shf.h_Z(shf.f)->shf.f->j_*(shf.f|_U)$,
    with the last map given by restriction. Equivalently, the support subsheaf
    is its kernel.

  - Taking global sections gives the corresponding left-exact
    sequence of groups; there is no general surjectivity assertion at the end.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the kernel sheaf.* For an open $V$, the kernel of
    $shf.f (V)->shf.f (V inter U)$ consists exactly of the sections whose
    germs vanish on $V inter U$, by SL-1. This is precisely support in
    $V inter Z$. These identifications commute with restriction, so the
    support subsheaf is the kernel sheaf.

  + *Take global sections.* Kernels and global sections are
    left exact, which gives both asserted sequences. A section on the
    complement need not extend across $Z$, so no surjectivity follows.
]

#metadata(none) <sup-se-4>
#definition(number: "SE-4", title: "Extension by zero")[
  - For an open inclusion $j:U->X$ and an abelian-group sheaf $shf.g$ on $U$,
    $j_!shf.g$ has, on an open $V$, sections of $shf.g (V inter U)$ whose
    support is closed in $V$. It has stalk $shf.g_x$ on $U$ and zero off $U$.

  - For $i:Z=X minus U->X$, the closed-inclusion direct image $i_*shf.h$
    has stalk $shf.h_x$ on $Z$ and zero off $Z$.
]

#proof[
  #set enum(numbering: "1.")

  + *Verify the sheaf construction.* The displayed assignments satisfy the sheaf axiom: compatible sections
    glue on $V inter U$, and the condition that their support be closed in
    $V$ is local on an open cover of $V$. Restrictions preserve the
    condition.

  + *Compute extension-by-zero stalks.* Near a point of $U$ one may restrict entirely inside $U$,
    which identifies the stalk with $shf.g_x$. At a point outside $U$, a
    section has closed support avoiding that point and is zero on its open
    complement, so its germ is zero.

  + *Compute closed direct-image stalks.* For $i_*$, intersections $V inter Z$
    of neighborhoods give all neighborhoods in $Z$, proving the stalk
    formula there; outside the closed subset choose a disjoint neighborhood.
]

#proposition(number: "SE-4.1", title: "The open-closed exact sequence")[
  - For any abelian-group sheaf $shf.f$ on $X$, there is an exact sequence
    $0->j_!(shf.f|_U)->shf.f->i_*(i^(-1)shf.f)->0$.
    The maps are extension by zero and restriction to the closed subspace.

  - For modules, equip $U,Z$ with the restricted sheaf of rings; the same
    constructions and sequence are linear. This is not a construction for
    ring sheaves, and $j_!$ is not $j_*$.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the maps.* A section on $V inter U$ with support closed in $V$ glues with zero
    on the complement of its support to give a section on $V$. These
    extension maps commute with restriction. The other map is the unit of
    inverse image and direct image for $i$.

  + *Check exactness on stalks.* On a stalk in $U$, the sequence
    is $0->shf.f_x ->^(ops.id) shf.f_x->0->0$; on a stalk in $Z$ it is
    $0->0->shf.f_x ->^(ops.id) shf.f_x->0$. The inverse-image stalk formula
    and SE-4 justify these identifications. Stalkwise exactness in SC
    proves the sequence.

  + *Retain the module structures.* Restricted ring actions preserve all maps, giving
    the module version. Extension by zero cannot preserve a multiplicative
    identity at the excluded stalks, which explains the stated limitation.
]

#metadata(none) <sup-se-5>
#proposition(number: "SE-5", title: "Support torsion")[
  - On $X=ops.spec A$ with $A$ Noetherian and $Z=V(I)$, the support
    subsheaf of $tildeOf(M)$ corresponds to
    ${m in M:I^n m=0 " for some " n>=0}$.

  - Consequently, on a Noetherian scheme, sections supported in a fixed closed
    subset form a quasi-coherent subsheaf of any quasi-coherent module, and a
    coherent subsheaf of any coherent module. These are the support-torsion
    statements of II.5.6(d)–(e).
]

#proof[
  #set enum(numbering: "1.")

  + *Identify support with ideal-power torsion.* By SE-2, the support of $m$ lies in $V(I)$ exactly when
    $I subset.eq sqrt(ops.ann(m))$. Choose finite generators
    $a_1,dots,a_r$ of $I$. If $a_i^(n_i)m=0$, every monomial of degree
    greater than $sum_i(n_i-1)$ contains one of these powers; hence some
    power of $I$ annihilates $m$. The converse is immediate.

  + *Check localization of torsion.* Write $T$ for this torsion submodule. On $D(a)$, its localization equals
    the torsion submodule of $M_a$ for $I_a$. One inclusion is immediate.
    For the other, if $(I_a)^n(m/a^q)=0$, take finite generators of $I^n$
    and clear the finitely many denominators in these zero equalities.
    Then $a^d m$ is killed by $I^n$, so $m/a^q$ lies in $T_a$.

  + *Identify and glue the support subsheaf.* Thus the support sheaf is $tildeOf(T)$ on the distinguished basis.
    These identifications concern the same support kernel and agree on
    overlaps, proving quasi-coherence. If $M$ is finite over the Noetherian
    ring, its submodule $T$ is finite, giving coherence.
]

#metadata(none) <sup-se-6>
#proposition(number: "SE-6", title: "Coherent extension")[
  - Let $X$ be Noetherian and $U$ open. A coherent module on $U$ extends
    to a coherent module on $X$.

  - More precisely, if it is a subsheaf of
    $shf.g|_U$ for a quasi-coherent $shf.g$ on $X$, it is the restriction
    of a coherent subsheaf of $shf.g$. The extension is neither canonical
    nor unique (II.5.15).
]

#proof[
  #set enum(numbering: "1.")

  + *Construct a quasi-coherent enlargement.* First suppose $shf.f subset.eq shf.g|_U$ is coherent. We extend across
    one affine open $V=ops.spec A$ at a time. Work on $U union V$ and let
    $j:U->U union V$. Every open immersion between Noetherian schemes is
    quasi-compact and quasi-separated. QC-5 therefore makes the kernel
    $shf.h=ops.ker(shf.g->j_*(shf.g|_U\/shf.f))$ quasi-coherent,
    with $shf.h|_U=shf.f$. Write $shf.h|_V=tildeOf(H)$.

  + *Choose finite numerators and glue.* The open $U inter V$ is quasi-compact, so cover it by finitely many
    principal opens $D(a_i)$ of $V$. On each, $H_(a_i)$ is finite because
    it represents $shf.f$. Choose finitely many generating fractions and
    let $N subset.eq H$ be generated by all their numerators. Multiplication
    by the denominator units shows $N_(a_i)=H_(a_i)$ for every $i$.
    Thus $tildeOf(N)$ and $shf.f$ are the same subsheaf of $shf.g$ on
    $U inter V$. Glue them using this equality, as in SL. Since $N$ is
    finite over the Noetherian ring $A$, the resulting subsheaf on
    $U union V$ is coherent and extends $shf.f$. A finite affine cover of
    $X$ lets us repeat this step finitely many times and reach all of $X$.

  + *Extend an arbitrary coherent module.* For an arbitrary coherent $shf.f$ on $U$, take
    $shf.g=j_*shf.f$ on $X$. QC-5 makes it quasi-coherent, and the
    restriction $shf.g|_U=shf.f$ gives the required inclusion. The case
    just proved supplies a coherent extension. Choices of numerators make
    the procedure noncanonical; Example SE-E4 proves nonuniqueness.
]

#metadata(none) <sup-se-7>
#corollary(number: "SE-7", title: "Coherent approximation")[
  On a Noetherian scheme, every quasi-coherent module is the directed union
  of its coherent subsheaves. The ordering is inclusion; the sum of two
  coherent subsheaves is another coherent subsheaf. This is the approximation
  part of II.5.15, using the extension statement above.
]

#proof[
  #set enum(numbering: "1.")

  + *Check directedness.* The sum of two coherent subsheaves is the image of their finite direct
    sum, so it is coherent by QC-6 and contains both.

  + *Contain every germ.* To see that their
    directed union is all of $shf.g$, represent a germ at $x$ on an affine
    neighborhood $V=ops.spec A$ by a fraction in the module defining
    $shf.g|_V$. Its numerator generates a finite submodule, whose associated
    sheaf contains the germ. SE-6 extends this coherent subsheaf of
    $shf.g|_V$ to a coherent subsheaf of $shf.g$ on $X$. Thus every germ
    lies in the union.

  + *Identify the union.* Filtered colimits have the indicated stalks by SC,
    so SL-1 identifies the union with $shf.g$.
]

#metadata(none) <sup-se-8>
#lemma(number: "SE-8", title: "Free stalks and neighborhoods")[
  If a module sheaf is finitely presented and its stalk at $x$ is free,
  it is free of the same finite rank on a neighborhood of $x$.
  The Noetherian coherent case, and the criterion that all stalks be free,
  are proved in #book-link(<sup-proof-5-7>)[II.5.7(a)–(b)].
  Finite presentation provides the finite relations needed to pass from a
  stalk isomorphism to a neighborhood isomorphism; see #book-link(<sup-al-8>)[AL-8].
]

#proof[
  #set enum(numbering: "1.")

  + *Pass to a finitely presented affine module.* Restrict a finite-presentation neighborhood to an affine
    $V=ops.spec A$ containing $x$. QC-7 and the affine correspondence write
    $shf.f|_V=tildeOf(M)$ with $M$ finitely presented. If $idl.p$ represents
    $x$, its stalk is $M_idl.p$, free of some finite rank $r$.

  + *Spread the stalk isomorphism.* AL-8 spreads a basis and its finite relations to one localization:
    there is $a in.not idl.p$ and an isomorphism $A_a^r->M_a$ whose
    further localization is the chosen stalk isomorphism. Associated
    sheaves give $shf.o_(D(a))^r simeq shf.f|_(D(a))$. The open $D(a)$
    contains $x$, which proves the precise rank assertion.
]

#metadata(none) <sup-se-9>
#proposition(number: "SE-9", title: "Fiber rank")[
  Let $shf.f$ be a coherent module on a Noetherian scheme $X$. Define
  $r(x)=ops.dim(tensor(shf.f_x, kappa(x), over: shf.o_(X,x)), over: kappa(x))$.

  - The function is upper semicontinuous: the loci $r(x)>=n$ are closed.

  - If $X$ is reduced, then $shf.f$ is locally free if and only if
    $r$ is locally constant.

  - A finite locally free sheaf has locally constant rank on any
    scheme, and constant rank if the scheme is connected (II.5.8).
]

#proof[
  #set enum(numbering: "1.")

  + *Prove upper semicontinuity.* On an affine Noetherian chart, write $shf.f=tildeOf(M)$ with $M$
    finite. At a prime $idl.p$ with $r(idl.p)<=q$, lift a residue-field
    basis to elements of $M_idl.p$, and clear their denominators to use
    elements of $M$. Nakayama gives a surjection $A_idl.p^q->M_idl.p$,
    padding the list with zero if necessary. The induced map $A^q->M$
    has finite cokernel whose localization at $idl.p$ is zero. By SE-2,
    one element $a in.not idl.p$ kills that cokernel, so $A_a^q->M_a$
    is surjective. Tensoring with the residue field at any point of $D(a)$
    remains surjective and gives fiber dimension at most $q$. Thus the
    locus $r<=q$ is open. Its complement $r>=q+1$ is closed, as claimed;
    the locus $r>=0$ is all of $X$.

  + *Use reducedness to obtain local freeness.* Suppose now that $A$ is reduced and the fiber rank is constantly $r$
    near a given point. Lift a residue-field basis to the module. Nakayama
    and the finite-support criterion of SE-2, applied to the cokernel,
    let us shrink to a principal neighborhood on which these lifts give
    a surjection $A^r->M$. Its kernel $K$ is finite. At every prime in
    this neighborhood, the induced surjection of residue-field vector
    spaces has equal dimensions and is an isomorphism. Therefore every
    vector of $K subset.eq A^r$ has all its coordinates in every prime:
    its residue vector is zero. The intersection of the primes is zero
    in the reduced ring, so $K=0$. The surjection is an isomorphism and
    $shf.f$ is free on this neighborhood.

  + *Read rank from a local basis.* Conversely, a local basis of size $r$ remains a basis after passage to
    every residue field in its domain, so a finite locally free sheaf has
    locally constant rank on any scheme. A locally constant integer-valued
    function on a connected space is constant, since each level set and its
    complement are open.
]

#metadata(none) <sup-se-10>
#corollary(number: "SE-10", title: "Invertible modules")[
  On a Noetherian scheme, a coherent module $shf.f$ is invertible exactly
  when there is a coherent $shf.g$ with
  $tensor(shf.f, shf.g, over: shf.o_X) simeq shf.o_X$.
  An inverse is its dual. See #book-link(<sup-proof-5-7>)[II.5.7(c)] and
  #book-link(<sup-al-9>)[AL-9] for the local algebra.
]

#metadata(none) <sup-se-examples>
#example(number: "SE-E1", title: "Counterexamples")[
  On $ops.spec ZZ$, let $M$ be the direct sum of $ZZ\/p ZZ$ over all
  positive primes $p$. Its sheaf has support all closed points and not the
  generic point, a nonclosed subset. Yet $ops.ann(M)=0$. In contrast,
  $tildeOf(QQ)$ has nonzero stalk $QQ$ at every point, so it is not an
  example of nonclosed sheaf support.
]

#proof[
  Localization commutes with direct sums. At $(p)$, only the summand $ZZ\/p ZZ$ survives, whereas at $(0)$, every summand vanishes. The closed points are dense: an integer divisible by every prime is zero. The same fact gives the zero annihilator of $M$. Every nonzero integer already acts invertibly on $QQ$, so all its localizations remain $QQ$.
]

#example(number: "SE-E2", title: "Counterexamples")[
  On $ops.spec(k[epsilon]\/(epsilon^2))$, the module $tildeOf(k)$ has
  constant fiber rank one but is not locally free.
]

#proof[
  There is one prime, with residue field $k$, and the fiber of the module $k$ is $k$. A free module with this fiber would have rank one and be isomorphic to $k[epsilon]\/(epsilon^2)$. But $epsilon$ annihilates $k$ and does not annihilate that ring, ruling out such an isomorphism.
]

#example(number: "SE-E3", title: "Counterexamples")[
  For $j:(0,1)->RR$ and the constant $ZZ$ sheaf on $(0,1)$, $j_*$ has
  nonzero stalks at the endpoints, while $j_!$ has zero stalks there.
]

#proof[
  Sufficiently small neighborhoods of either endpoint intersect $(0,1)$ in a nonempty interval. Sections of the constant sheaf there are $ZZ$, and the restriction maps are identities. Their colimit is $ZZ$, the direct-image stalk. Extension by zero has zero stalk outside the open by SE-4.
]

#example(number: "SE-E4", title: "Counterexamples")[
  The sheaves $shf.o (n)$ on $sch.p^1_k$ all restrict to the trivial
  invertible sheaf on a standard affine line but are not mutually isomorphic
  on the projective line. Coherent extensions need not be unique.
]

#proof[
  The standard trivialization of each twisting sheaf gives the claimed affine restriction. If $shf.o (n) simeq shf.o (m)$, tensoring by $shf.o (-m)$ gives $shf.o (n-m) simeq shf.o$. The standard projective-line section calculation gives zero global sections in negative degree and dimension $d+1$ in degree $d>=0$; only degree zero can be trivial. Thus $n=m$.
]

#block(sticky: true)[#strong[Application: II.5.7]] <sup-proof-5-7>

#exercise(title: "Exercise 5.7")[
  Let $X$ be noetherian and $shf.f$ coherent.

  + If $shf.f_x$ is free, show $shf.f$ is free on a neighborhood of $x$.
  + Deduce $shf.f$ is locally free iff all stalks are free.
  + Show $shf.f$ is invertible iff some coherent $shf.g$ satisfies
    $tensor(shf.f, shf.g, over: shf.o_X) simeq shf.o_X$.
]

#proof[
  #set enum(numbering: "a)", spacing: 1em)

  + *Spread a free stalk to a neighborhood.*

    - *Choose an affine chart.* Choose an affine neighborhood $U=ops.spec A$ of $x$.  Since $X$ is
      noetherian and $shf.f$ is coherent, we may write
      $shf.f|_U simeq tildeOf(M)$ with $A$ noetherian and $M$ finite.  Let
      $idl.p$ correspond to $x$.  By Proposition 5.1(b), the hypothesis says
      that $M_idl.p$ is a finite free $A_idl.p$-module, say of rank $r$.

    - *Spread the basis and surjectivity.* Represent a basis of $M_idl.p$ by fractions $m_i/s_i$ with
      $s_i in.not idl.p$.  Multiplying each basis vector by the unit $s_i$
      shows that the images of $m_1,dots.c,m_r in M$ still form a basis.  Let
      $
        phi:A^r -> M, quad (a_i) mapsto sum_i a_i m_i.
      $
      The localization of $C=ops.coker(phi)$ at $idl.p$ is zero.  The module
      $C$ is finite, so a single element $a in.not idl.p$ annihilates all of a
      finite set of generators of $C$.  Hence $C_a=0$ and $phi_a$ is
      surjective.

    - *Kill the kernel.* Put $K=ops.ker(phi)$.  Since $A$ is noetherian, $K subset.eq A^r$ is
      finite.  Also $K_idl.p=0$, because $phi_idl.p$ is an isomorphism.  Thus
      some $b in.not idl.p$ kills a finite set of generators of $K$, so
      $K_b=0$.  For $h=a b in.not idl.p$, the map
      $
        phi_h:A_h^r simeq M_h
      $
      is an isomorphism.  Consequently,
      $shf.f|_(D(h)) simeq shf.o_(D(h))^r$, and $D(h)$ is the desired
      neighborhood of $x$.

  + If $shf.f$ is locally free, every stalk is the corresponding free module
    over the local ring.  Conversely, if every stalk is free, part (a)
    supplies, for every $x$, a neighborhood on which $shf.f$ is free.  These
    neighborhoods cover $X$, so $shf.f$ is locally free.

  + *Characterize invertibility by a tensor inverse.*

    - *Use the dual of an invertible sheaf.* Suppose first that $shf.f$ is invertible.  It is locally free of rank
      one, hence coherent, and its dual $shf.g=shf.f^ast$ is also locally free
      of rank one and coherent.  The evaluation map
      $
        tensor(shf.f, shf.f^ast, over: shf.o_X) -> shf.o_X
      $
      is an isomorphism locally on every trivializing open, and hence globally.

    - *Reduce to cyclic modules at a stalk.* Conversely, suppose a coherent $shf.g$ satisfies
      $tensor(shf.f, shf.g, over: shf.o_X) simeq shf.o_X$.  At a point $x$, put
      $
        R=shf.o_(X,x), quad M=shf.f_x, quad N=shf.g_x.
      $
      Then $R$ is local, $M,N$ are finite, and
      $tensor(M, N, over: R) simeq R$.  After tensoring with the residue field $k(x)$,
      $
        tensor(M/frak(m)M, N/frak(m)N, over: k(x)) simeq k(x).
      $
      Both factors are nonzero finite-dimensional vector spaces, and the
      product of their dimensions is $1$; each therefore has dimension $1$.
      Choose $m in M$ and $n in N$ lifting bases.  Nakayama's lemma shows that
      $m$ and $n$ generate $M$ and $N$.

    - *Prove that the cyclic module is free.* The map $R->tensor(M, N, over: R)$ sending $1$ to $tensor(m, n)$ is
      surjective by Nakayama.  Composing with an isomorphism
      $tensor(M, N, over: R) simeq R$ gives a
      surjective endomorphism of the rank-one free module $R$, hence
      multiplication by a unit; it is injective.  If $a m=0$, then
      $a tensor(m, n)=0$, so $a=0$.  Thus $R->M$, $a mapsto a m$, is also
      injective, and it is already surjective.  Hence $M simeq R$.

    - *Spread rank one to neighborhoods.* We have proved that every stalk $shf.f_x$ is free of rank one.  Part (a)
      applied with rank $1$ gives a neighborhood of each point on which
      $shf.f$ is free of rank $1$.  Therefore $shf.f$ is invertible.
]
