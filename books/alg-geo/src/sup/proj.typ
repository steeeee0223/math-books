#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

=== PJ — Proj and graded modules <sup-pj>

The geometric part uses #book-link(<text-ii-2>)[II.2, D4 and Proposition 2.5]
for Proj and its affine charts. The module part uses
#book-link(<text-ii-5>)[II.5.11–II.5.16] for graded associated sheaves, twists,
sections, and reconstruction. Generation, finiteness of sections, and
projective pushforward remain in II.5.17–II.5.20; projective morphisms and
their properness remain in #book-link(<text-ii-4>)[II.4, Theorem 4.9].

#metadata(none) <sup-pj-1>
#lemma(number: "PJ-1", title: "Empty Proj")[
  Let $S$ be a nonnegatively graded ring. Then $ops.proj S=emptyset$ if
  and only if, for every $s in S_+$, there is an integer $n>=1$ such that
  $s^n=0$.
  The exponent $n$ may depend on $s$; a common nilpotence exponent for
  the entire ideal $S_+$ is not required (II.2.14(a)).
]

#proof[
  #set enum(numbering: "1.")

  + *Test emptiness on homogeneous affine charts.* The opens $D_+(f)$ for homogeneous $f$ of positive degree cover
    $ops.proj S$. By II.2.5, such an open is the spectrum of $(S_f)_0$.
    This spectrum is empty exactly when its ring is zero, equivalently
    $1=0$ in $S_f$, or $f^m=0$ for some $m$. Thus Proj is empty exactly
    when every positive-degree homogeneous element is nilpotent.

  + *Pass from homogeneous elements to the irrelevant ideal.* Each element of $S_+$ is a finite sum of such elements, and a finite
    sum of commuting nilpotents is nilpotent. This proves the assertion
    for all elements of $S_+$. The argument chooses an exponent for each
    element individually and imposes no finite generation on $S_+$.
]

#metadata(none) <sup-pj-2>
#proposition(number: "PJ-2", title: "Domain of a graded map")[
  - A degree-preserving homomorphism $phi:S->T$ induces a morphism
    $U=ops.proj T minus V(phi(S_+)T)->ops.proj S$ by homogeneous-prime
    contraction and the degree-zero localization maps.

  - This morphism is defined on all of $ops.proj T$ if and only if
    $T_+ subset.eq sqrt(phi(S_+)T)$.
]

#proof[
  #set enum(numbering: "1.")

  + *Determine the domain by prime contraction.* For a homogeneous prime $idl.q$ of $T$, its contraction is homogeneous
    and prime. It belongs to $ops.proj S$ precisely when some homogeneous
    $f in S_+$ has $phi(f) in.not idl.q$. Thus the domain is the union of
    $D_+(phi(f))$ over these $f$, which is the stated $U$.

  + *Construct and glue the chart morphisms.* On this open, the map to $D_+(f)$ is induced by
    $(S_f)_0->(T_(phi(f)))_0$, $a/f^m mapsto phi(a)/phi(f)^m$.
    The fraction formulas commute with further homogeneous localization;
    on pairwise intersections they therefore agree. XL glues them to a
    morphism with the stated map on points.

  + *Test when the domain is all of Proj.* The excluded locus is the underlying Proj of the homogeneous quotient
    $T\/phi(S_+)T$, by homogeneous-prime correspondence for a quotient.
    Applying PJ-1 to this quotient shows that it is empty exactly when
    every element of $T_+$ has some power in $phi(S_+)T$.
]

#example(number: "PJ-E1", title: "A graded map with empty domain on Proj")[
  For $k[x_0,x_1]->k[t]$ sending both $x_i$ to zero, the target Proj of
  the ring map, $ops.proj k[t]$, is nonempty but $U$ is empty.
]

#proof[
  Here $phi(S_+)T=0$, so its vanishing locus is all of $ops.proj k[t]$.
  This Proj contains the homogeneous prime $(0)$, which does not contain
  $t$. In fact, its single standard chart is $ops.spec k$. Thus the
  source of the proposed Proj morphism is nonempty while its domain is empty.
]

#metadata(none) <sup-pj-3>
#proposition(number: "PJ-3", title: "High-degree invariance")[
  If a graded map $S->T$ is an isomorphism in every sufficiently high
  degree, the domain in PJ-2 is all of $ops.proj T$ and its induced morphism
  is an isomorphism. This is the comparison of II.2.14(c), with the graded
  map, not just degreewise abstract isomorphisms, specified.
]

#proof[
  #set enum(numbering: "1.")

  + *Verify that the morphism is defined everywhere.* Choose $N$ such that $S_n->T_n$ is an isomorphism for all $n>=N$.
    Each homogeneous $t in T_e$, $e>0$, has a sufficiently high power in
    the image of $S_+$; PJ-2 gives the whole domain.

  + *Reduce to the standard affine charts.* Cover $ops.proj S$ by $D_+(f)$ with $f$ homogeneous of positive degree.
    On the inverse image of such a chart, the ring map is
    $(S_f)_0->(T_(phi(f)))_0$.

  + *Prove surjectivity on each chart.* For surjectivity, represent an element as $b/phi(f)^m$ and multiply
    numerator and denominator by a sufficiently high power of $phi(f)$.
    Its numerator then lies in a degree where $phi$ is surjective.

  + *Prove injectivity on each chart.* For injectivity, if $a/f^m$ maps to zero, then
    $phi(f)^l phi(a)=0$ for some $l$. Increase $l$ until
    $f^l a$ has degree at least $N$; injectivity in that degree gives
    $f^l a=0$. Thus the fraction was zero.

  + *Glue the inverse morphisms.* The chart maps are isomorphisms,
    and their inverses agree on overlaps because they invert the same
    canonical localization maps. They glue to an inverse of the Proj morphism.
]

#metadata(none) <sup-pj-4>
#proposition(number: "PJ-4", title: "Homogeneous quotients")[
  - A surjective graded map $S->S\/I$ gives a closed immersion
    $ops.proj(S\/I)->ops.proj S$.

  - Its ideal on $D_+(f)$ is the degree-zero
    part of the localized ideal $I_f$, under the affine quotient identification
    of #book-link(<sup-cs-1>)[CS-1].

  - For any nonnegative cutoff $n$, replacing
    $I$ by its high-degree ideal $bigOPlus(I_d, d>=n)$ gives the same closed
    subscheme (II.3.12).

  - Its geometric structure depends on the ideal sheaf,
    not just on the underlying closed subset.
]

#proof[
  #set enum(numbering: "1.")

  + *Verify that the morphism is defined everywhere.* The image of $S_+$ generates the irrelevant ideal of $S\/I$, so PJ-2
    gives a morphism everywhere.

  + *Identify the affine quotient charts.* On $D_+(f)$, its ring map is the surjection
    $(S_f)_0->((S\/I)_(bar(f)))_0$ with kernel $(I_f)_0$.
    Indeed, localization is exact, and taking degree zero of an exact
    sequence of graded modules is exact. CS-1 identifies this chart map
    with the closed immersion defined by that kernel. The target-local
    criterion for closed immersions in LP now proves the global assertion.

  + *Compare the truncated ideal.* Write $J=bigOPlus(I_d, d>=n)$. Every homogeneous fraction from $I_f$
    can have numerator degree raised beyond $n$ by multiplying numerator
    and denominator by a power of $f$. Consequently, $(J_f)_0=(I_f)_0$
    on every standard chart. These are equal as submodules of $(S_f)_0$,
    not merely isomorphic modules, so the ideal sheaves and their closed
    subschemes are equal by CS-1.
]

#metadata(none) <sup-pj-5>
#proposition(number: "PJ-5", title: "Graded sections and high degrees")[
  Let $S$ be a nonnegatively graded ring generated by finitely many
  degree-one elements over $S_0$, let $X=ops.proj S$, and let $M$ be a
  graded $S$-module.

  - The canonical graded map $alpha:M->Gamma_*(tildeOf(M))$ sends a
    homogeneous element to the section represented by it on each standard
    chart, with the corresponding twist.

  - If $S$ is Noetherian and $M$ is finite, then there is an integer $n_0$
    such that $alpha_n$ is an isomorphism for every $n>=n_0$.

  - The canonical sheaf comparison
    $tildeOf(Gamma_*(tildeOf(M)))->tildeOf(M)$ is an isomorphism by
    #book-link(<text-ii-5>)[II.5, Proposition 5.15].

  - If $S$ is Noetherian and $M$ is finite, then $tildeOf(M)=0$ if and
    only if there is an integer $n_0$ such that $M_n=0$ for every $n>=n_0$.

  - For every $shf.o_X$-module $shf.f$, II.5.3\* gives the natural adjunction
    $ops.hom(tildeOf(M), shf.f, over: shf.o_X) simeq
    ops.hom(M, Gamma_*shf.f, over: S)$,
    where module maps on the right preserve degree.
]

#proof[
  #set enum(numbering: "1.")

  + *Construct the canonical graded map.* Write $x_0,dots,x_r$ for the degree-one generators. On
    $U_i=D_+(x_i)$, the twist $shf.o (n)$ is trivialized by $x_i^n$ and
    $tildeOf(M)(n)$ corresponds to $(M_(x_i))_n$. A homogeneous
    $m in M_n$ therefore gives the local fraction $m/1$ in this module.
    These fractions agree on the overlaps, defining the canonical map.

  + *Prove eventual exactness of the localization complex.* Here is the precise graded-algebra computation needed for its eventual
    bijectivity. For a finite graded module $M$ over a Noetherian standard
    graded ring, the augmented localization complex
    $M -> product_i M_(x_i) -> product_(i<j) M_(x_i x_j) -> dots$
    is exact at its first two terms in all sufficiently high degrees.
    To see this, regard $M$ as a finite module over
    $P=S_0[X_0,dots,X_r]$ and take a graded free resolution through
    $r+2$ terms, with each term a finite sum of shifts of $P$; the
    Noetherian hypothesis makes the successive kernels finite.
    For $P$, decomposing the localization complex by Laurent monomials
    shows that its only possible cohomology is the last term, represented
    by monomials with every exponent negative. It thus vanishes in high
    degrees, also for each of the finitely many shifts. The long exact
    sequences of these complexes shift the first two cohomology groups
    past the length of the complex, proving the asserted eventual
    exactness for $M$.

  + *Identify the high-degree sections.* The sheaf gluing axiom identifies the kernel of the second arrow in
    degree $n$ with $Gamma(X, tildeOf(M)(n))$, because the $U_i$ cover $X$
    and their pairwise intersections are $D_+(x_i x_j)$.
    This proves the high-degree comparison.

  + *Characterize the zero associated sheaf.* For the zero-sheaf assertion, triviality of $shf.o (1)$ on $U_i$ implies
    that $tildeOf(M)=0$ exactly when all graded localizations $M_(x_i)$
    vanish. Choose finitely many homogeneous generators of $M$. If the
    localizations vanish, powers of each $x_i$ kill all these generators.
    The elementary monomial bound then gives $S_+^q M=0$ for some $q$,
    so all sufficiently high degree pieces vanish. Conversely, eventual
    vanishing kills every homogeneous element after enough multiplication
    by $x_i$, and hence gives zero localizations.

  + *Construct the adjunction and reconstruction maps.* Finally, a degree-preserving map $M->Gamma_*shf.f$ defines on $U_i$
    a map $tildeOf(M)->shf.f$: send a degree-zero fraction $m/x_i^n$
    to the section assigned to $m$, divided by the invertible trivializing
    section $x_i^n$. For negative $n$, first raise numerator degree by
    multiplication by $x_i$. The graded module identities make this
    independent of the fraction representation. On overlaps, the same
    division formula proves agreement. Conversely, twist a sheaf map and
    apply it to the canonical sections of every degree. These constructions
    are inverse on each $U_i$, and hence globally, and are natural.
    The reconstruction statement is exactly II.5.15, whose comparison on
    $U_i$ uses this same fraction formula.
]

#metadata(none) <sup-pj-6>
#definition(number: "PJ-6", title: "Saturation")[
  Let $S=A[x_0,dots,x_r]$ with $A$ Noetherian. For a homogeneous ideal $I$,
  define $I^op("sat")={s in S:S_+^n s subset.eq I " for some " n>=0}$.
]

#proposition(number: "PJ-6.1", title: "Saturation and ideal sheaves")[
  - The ideals $I$ and $I^op("sat")$ give the same ideal sheaf.

  - Homogeneous ideals define the same closed subscheme exactly when their
    saturations agree.

  - Saturated homogeneous ideals correspond to the
    quasi-coherent ideal sheaves of closed subschemes of $ops.proj S$.

  - For $I=(x_0)$ and $J=(x_0^2,x_0 x_1)$ in $k[x_0,x_1]$,
    $I!=J$ but $I^op("sat")=J^op("sat")=(x_0)$.
]

#proof[
  #set enum(numbering: "1.")

  + *Test saturation by localization.* For homogeneous $s$, membership in $I^op("sat")$ is equivalent to
    membership of $s/1$ in $I S_(x_i)$ for every $i$.
    One direction follows since $x_i$ is invertible there. Conversely, choose
    $n_i$ with $x_i^(n_i)s in I$. Taking all $n_i$ positive, every
    monomial of degree $1+sum_i(n_i-1)$ has an exponent at least $n_i$
    for some $i$, so this power of $S_+$ sends $s$ into $I$.

  + *Compare ideal sheaves and saturations.* For $s$ of degree $e$, its membership can equally be tested by
    $s/x_i^e$ in $(I S_(x_i))_0$. Thus equality of ideal sheaves is
    equivalent to equality of saturated ideals, degree by degree.
    Applying the same criterion twice proves idempotence of saturation.

  + *Recover every closed-subscheme ideal sheaf.* For completeness, an ideal sheaf $shf.j subset.eq shf.o_X$ yields the
    homogeneous ideal whose degree $n>=0$ part consists of those
    $s in S_n$ whose canonical section belongs to $shf.j (n)$.
    It recovers $shf.j$ on every $U_i$. Indeed, for a section of $shf.j$
    on $U_i$, clearing powers of $x_i$ in a finite affine cover and then
    clearing the differences on the pairwise intersections extends it to
    a section of $shf.j (n)$ for some $n$. This is the extension argument
    of II.5.14 used in II.5.15. Increasing $n$ further makes its image in
    $Gamma(X, shf.o (n))$ come from $S_n$ by PJ-5.
    Dividing by $x_i^n$ recovers the original section. Hence the resulting
    ideal sheaf is $shf.j$. Saturating the ideal makes this correspondence
    unique by the preceding criterion.

  + *Compute the example.* In the example, $J=x_0(x_0,x_1)$, so $x_0$ belongs to its saturation.
    The ideal $(x_0)$ is saturated: if $S_+^n s subset.eq (x_0)$,
    reduce $x_1^n s$ modulo $x_0$ in the domain $k[x_1]$ to get
    $s in (x_0)$. Since $J subset.eq (x_0)$ this proves the claimed
    equality of saturations. Their degree-one parts show $I!=J$.
]

#metadata(none) <sup-pj-7>
#proposition(number: "PJ-7", title: "Veronese")[
  - For standard graded $S$ and $d>0$, put
    $S^((d))=bigOPlus(S_(n d), n>=0)$, with $S_(n d)$ placed in degree $n$.

  - There is a canonical isomorphism $ops.proj S^((d)) simeq ops.proj S$,
    under which $shf.o_(ops.proj S^((d)))(1)$ corresponds to
    $shf.o_(ops.proj S)(d)$.

  - For $S=k[x_0,x_1]$, its monomials of degree
    $d$ give the rational normal curve and the $d$-uple embedding of
    $sch.p^1_k$ (II.5.13).
]

#proof[
  #set enum(numbering: "1.")

  + *Choose corresponding affine covers.* Choose degree-one generators $x_i$ of $S$. The charts $D_+(x_i)$
    cover $ops.proj S$, and the charts $D_+(x_i^d)$ cover
    $ops.proj S^((d))$: every degree-$d$ monomial has a power divisible
    by some $x_i^d$, so these elements generate the irrelevant ideal up
    to radical.

  + *Identify and glue the localization rings.* Their degree-zero localization rings identify canonically.
    Explicitly multiply numerator and denominator of $a/x_i^m$ by
    $x_i^l$ so that $m+l$ is divisible by $d$. This represents it in
    $(S^((d))_(x_i^d))_0$, and equality is tested by the same localization
    relation. These identifications commute with localization on overlaps
    and glue by XL.

  + *Compare the twists.* The generator of the degree-one twist on the $i$th Veronese chart is
    $x_i^d$; its transition ratios are $(x_j/x_i)^d$. These are precisely
    the transition ratios for $shf.o (d)$, proving the sheaf comparison.

  + *Identify the rational normal curve.* For $k[x_0,x_1]$, the Veronese ring is generated in degree one by
    $x_0^d,x_0^(d-1)x_1,dots,x_1^d$. The surjection from the polynomial
    ring on these generators gives a closed immersion by PJ-4.
    Its map is $[a:b] mapsto [a^d:a^(d-1)b:dots:b^d]$, the rational
    normal curve and the asserted $d$-uple embedding.
]

#metadata(none) <sup-pj-8>
#proposition(number: "PJ-8", title: "Segre")[
  - For standard graded $A$-algebras $S,T$, let
    $R=bigOPlus(tensor(S_n, T_n, over: A), n>=0)$ with componentwise multiplication.

  - There is a canonical isomorphism
    $ops.proj R simeq fiber(ops.proj S, ops.proj T, base: ops.spec A)$.

  - Under it, $shf.o_(ops.proj R)(1)$ corresponds to
    $tensor(p_1^*shf.o (1), p_2^*shf.o (1))$.

  - For two polynomial rings in two variables over $k$, this gives the quadric
    embedding of $sch.p^1_k times_k sch.p^1_k$ in $sch.p^3_k$ with equation
    $z_(0 0)z_(1 1)-z_(0 1)z_(1 0)=0$ (II.5.11).
]

#proof[
  #set enum(numbering: "1.")

  + *Choose degree-one generators.* Choose degree-one generators $s_i$ and $t_j$. The tensors
    $tensor(s_i, t_j)$
    generate the diagonal graded algebra $R$ in degree one.

  + *Identify and glue the affine charts.* On its chart $D_+(tensor(s_i, t_j))$, the canonical ring comparison is
    $R_((tensor(s_i, t_j))) simeq tensor(S_((s_i)), T_((t_j)), over: A)$,
    where parentheses denote degree-zero localization.
    To define its inverse, take a pure tensor of fractions with denominators
    $s_i^a$ and $t_j^b$ and raise both denominators to a common exponent
    $n>=a,b$. The tensor of their adjusted numerators divided by
    $tensor(s_i, t_j)^n$ has degree zero in $R$.
    The localization relations and tensor bilinearity make this independent
    of the choices; the forward map sends such a fraction to the tensor of
    its two fractions. The two maps are inverse on pure tensors, which
    generate the tensor product. Their formulas commute with further
    localization. MG-1 identifies these spectra with the affine charts
    of the fiber product, and XL glues them to the desired isomorphism.

  + *Compare the twists.* The trivializing generator $tensor(s_i, t_j)$ has transition ratio
    $(s_(i')/s_i)(t_(j')/t_j)$, proving the twist formula.

  + *Compute the quadric equation.* For the two polynomial rings, the four degree-one tensors give the
    homogeneous coordinate map $z_(i j) mapsto tensor(x_i, y_j)$.
    Its kernel is generated by $z_(0 0)z_(1 1)-z_(0 1)z_(1 0)$:
    use this relation to replace every monomial containing both $z_(0 0)$
    and $z_(1 1)$; the remaining monomials have distinct pairs of row
    and column exponent sums, hence linearly independent images.
    This proves the stated quadric equation, including its scheme structure.
]

#metadata(none) <sup-pj-9>
#corollary(number: "PJ-9", title: "Very ampleness and composition")[
  Use the definition of relative very ampleness in
  #book-link(<text-ii-5>)[II.5].

  - If two invertible sheaves on $X$ are very ample
    over a common base $Y$, their tensor product is very ample over $Y$,
    using the product of their immersions followed by Segre.

  - For $X ->^f Y ->^g Z$, if $shf.l$ on $X$ is very ample over $Y$ and
    $shf.m$ on $Y$ is very ample over $Z$, then
    $tensor(shf.l, f^*shf.m)$ is very ample over $Z$.

  - These use immersions into finite-dimensional relative projective spaces;
    when the immersions are closed, the resulting immersion is closed.

  - In particular, compositions, base changes, and products of projective
    morphisms remain projective (II.4.9 and II.5.12).
]

#proof[
  #set enum(numbering: "1.")

  + *Realize the tensor product by Segre.* Let $i:X->sch.p^r_Y$ and $j:X->sch.p^s_Y$ realize the two sheaves.
    The map $(i,j)$ to their product is an immersion: factor it as the
    graph $X->fiber(X, sch.p^s_Y, base: Y)$ followed by the base change of
    $i$. The graph is closed since $sch.p^s_Y$ is separated over $Y$,
    by MG-3, and base change preserves immersions. Compose with the Segre
    closed immersion. Its pullback of $shf.o (1)$ is the tensor product by
    PJ-8, proving the first assertion. If $i$ is closed, both factors are
    closed immersions.

  + *Construct the composite immersion.* For composition, use the immersion $Y->sch.p^s_Z$ realizing $shf.m$.
    Its base change embeds $sch.p^r_Y$ into
    $fiber(sch.p^r_Z, sch.p^s_Z, base: Z)$. Compose the immersion realizing
    $shf.l$ with this map and then Segre. The two projective factors pull
    back $shf.o (1)$ to $shf.l$ and $f^*shf.m$, respectively. This proves
    the formula, and the same factorization consists of closed immersions
    if the original ones are closed.

  + *Deduce stability of projective morphisms.* Base change preserves a factorization
    as a closed immersion into a finite projective space followed by its
    projection. Products use the product of the closed immersions and
    Segre; compositions use the factorization just constructed. These
    establish the three assertions about projective morphisms.
]

#metadata(none) <sup-pj-10>
#proposition(number: "PJ-10", title: "Projective normality")[
  Let $k$ be algebraically closed and $X$ a normal integral closed subscheme
  of $sch.p^r_k$, with homogeneous coordinate ring $S$.

  - Then $S$ is a domain, and
    $S'=bigOPlus(Gamma(X, shf.o_X(n)), n>=0)$ identifies with its integral
    closure in its fraction field.

  - The canonical inclusion $S->S'$ is an
    isomorphism in sufficiently high degrees. Thus a sufficiently high Veronese
    embedding of $X$ is projectively normal.

  - More generally for an integral projective closed subscheme, projective
    normality is equivalent to normality together with surjectivity of
    $Gamma(sch.p^r_k, shf.o (n))->Gamma(X, shf.o_X(n))$ for every $n>=0$.

  - The nonempty connected normal formulation of II.5.14 is integral by
    #book-link(<sup-xp-6>)[XP-6], since these schemes are Noetherian.
]

#proof[
  #set enum(numbering: "1.")

  + *Identify the normal affine coordinate rings.* The homogeneous ideal of an integral closed subscheme is prime, so its
    coordinate ring $S$ is a domain. Discard any coordinate whose image is
    zero, and write $x_i$ for the remaining degree-one coordinates.
    Put $A_i=(S_(x_i))_0$. Normality of $X$, and XP-6, say that each
    $A_i$ is an integrally closed domain. Inside $K=ops.frac S$ one has
    $S_(x_i)=A_i[x_i,x_i^(-1)]$, with $x_i$ transcendental over $A_i$;
    uniqueness follows by comparing homogeneous degrees.

  + *Describe the section ring as an intersection.* Sheaf gluing on these charts identifies
    $S'=inter_i A_i[x_i] subset K$.
    Indeed, its degree-$n$ part consists exactly of the fractions regular
    as sections of $shf.o_X(n)$ on every chart; intersection with these
    polynomial rings excludes all negative degrees.
    Each $A_i[x_i]$ is integrally closed with fraction field $K$.
    Hence their intersection is integrally closed and contains every element
    of $K$ integral over $S$.

  + *Identify the integral closure.* PJ-5 applied to $M=S$ identifies $S_n$ with $S'_n$ for $n>=N$.
    Each remaining $S'_n$ is finite dimensional over $k$ by II.5.19.
    Consequently, $S'$ is a finite $S$-module: add bases for the finitely
    many low-degree pieces to the element $1$ as module generators.
    A module-finite algebra is integral, so $S'$ is exactly the integral
    closure of $S$ in $K$.

  + *Pass to a high Veronese subring.* Also $S'_0=k$: it is a finite dimensional domain over $k$, hence a
    finite field extension, and $k$ is algebraically closed.
    Choose $d>=max(N, 1)$. Then $S^((d))=(S')^((d))$ in every degree.
    A Veronese subring of a normal graded domain is normal: an element
    of its fraction field integral over it is integral over the original
    ring, lies in that ring by normality, and has only degrees divisible
    by $d$. For the last assertion, write it as a quotient of two sums
    of degrees divisible by $d$ and compare the direct-sum components
    modulo $d$. PJ-7 now proves projective normality of this embedding.

  + *Prove the projective-normality criterion.* Finally, if $S$ is normal, then each $(S_(x_i))_0$ is normal (compare
    degree-zero components of an integral element), and so $X$ is normal.
    The preceding identification gives $S=S'$. Conversely, normality of
    $X$ and surjectivity of every displayed restriction map give $S=S'$
    degree by degree, so $S$ is normal. Here the image of the restriction
    map is exactly $S_n$ by the definition of the homogeneous coordinate
    ideal. This proves the equivalence. XP-6 supplies the last reduction
    from connected normal Noetherian schemes to integral schemes.
]

#metadata(none) <sup-pj-examples>
#example(number: "PJ-E2", title: "Lost low degrees and failure of exactness")[
  - The graded modules $S$ and $S plus.o S\/S_+$ have identical associated
    sheaves: the extra summand is irrelevant torsion.

  - On $sch.p^1_k$, the ideal
    sequence of two distinct points gives in degree zero the diagonal map
    $k->k times k$. Hence $Gamma_*$ does not in general preserve the
    surjectivity of short exact sequences; compare #book-link(<sup-sc-examples>)[SC-E3].
]

#proof[
  #set enum(numbering: "1.")

  + *Remove the irrelevant-torsion summand.* Every positive-degree homogeneous $f$ annihilates $S\/S_+$, so
    localization at $f$ kills this summand. The graded associated-sheaf construction on the standard
    charts therefore gives the same sheaf as for $S$.

  + *Compute the failure of surjectivity on sections.* For the second
    assertion let $Z$ be the union of the two reduced points. The ideal
    sequence is $0->shf.i_Z->shf.o_(sch.p^1_k)->shf.o_Z->0$, with the
    last sheaf understood as its pushforward. The two standard charts of
    $sch.p^1_k$ show $Gamma(sch.p^1_k, shf.o)=k$, since a polynomial in
    $t$ that is also a polynomial in $t^(-1)$ is constant.
    Meanwhile $Gamma(Z, shf.o_Z)=k times k$. Restriction is
    $a mapsto (a,a)$ and misses $(0,1)$. Hence the degree-zero part of
    $Gamma_*$ is not surjective in this short exact sequence.
]
