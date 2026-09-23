#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== XP — Topology and intrinsic properties of schemes <sup-xp>

The definitions of connected, irreducible, reduced, integral, and
(locally) Noetherian schemes, and their initial criteria, remain in
#book-link(<text-ii-3>)[II.3, Propositions 3.1–3.2 and surrounding definitions].

=== Generic points and specialization <sup-xp-generic-points>

#metadata(none) <sup-xp-1>
#proposition(number: "XP-1", title: "Existence and uniqueness")[
  Every nonempty irreducible closed subset of a scheme has a unique generic
  point, without a Noetherian hypothesis. On $ops.spec A$, the generic point
  of $V(idl.p)$ is $idl.p$ for each prime $idl.p$ (II.2.9).
]

#proof[

  + *Find a prime on an affine chart.* Let $C$ be the closed irreducible subset and choose an affine open
    $U=ops.spec A$ meeting it. The nonempty open $C inter U$ of $C$ is
    dense and irreducible. Write it as $V(I)$ in $U$. Irreducibility says
    that $sqrt(I)$ is prime: if $a b in sqrt(I)$, the containment
    $V(I) subset.eq V(a) union V(b)$ forces one of the two containments.

  + *Construct the generic point.* Put $idl.p=sqrt(I)$. The closure of $idl.p$ in $U$ is $V(idl.p)$,
    so its closure in $X$ contains $C inter U$ and is contained in $C$;
    density gives equality with $C$.

  + *Prove uniqueness.* If two points have closure $C$, every open meeting $C$ contains both:
    an open containing a specialization contains its generizations. Choose
    an affine neighborhood of one. In this affine chart, equal closures
    mean equal prime ideals, so the two points coincide.
]

#metadata(none) <sup-xp-2>
#definition(number: "XP-2", title: "Specialization and components")[
  A point $y$ is a specialization of $x$ if $y in overline({x})$; $x$ is
  then a generization of $y$.
]

#metadata(none) <sup-xp-3>
#proposition(number: "XP-3", title: "Specialization in an affine scheme")[
  + For points $x,y in ops.spec A$, $y in overline({x})$ if and only if
    $idl.p_x subset.eq idl.p_y$.

  + Schemes are $cal(T)_0$: distinct points have
    distinct closures.

  + Closed points of an affine scheme are the maximal
    ideals.

  + Its irreducible components correspond to minimal primes, with those
    primes as their generic points.
]

#proof[

  + *Compute specialization on an affine chart.* A closed set $V(I)$ contains $idl.p$ precisely when $I subset.eq idl.p$;
    intersecting these sets gives $overline({idl.p})=V(idl.p)$.
    This proves the specialization criterion.

  + *Separate distinct points by their closures.* If two points of a scheme
    have equal closures, an affine neighborhood of either contains both,
    and the criterion gives both inclusions of their primes. Thus the
    scheme is $cal(T)_0$.

  + *Identify closed points.* The closure is a singleton exactly for a maximal prime.

  + *Identify irreducible components.* By XP-1, every irreducible closed set is $V(idl.p)$, and maximality of
    that closed set is exactly minimality of $idl.p$ among prime ideals.
]

#metadata(none) <sup-xp-4>
#lemma(number: "XP-4", title: "Restriction to opens")[
  + Every nonempty open of an irreducible scheme contains its generic point
    and is irreducible with the same generic point.

  + For any scheme $X$ and
    open $U$, the components of $U$ are exactly the nonempty intersections
    $C inter U$ for components $C$ of $X$. No finiteness of the component set
    is assumed.
]

#proof[

  + *Restrict the generic point.* A nonempty open in an irreducible space is dense and irreducible.
    Since its points specialize from the generic point, it contains that
    point, whose closure in the open is the whole open.

  + *Restrict an irreducible component.* Now let $C$ be a component meeting $U$. If an irreducible closed subset
    of $U$ contains $C inter U$, its closure in $X$ is irreducible and
    contains $C$, hence equals $C$. This proves maximality of $C inter U$.

  + *Recover every component of the open.* Conversely, close a component $D$ of $U$ in $X$ and include that
    irreducible closed set in a maximal one $C$. Such a maximal set exists
    by the maximality principle: the closure of the union of a chain of
    irreducible subsets is irreducible. Then $D subset.eq C inter U$, and
    maximality in $U$ gives equality. This argument uses no finite list of
    components.
]

#metadata(none) <sup-xp-5>
#proposition(number: "XP-5", title: "Function fields")[
  + For an integral scheme $X$ with generic point $eta$, there are canonical
    identifications $K(X)=shf.o_(X,eta)=kappa(eta)$ and
    $ops.frac(A) simeq K(X)$ for every nonempty affine open $ops.spec A$.

  + Restriction to the generic stalk embeds $Gamma(U, shf.o_X)$ into $K(X)$
    for every nonempty open $U$.

  + These are the function-field identifications
    of II.3.6; a generic local ring on a nonintegral scheme need not be a field.
]

#proof[

  + *Identify the generic local ring.* On a nonempty affine open $ops.spec A$, integrality makes $A$ a domain
    and identifies $eta$ with $(0)$. Proposition 5.1's stalk formula for the
    structure sheaf gives $shf.o_(X,eta)=A_((0))=ops.frac(A)$; its maximal
    ideal is zero, so it equals its residue field. These identifications
    use the same germ map and consequently agree on smaller affine opens.
    They give the claimed canonical identifications with $K(X)$.

  + *Embed sections into the function field.* For $s in Gamma(U, shf.o_X)$ with zero generic germ, restrict to every
    affine open $V=ops.spec B subset.eq U$. The map $B->ops.frac(B)$ is
    injective, so $s|_V=0$. These affines cover $U$, and SL-1 gives $s=0$.
]

#metadata(none) <sup-xp-6>
#proposition(number: "XP-6", title: "Dominance")[
  + For integral schemes $X,Y$, a morphism $f:X->Y$ is dominant if and only
    if $f(eta_X)=eta_Y$; its local map gives an inclusion $K(Y)->K(X)$.

  + For a ring map $phi:A->B$ inducing $f:ops.spec B->ops.spec A$,
    $f$ is dominant if and only if $ops.ker(phi) subset.eq sqrt((0))$.
    Here $sqrt((0))$ is the nilradical of $A$.

  + If $A$ is reduced, then $f$ is dominant if and only if $phi$ is injective.

  + The quotient $A->A_(red)$ is dominant
    on spectra but is not injective when $A$ has a nonzero nilpotent.

  (Ex. II.3.7)
]

#proof[

  + *Test dominance at generic points.* Continuity gives $f(X) subset.eq overline({f(eta_X)})$; since the
    right side is closed and contains a point of $f(X)$, the two closures
    coincide. XP-1 now proves the dominance criterion. The local map
    at the generic points is a map of fields and is therefore injective.

  + *Compute the closure of an affine image.* For a ring map $u:A->B$, the primes containing every contraction from
    $ops.spec B$ form $V(u^(-1)(sqrt((0))))=V(ops.ker(u))$:
    $u(a)$ is nilpotent if and only if some power of $a$ belongs to the kernel.
    This is the closure of the image, by the formula for closed sets in a
    spectrum. It is the whole spectrum if and only if the kernel lies in
    the intersection of all primes, the nilradical. Reducedness then makes
    this equivalent to a zero kernel. Applying this to the nilradical
    quotient gives the last example.
]

#metadata(none) <sup-xp-7>
#remark(number: "XP-7", title: "Noetherian and closed-point phenomena")[
  + A Noetherian scheme has a Noetherian underlying space and unique generic
    points for nonempty irreducible closed subsets; in the terminology of
    II.3.17 it is a Zariski space.

  + A scheme locally of finite type over a field
    has closed points dense in every closed subset.

  + For a scheme of finite
    type over a field, closed points have residue fields finite over that field.
    Over an algebraically closed field, these residue fields equal the base.

  + Neither Noetherianity nor density of closed points is needed for XP-1.
]

#proof[

  + *Prove Noetherianity of the underlying space.* A finite cover by spectra of Noetherian rings gives a finite cover by
    Noetherian spaces: ascending chains of opens stabilize on each member,
    hence simultaneously. Generic points are supplied by XP-1.

  + *Apply the Nullstellensatz.* For the closed-point assertion, use the algebraic form of the
    Nullstellensatz: a finitely generated algebra over a field is Jacobson,
    and its maximal-ideal residue fields are finite over that field.
    These are algebraic inputs left to the reader (Check!).

  + *Find a point with finite residue field.* Given a
    nonempty relatively open part of a closed subset, choose an affine
    finite-type chart and then a principal open inside that part. A maximal
    ideal of its quotient coordinate ring gives a point with finite residue
    field.

  + *Prove global closedness and density.* This point is closed in the entire scheme: in any finite-type
    affine neighborhood of a specialization its prime has quotient embedded
    in that finite field, hence that quotient is a finite-dimensional domain
    over the base field and is a field. The specialization must therefore
    equal the point. This proves the density assertion even when only local
    finite type is assumed.

  + *Identify residue fields over an algebraically closed base.* Over an algebraically closed field a finite
    field extension is the field itself.
]

#metadata(none) <sup-xp-8>
#proposition(number: "XP-8", title: "Clopen sets and idempotents")[
  + Global idempotents $e in Gamma(X, shf.o_X)$ correspond to clopen subsets
    by $e mapsto X_e$, with $e$ equal to $1$ on $X_e$ and $0$ on its
    complement.

  + On $ops.spec A$, a nontrivial decomposition is equivalent to
    $A simeq A_1 times A_2$ with both factors nonzero, or to orthogonal
    nonzero idempotents $e_1+e_2=1$. The factors are $A e_1,A e_2$ with
    identities $e_1,e_2$.

  (II.2.19)
]

#proof[

  + *Construct a clopen set from an idempotent.* In a local ring, $e(1-e)=0$ implies $e=0$ or $e=1$, since one of
    $e,1-e$ is a unit (Check!). For a global idempotent, the loci of these two germ
    equalities are open, disjoint, and exhaustive. They therefore form a
    clopen decomposition, and SL-1 identifies the restrictions with $1,0$.

  + *Glue an idempotent from a clopen decomposition.* Conversely, those two constant sections glue uniquely on a clopen
    decomposition, and their glued section is idempotent. These operations
    are inverse.

  + *Identify the affine product decomposition.* In an affine ring, the maps $a mapsto (a e,a(1-e))$ and
    $(b,c) mapsto b+c$ are inverse ring homomorphisms between $A$
    and $A e times A(1-e)$, with the indicated factor identities.
    Neither factor vanishes precisely for a nontrivial decomposition.
]

#metadata(none) <sup-xp-9>
#proposition(number: "XP-9", title: "Reduction")[
  + A scheme $X$ is reduced if and only if every local ring $shf.o_(X,x)$
    is reduced; equivalently, every ring $shf.o_X (U)$ has no nonzero nilpotents.
  + Let $cal(N)$ be the sheaf of locally nilpotent sections of $shf.o_X$.
    Then $X_(red)=(X,shf.o_X\/cal(N))$ is a reduced scheme, and the quotient
    map defines a closed immersion $i:X_(red)->X$ that is a homeomorphism
    on underlying spaces. Its structure sheaf is the sheafification of
    $U mapsto shf.o_X (U)_(red)$.
  + Every morphism from a reduced scheme $T$ to $X$ factors uniquely
    through $i:X_(red)->X$.

  A common nilpotence exponent on an arbitrary open is not required.
  Reduced induced structures on other closed subsets are treated in CS-4.
  (Ex. II.2.3)
]

#proof[
  + *Compare reduced sections and reduced stalks.*

    + *Pass from stalks to sections.* Suppose first that every $shf.o_(X,x)$ is reduced.  If
      $s in shf.o_X (U)$ is nilpotent, then every germ $s_x$ is nilpotent and
      hence zero.  A section whose germs are all zero is zero, so
      $shf.o_X (U)$ is reduced.

    + *Pass from sections to stalks.* Conversely, assume every $shf.o_X (U)$ is reduced.  Let a germ
      $a in shf.o_(X,x)$ be nilpotent.  Represent it by
      $s in shf.o_X (U)$.  The equality $a^n=0$ means that after shrinking to
      some neighborhood $V$ of $x$, one has $(s|_V)^n=0$.  Reducedness of
      $shf.o_X (V)$ gives $s|_V=0$, hence $a=0$.  Thus every local ring is
      reduced.

  + *Construct the reduction.*

    + *Form the nilradical quotient sheaf.* Let $cal(N)$ be the sheafification of the ideal presheaf
      $U mapsto sqrt((0)) subset.eq shf.o_X(U)$.  Its inclusion into
      $shf.o_X$ is injective by SC-4.  Thus $cal(N)(U)$ consists
      of locally nilpotent sections; a uniform nilpotence exponent on an
      arbitrary open $U$ is not required.  Define
      $
        X_(red)=(X,shf.o_X\/cal(N)).
      $
      Equivalently, this quotient sheaf is the sheafification of
      $U mapsto shf.o_X (U)_(red)$.

    + *Identify its affine charts.* On an affine open
      $V=ops.spec A$, its restriction is the structure sheaf of
      $ops.spec(A\/sqrt((0)))$.  To see this, on every $D(a) subset.eq V$
      a locally nilpotent section is nilpotent because $D(a)$ is
      quasi-compact: choose a finite cover with nilpotence exponents and take
      their maximum.  The nilradical of $A_a$ is $sqrt((0))A_a$, and
      $A_a\/sqrt((0))A_a simeq (A\/sqrt((0)))_(bar(a))$. These nilradical
      and quotient-localization identities are algebraic checks (Check!). Localization
      commutes with these quotient maps, so these identifications respect all
      restrictions on the distinguished basis.  They identify the quotient
      sheaf with the indicated affine structure sheaf.  Hence these affine reductions
      glue and make $X_(red)$ a scheme.  The quotient maps define a closed immersion
      $i:X_(red)->X$.

    + *Compare the underlying spaces.* Every prime ideal of $A$ contains $sqrt((0))$, so contraction gives a
      homeomorphism
      $ops.spec(A\/sqrt((0))) simeq ops.spec A$.  These local homeomorphisms
      agree, and therefore $i$ is a homeomorphism on underlying spaces.

    + *Verify reducedness.* Finally, $A\/sqrt((0))$ is reduced on every affine chart, so part (a)
      shows that $X_(red)$ is reduced.

  + *Prove the reduced-source universal property.*

    + *Factor the structure-sheaf map.* Let $f:X->Y$ with $X$ reduced.  Nilpotent local sections of $shf.o_Y$
      pull back to nilpotent sections of $shf.o_X$, hence to zero.  Thus
      $f^sharp$ kills the nilradical ideal sheaf of $Y$ and factors through
      $shf.o_Y\/cal(N)_Y$.  This gives a morphism
      $tilde(f):X->Y_(red)$ with $i compose tilde(f)=f$.

    + *Check locality on stalks.* At $x in X$,
      the induced map is the factor of the local homomorphism
      $shf.o_(Y,f(x))->shf.o_(X,x)$ through its nilradical quotient.  It is
      local because the maximal ideal of that quotient is the image of the
      original maximal ideal.  Thus this is a morphism of locally ringed
      spaces.

    + *Prove uniqueness.* The underlying map is forced by the homeomorphism $i$, and
      the sheaf map is forced by the epimorphism to the quotient, proving
      uniqueness.

]

#metadata(none) <sup-xp-10>
#lemma(number: "XP-10", title: "Quasi-compactness and Noetherian induction")[
  + Every affine scheme is quasi-compact.

  + A topological space is Noetherian
    if and only if every open is quasi-compact.

  + A locally Noetherian scheme is
    Noetherian if and only if it is quasi-compact.

  + On a Noetherian space,
    Noetherian induction proves a property for all closed subsets if, for each
    closed subset, its validity on every proper closed subset implies its
    validity there. This includes the empty subset as the initial case
    (II.2.13 and II.3.16).
]

#proof[

  + *Prove affine quasi-compactness.* Refine an open cover of $ops.spec A$ by distinguished opens $D(a_i)$.
    Their covering condition says that the ideal generated by all $a_i$ is
    the unit ideal (Check! a proper ideal lies in a maximal ideal).
    An expression for $1$ uses finitely many generators,
    giving a finite subcover.

  + *Characterize Noetherian spaces.* In a Noetherian space, the finite unions from
    any open cover of an open subset have a maximal member, which must be
    that subset. Conversely, if every open is quasi-compact, the union of
    an ascending chain of opens is covered by finitely many members and
    the chain stabilizes.

  + *Characterize Noetherian schemes.* A quasi-compact locally Noetherian scheme has a
    finite cover by Noetherian affine charts; the converse follows from
    that finite cover and affine quasi-compactness.

  + *Apply Noetherian induction.* If induction failed, the descending chain condition on closed subsets
    would give a minimal closed counterexample. All its proper closed
    subsets satisfy the property, so the induction hypothesis rules out
    this counterexample, including the possibility that it is empty.
]

#metadata(none) <sup-xp-11>
#definition(number: "XP-11", title: "Quasi-separatedness")[
  Let $Delta_X:X->fiber(X, X, base: ops.spec ZZ)$ be the diagonal.
  A scheme $X$ is quasi-separated if $Delta_X$ is quasi-compact.
  The following conditions are equivalent:

  #set enum(spacing: 0.8em)

  + $X$ is quasi-separated.
  + $U inter V$ is quasi-compact for every pair of affine open subsets
    $U,V subset.eq X$.

  Every separated scheme is quasi-separated. The converse fails:
  the doubled affine line has affine overlap and is not separated.
]

#proof[

  + *Compute the inverse images of the diagonal.* Cover $fiber(X, X, base: ops.spec ZZ)$ by products $U times V$ of affine
    opens. These products are affine by MG-1, and the inverse image under
    the diagonal is $U inter V$. The target criterion for quasi-compactness
    in LP gives the equivalence.

  + *Deduce quasi-separatedness from separatedness.* A closed immersion is quasi-compact, so
    separatedness implies the condition.

  + *Check the doubled-line example.* For the doubled line, its two
    standard charts and their overlap $ops.spec k[t,t^(-1)]$ are
    quasi-compact. On the product of the two charts, the diagonal has the
    punctured diagonal as image; its closure contains the pair of origins.
    It is therefore not a closed immersion.
]

#metadata(none) <sup-xp-12>
#proposition(number: "XP-12", title: "Normality")[
  + A scheme $X$ is normal if and only if $shf.o_(X,x)$ is an integrally
    closed domain for every $x in X$.

  + For any open cover $X=union_i U_i$, $X$ is normal if and only if
    $U_i$ is normal for every $i$.

  + For a ring $A$, $ops.spec A$ is normal if and only if $A_idl.p$ is
    an integrally closed domain for every prime ideal $idl.p subset.eq A$.
    If $A$ is a domain, this is also equivalent to $A$ being integrally
    closed in $ops.frac(A)$.

  + Normality does not imply connectedness or irreducibility.

  + If $X$ is nonempty, connected, normal, and Noetherian, then $X$ is integral.
]

#proof[

  + *Check normality on an open cover.* Restricting a scheme to an open preserves its local rings, which proves
    both open restriction and the cover criterion.

  + *Apply the affine localization criterion.* On $ops.spec A$, the
    stalks are $A_idl.p$. For a domain, the algebraic criterion is that
    integral closedness is preserved by localization and that
    $A=inter.big_idl.p A_idl.p$ inside $ops.frac(A)$. Indeed, an element
    integral over $A$ lies in every integrally closed $A_idl.p$, hence in
    $A$. For the intersection formula, if a fraction $z$ is not in $A$,
    the proper ideal ${a:a z in A}$ is contained in a maximal ideal,
    and $z$ is not in that localization.

  + *Prove the connected Noetherian conclusion.* In the Noetherian case, there are finitely many irreducible components.
    No two can meet: in an affine neighborhood of an intersection point,
    their distinct minimal primes remain distinct minimal primes in the
    local ring at that point, contradicting its being a domain. Thus the
    components are disjoint and, being finitely many closed subsets, open.
    Connectedness and nonemptiness force a single component. Normal local
    rings are reduced, so the stalk criterion makes $X$ reduced as well;
    reducedness and irreducibility give integrality.
]

#metadata(none) <sup-xp-13>
#corollary(number: "XP-13", title: "Finite type and Noetherianity")[
  A finite-type scheme over a Noetherian scheme is Noetherian.
  Local finite type supplies Noetherian affine charts by the Hilbert basis
  theorem; quasi-compactness supplies a finite affine cover. The distinction
  between these two hypotheses is part of the finite-type definition and
  #book-link(<sup-lp>)[its locality criteria].
]

#proof[

  + *Obtain Noetherian affine charts.* Choose a finite Noetherian affine cover $V_i=ops.spec A_i$ of the
    target. LP's local finite-type criterion gives an affine cover of
    $f^(-1)(V_i)$ with rings finitely generated over $A_i$; each is
    Noetherian by the Hilbert basis theorem and passage to quotients.

  + *Choose a finite cover.* Quasi-compactness of $f$ makes each inverse image quasi-compact, so
    finitely many such charts suffice for each $i$. They give a finite
    Noetherian affine cover of the source, as required by XP-10.
]

=== Locality of intrinsic properties <sup-xp-locality>

#table(
  columns: (1fr, 1fr, 1fr, 1.5fr),
  inset: 5pt,
  fill: (_, y) => if calc.odd(y) { rgb("EAF2F5") },
  stroke: none,
  table.header([Property], [Open restriction], [Open-cover test], [Stalk / affine test]),
  [Reduced], [Yes], [Yes], [Reduced stalks / reduced rings],
  [Normal], [Yes], [Yes], [Normal local rings / XP-12],
  [Locally Noetherian], [Yes], [Yes], [Noetherian affine rings; Noetherian stalks alone do not suffice],
  [Quasi-compact], [Not in general], [Finite cover by quasi-compact opens], [No stalk test],
  [Irreducible],
  [Nonempty opens],
  [Irreducible nonempty cover members with pairwise nonempty intersections],
  [No stalk test],

  [Connected], [Not in general], [Connected nonempty cover members with connected intersection graph], [No stalk test],
  [Integral],
  [Nonempty opens],
  [Reduced plus the irreducibility condition above],
  [Domains on every nonempty affine open],
)

#metadata(none) <sup-xp-examples>
#metadata(none) <sup-xp-14>
#example(number: "XP-14", title: "Calculations and counterexamples")[
  In $ops.spec(k[x,y]\/(x y))$, the generic primes are $(x)$ and $(y)$,
  with closures the two axes. Only the component $V(y)$ meets $D(x)$;
  only $V(x)$ meets $D(y)$. Deleting the origin gives a disconnected open
  in a connected scheme.
]

#proof[
  A prime containing $x y$ contains $x$ or $y$, giving precisely the two minimal primes. On $D(x)$ the relation forces $y=0$, and on $D(y)$ it forces $x=0$. The two axes are connected and meet at the origin, so their union is connected; deleting that point leaves two disjoint nonempty opens.
]

#metadata(none) <sup-xp-15>
#example(number: "XP-15", title: "Calculations and counterexamples")[
  $ops.spec(k[epsilon]\/(epsilon^2))$ has one point, both closed and
  generic, but its local ring is not a field.
]

#proof[
  Every prime contains $epsilon$, and the quotient by $(epsilon)$ is $k$. Thus there is just one prime. The element $epsilon$ is nonzero with square zero in the local ring, so this ring is not a field.
]

#metadata(none) <sup-xp-16>
#example(number: "XP-16", title: "Calculations and counterexamples")[
  The closed points of $sch.a^1_k$ for algebraically closed $k$ are dense
  and omit its generic point. In contrast, a nonfield DVR has one closed
  point and one generic point, and its closed points are not dense.
]

#proof[
  A nonzero polynomial in one variable has only finitely many roots, whereas an algebraically closed field is infinite. Thus no proper closed subset contains all $k$-points. In a nonfield DVR the only nonzero prime is its maximal ideal, whose singleton is closed and proper.
]

#metadata(none) <sup-xp-17>
#example(number: "XP-17", title: "Calculations and counterexamples")[
  For $k[s]->k[t]$, $s mapsto t^2$, the generic map is $k(s)->k(t)$
  with the same substitution. See #book-link(<sup-mg-3>)[MG-3] for the fibers.
]

#proof[
  The substitution is injective on polynomials, since distinct powers of $s$ become distinct even powers of $t$. It extends uniquely to fractions, giving the claimed generic field inclusion by XP-5.
]

#metadata(none) <sup-xp-disjoint-points>
#metadata(none) <sup-xp-18>
#example(number: "XP-18", title: "Calculations and counterexamples")[
  An infinite disjoint union of copies of $ops.spec k$ is locally
  Noetherian but not quasi-compact. Two copies already have an integral
  affine cover without being connected or irreducible.
]

#proof[
  The components themselves form an open cover with no finite subcover. Each component is a Noetherian affine open. Two components form a disjoint clopen decomposition, which prevents connectedness and irreducibility.
]

#metadata(none) <sup-xp-19>
#example(number: "XP-19", title: "Calculations and counterexamples")[
  The square-zero ring $k plus.o V$, with $V$ infinite-dimensional and
  $V^2=0$, is not Noetherian, though its spectrum has one point.
]

#proof[
  Every prime contains the square-zero ideal $V$ and the quotient is $k$, giving one prime. A generating set for $V$ as an ideal must span it over $k$, since $V$ acts on itself by zero. Thus $V$ is not finitely generated.
]

#metadata(none) <sup-xp-20>
#example(number: "XP-20", title: "Calculations and counterexamples")[
  For $A=product_(n>=0) bb(F)_2$, every local ring is a field but $A$ is
  not Noetherian. Noetherian stalks do not imply local Noetherianity.
]

#proof[

  + *Compute the local rings.* Every element of $A$ is idempotent. In any local ring of $A$, every element is therefore $0$ or $1$, so that ring is a field.

  + *Exhibit failure of Noetherianity.* The ideals of sequences supported in the first $n$ coordinates form a strictly ascending chain.

  + *Exclude local Noetherianity.* If the scheme were locally Noetherian, its affine quasi-compactness would give a finite Noetherian affine cover and force $A$ Noetherian, a contradiction.
]

#metadata(none) <sup-xp-21>
#example(number: "XP-21", title: "Calculations and counterexamples")[
  $ops.spec(k times k)$ is normal and is not integral.
]

#proof[
  Its two local rings are $k$, hence are integrally closed domains, whereas the spectrum has two disjoint nonempty components and the ring has nonzero zero divisors.
]
