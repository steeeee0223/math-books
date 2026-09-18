#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion

== PM — Projective morphisms and positivity <sup-pm>

Projective has Hartshorne's meaning: a factorization through a closed
immersion into one finite-dimensional $sch.p_Y^N$. A very ample sheaf
relative to $Y$ is the pullback of $shf.o (1)$ under an immersion into
such a space; the immersion is closed when the morphism to $Y$ is proper.
The locality and stability statements belong to
#book-link(<sup-lp-54>)[LP's projectivity criteria]. This supplement
constructs embeddings from specified positivity data, using the section
extension and generation results of II.5–II.7.

=== From one line bundle to a global embedding

#metadata(none) <sup-pm-1>
#definition(number: "PM-1", title: "Relative ampleness")[
  For a finite-type morphism $f:X->Y$ of Noetherian schemes, an invertible
  sheaf $shf.l$ is $f$-*ample* if $Y$ has an affine open cover $U_i$ on
  which $shf.l|_(f^(-1)U_i)$ is ample. Equivalently, this holds on every
  affine open of $Y$, by #book-link(<sup-lp2>)[LP2's ampleness criteria].
  The same globally defined $shf.l$ is used on every member of the cover.
  This condition does not by itself supply finitely many global sections
  defining a closed immersion $X->sch.p_Y^N$.
]

#metadata(none) <sup-pm-2>
#theorem(number: "PM-2", title: "Global projectivity over a positive base")[
  Suppose $Y$ is Noetherian with an ample invertible sheaf $shf.a$, and
  $f:X->Y$ is proper. The following conditions are equivalent:
  + $f$ is projective in Hartshorne's sense.
  + $X$ has an $f$-ample invertible sheaf.
  + $X$ has an ample invertible sheaf.
  + $X$ is isomorphic over $Y$ to $ops.proj_Y shf.s$ for a
    quasi-coherent graded algebra with $shf.s_0=shf.o_Y$, generated
    by a coherent degree-one part.
]
#proof[
  A projective embedding supplies $shf.l=i^*shf.o (1)$; its restrictions
  over affine opens are ample by II.5.17 and II.7.6. Conversely suppose
  that $shf.l$ is $f$-ample. Choose a positive $e$ and finitely many
  $t_i in Gamma(Y, shf.a^e)$ such that $U_i=Y_(t_i)$ are affine and
  cover $Y$; II.7's affine-section criterion for ampleness permits this.
  By II.7.6, on each $X_i=f^(-1)U_i$ a positive power of $shf.l$ is
  very ample over $U_i$. Replace the finitely many powers by a common
  multiple $n$, using Veronese embeddings. Properness makes these
  immersions closed. Choose finite generating sections $s_(i j)$ of
  $shf.l^n|_(X_i)$ giving these embeddings.

  Apply II.5's section-extension lemma on the Noetherian scheme $X$,
  to the section $f^*t_i$ of $f^*shf.a^e$: after multiplying by a power
  of $f^*t_i$, each $s_(i j)$ extends to a section of
  $shf.l^n times.o f^*shf.a^(e m)$ on $X$. Increase all exponents to one
  common $m$, multiplying an extension by further powers of its own
  $f^*t_i$. On $X_i$ the resulting sections from the $i$-th group still
  generate and still define its original embedding, because the common
  factor is a unit in the frame $t_i^m$. The union of all groups
  therefore generates this single bundle on $X$ and defines
  $h:X->sch.p_Y^N$.

  On $X_i$, project to the coordinates belonging to the $i$-th group;
  these do not vanish simultaneously. In each projective affine chart
  of that group, the original coordinate ring already surjects onto
  the coordinate ring of $X_i$ in its closed embedding. Adding the
  other coordinate ratios preserves surjectivity. Thus $h|_(X_i)$ is
  an immersion. These are the inverse images of the target cover
  $sch.p_(U_i)^N$, so target locality of immersions proves that $h$ is
  an immersion. Its graph is closed since $sch.p_Y^N->Y$ is separated;
  composing the graph with the base change of the proper map $f$
  proves $h$ proper. A proper immersion is a closed immersion. This
  proves projectivity without a pushforward-coherence assertion.

  A projective embedding also gives an ample bundle on $X$. Indeed,
  on $sch.p_Y^N$ the sections $T_j pi^*t_i$ of
  $shf.o (1) times.o pi^*shf.a^e$ have nonvanishing loci
  $D_+(T_j) times_Y U_i$, affine spaces over the affine schemes $U_i$.
  They cover. The affine-section criterion shows that this bundle is
  ample, and its restriction to the closed subscheme $X$ is ample.
  Conversely, an ample bundle on $X$ restricts to every $X_i$, hence
  is $f$-ample.

  Finally take a specified closed immersion $i:X->sch.p_Y^N$. On
  $V=ops.spec A subset Y$, define $J_d(V)$ to be the kernel of the
  restriction map from the degree-$d$ homogeneous polynomials
  $A[T_0,dots,T_N]_d$ to $Gamma(X_V, i^*shf.o (d))$. These specified
  kernels reconstruct the ideal sheaf by PJ and II.5. They commute
  with restriction to $D(a) subset V$: global sections on the
  quasi-compact separated $X_V$ are the equalizer of sections on a
  finite affine cover and its affine intersections; exact localization
  commutes with this finite equalizer. The terminal module-localization
  assertion is left to the reader. Thus the $J_d(V)$ define
  quasi-coherent sheaves and agree on affine refinements of overlaps,
  giving a homogeneous ideal globally. Set its degree-zero component
  to zero while keeping every positive component. This still gives
  an ideal and does not change its associated ideal sheaf: on each
  $D_+(T_j)$ a degree-zero relation is represented by its product
  with $T_j$, divided by $T_j$. The resulting quotient has degree
  zero $shf.o_Y$, is generated in degree one, and has relative Proj
  equal to $X$. This proves the fourth condition. Conversely that
  condition gives a closed immersion into
  $sch.p (shf.s_1)$ by PJ2-2, and PM-3 below puts it inside one
  $sch.p_Y^N$.
]

#metadata(none) <sup-pm-3>
#proposition(number: "PM-3", title: "The purpose of the base twist")[
  Let $shf.e$ be coherent on a Noetherian $Y$ with ample $shf.a$.
  For some $m>=0$ there is a finite surjection
  $shf.o_Y^(N+1)->shf.e times.o shf.a^m$. Consequently
  $sch.p (shf.e)$ embeds as a closed subscheme of $sch.p_Y^N$, with
  hyperplane bundle $shf.o_(sch.p (shf.e))(1) times.o pi^*shf.a^m$.
  The same conclusion holds for every closed subscheme of $sch.p (shf.e)$.
]
#proof[
  Ampleness makes $shf.e times.o shf.a^m$ globally generated for all
  sufficiently large $m$. Coherence and quasi-compactness let us choose
  finitely many generating sections. The resulting surjection of
  symmetric algebras gives a closed immersion on relative Proj by
  PJ2-2. The twisting isomorphism of PJ2-6 identifies its source with
  $sch.p (shf.e)$ and tracks $shf.o (1)$ as displayed. Composing with
  a closed immersion gives the final assertion. Here $m$ is chosen to
  generate a sheaf on the base; it is distinct from the exponent $n$
  in PM-2 that first makes a bundle very ample over affine base opens.
]

#metadata(none) <sup-pm-4>
#proposition(number: "PM-4", title: "A difference of very ample bundles")[
  If $X$ is quasi-projective over a Noetherian affine scheme, every
  invertible $shf.l$ has the form $shf.l_1 times.o shf.l_2^(-1)$ with
  $shf.l_1,shf.l_2$ very ample over that affine scheme.
]
#proof[
  Choose a very ample $shf.h$. It is ample by II.7.6. For sufficiently
  large $n>=0$, the sheaf $shf.l times.o shf.h^n$ is generated by
  finitely many sections. Its morphism to a finite projective space,
  together with the immersion defined by $shf.h$, gives an immersion
  into the product: on the first factor's image this is the graph of
  the second morphism. The second projective space is separated, so
  the graph is closed over that image. Composing with Segre gives an
  immersion whose hyperplane bundle is $shf.l times.o shf.h^(n+1)$.
  Thus take $shf.l_1=shf.l times.o shf.h^(n+1)$ and
  $shf.l_2=shf.h^(n+1)$, the latter very ample by Veronese. This uses
  immersions and remains valid when $X$ is not proper.
]

#metadata(none) <sup-pm-5>
#proposition(number: "PM-5", title: "Finite maps")[
  A finite morphism to a Noetherian scheme possessing an ample
  invertible sheaf is projective in Hartshorne's sense.
]
#proof[
  First take $Y=ops.spec A$ and $X=ops.spec B$, with $B$ finite over $A$.
  Choose algebra generators $b_1,dots,b_r$, each satisfying a monic
  equation of degree $d_i$. Embed $X$ in $sch.a_A^r$, and homogenize
  its full defining ideal to take its scheme-theoretic closure in
  $sch.p_A^r$. At infinity, the homogenized monic equations give
  $T_i^(d_i)=0$ for every $i$ while $T_0=0$. No homogeneous prime of
  Proj can contain all these coordinates, so the part at infinity is
  empty. The closure lies in $D_+(T_0)$, where it is exactly $X$;
  hence $X->sch.p_A^r$ is a closed immersion. The algebraic facts
  about finite algebras being integral and homogenized ideals on the
  affine chart are left to the reader.

  For general $Y$, the preimage of every affine open is affine, so
  $shf.o_X$ is $f$-ample: coherent modules on affine schemes are
  generated by global sections. A finite map is proper by LP. PM-2
  now supplies the global embedding using the ample bundle on $Y$.
  The affine embeddings alone do not provide compatible projective
  coordinates on the whole base.
]

=== Explicit positivity calculations

#metadata(none) <sup-pm-6>
#example(number: "PM-6", title: "The two directions on a quadric surface")[
  On $sch.p^1_k times sch.p^1_k$, put
  $shf.o (a,b)=p_1^*shf.o (a) times.o p_2^*shf.o (b)$.
  Its global sections are bihomogeneous polynomials of bidegree $(a,b)$;
  they are zero if either degree is negative and otherwise have basis
  $X_0^(a-i)X_1^i Y_0^(b-j)Y_1^j$ for $0<=i<=a$, $0<=j<=b$.
  It is globally generated exactly when $a,b>=0$, and ample, equivalently
  very ample, exactly when $a,b>0$.
]
#proof[
  Use the four products of standard affine charts. Their section
  modules are polynomial rings times the frames $X_i^a Y_j^b$;
  agreement on intersections requires the same Laurent polynomial.
  Intersecting these four modules leaves exactly the indicated
  monomials. This Laurent-polynomial intersection is a purely algebraic
  calculation left to the reader. For nonnegative degrees the monomial
  using the nonzero coordinate on each factor generates at every point.
  Restricting to either ruling gives $shf.o (a)$ or $shf.o (b)$ on
  $sch.p^1$, so global generation forces both degrees nonnegative.
  Restriction of an ample bundle to a closed fiber is ample, and
  II.7.6.1 forces both degrees positive. Finally, for positive degrees
  the degree-$a$ and degree-$b$ Veronese embeddings followed by Segre
  have exactly the displayed coordinates and hyperplane bundle
  $shf.o (a,b)$. They give a closed immersion, proving sufficiency.
]

#metadata(none) <sup-pm-7>
#example(number: "PM-7", title: "Relative positivity on a ruled surface")[
  On $F_n=sch.p_(sch.p^1)(shf.o plus.o shf.o (n))$, $n>=0$, the bundle
  $shf.o (1)$ is relatively ample but is not ample on $F_n$.
  For every $m>=1$,
  $shf.l_m=shf.o (1) times.o pi^*shf.o (m)$ is very ample.
]
#proof[
  Over each standard affine base chart, $F_n$ is a projective line
  with its usual $shf.o (1)$, proving relative ampleness. Its restriction
  to the quotient section $shf.o plus.o shf.o (n)->shf.o$ is trivial,
  whereas an ample bundle restricts to an ample bundle on the closed
  section. The trivial bundle on $sch.p^1$ is not ample.

  By PJ2-6, $shf.l_m$ is tautological for
  $shf.o (m) plus.o shf.o (m+n)$. Write quotient coordinates as $[a:b]$
  relative to local frames. All global sections are represented by
  the two blocks
  $
    a T_0^(m-i)T_1^i quad (0<=i<=m), quad
    b T_0^(m+n-j)T_1^j quad (0<=j<=m+n).
  $
  They generate because both summands are generated. To verify the
  resulting map is a closed immersion, use the open $T_0!=0$ of the
  base with coordinate $t=T_1/T_0$. Where $a!=0$, divide by the first
  section $a T_0^m$: the ratios include $t$ (as $m>=1$) and $b/a$
  in the chosen frames. These generate the chart ring $k[t,b/a]$.
  Where $b!=0$, dividing by $b T_0^(m+n)$ yields $t$ and $a/b$.
  Repeating at $T_1!=0$ gives the remaining charts. Thus each of the
  four indicated target standard opens pulls back to precisely the
  corresponding affine source chart and induces a surjective ring map.
  Their union contains the image, so the map is an immersion. The
  surface is proper over $k$ (compose the proper relative Proj map
  with $sch.p^1->ops.spec k$), hence the immersion is closed.
  This verifies separation of points and tangent directions directly
  by coordinate-ring generation, without a numerical ampleness criterion.
]

#metadata(none) <sup-pm-8>
#theorem(number: "PM-8", title: "Finite linear projection")[
  Let $X subset.eq sch.p_k^N$ be an integral projective variety of
  dimension $d$ over an algebraically closed field. There are linear
  forms $l_0,dots,l_d$ whose common center misses $X$ and whose
  projection restricts to a finite surjective morphism
  $X->sch.p_k^d$.
]
#proof[
  Put $R=k[T_0,dots,T_N]/I_X$. Use the following homogeneous
  normalization assertion: a standard graded domain of dimension
  $d+1$ over an infinite field contains algebraically independent
  degree-one elements $l_0,dots,l_d$ such that it is finite over
  $B=k[l_0,dots,l_d]$. This is a purely algebraic theorem; its proof
  by successive avoidance of the finitely many relevant homogeneous
  primes is left to the reader. The dimension comparison
  $dim R=dim X+1$ is the usual affine-cone calculation from Chapter I.

  Finiteness and grading imply that $R/(l_0,dots,l_d)$ vanishes in
  all sufficiently high degrees. Consequently the radical of
  $(l_0,dots,l_d)R$ contains $R_+$, so the center has empty intersection
  with $X$ by PJ-1. The graded inclusion defines a morphism everywhere.
  On $D_+(l_i)$ it is the affine map
  $ops.spec (R_(l_i))_0 -> ops.spec (B_(l_i))_0$.
  Choose homogeneous $B$-module generators $r_j$ of degrees $e_j$;
  the fractions $r_j/l_i^(e_j)$ generate $(R_(l_i))_0$ over
  $(B_(l_i))_0$. This algebraic finite-generation assertion follows by
  taking homogeneous parts and is left to the reader. The affine
  criterion for finiteness in LP therefore proves the map finite.

  Each chart inclusion remains injective: both rings embed in the
  homogeneous fraction field of the domain $R$. It is also integral,
  being finite. Lying over makes the corresponding map on spectra
  surjective; this is the purely algebraic lying-over theorem. The
  charts cover $sch.p^d$, so the global morphism is surjective.
  Its fibers are finite because they are spectra of finite algebras
  over residue fields. Thus finiteness comes from the explicit ring
  extensions, rather than from properness alone.
]

#metadata(none) <sup-pm-9>
#example(number: "PM-9", title: "The image does not determine the modification")[
  The pencil $[x:y:z] mapsto [x:y]$ on $sch.p^2$ has base ideal
  $(x,y)$ and image all of $sch.p^1$, whose homogeneous ideal is zero.
  Its graph closure in $sch.p^2 times sch.p^1$ has equation $x v=y u$.
  This is the blowup at $[0:0:1]$, as computed in
  #book-link(<sup-bu-13>)[BU-13]. The projection to $sch.p^2$ is a
  projective modification, and the other projection is the morphism
  defined by the transformed pencil. Thus the homogeneous equations
  of the image, the base ideal, the graph in a product, and the
  relative embedding of a modification answer distinct questions.
  In particular, the empty list of equations for the image contains
  no information from which to recover the exceptional divisor.
]

#exercise(title: "Exercises on positivity")[
  + In PM-7, write the equations relating adjacent coordinates in the
    two blocks for $n=1,m=1$. Identify the resulting cubic scroll.
  + Show directly that the finite affine construction in PM-5 excludes
    points at infinity even when $A$ has nilpotents.
  + For a smooth plane conic, choose a center outside the conic and
    compute the degree of the finite projection to $sch.p^1$.
]

PM-4 is the second-chapter form of Liu, Proposition 7.1.31; PM-2–PM-3
refine the use of II.7.10. For convention comparisons see
#link("https://stacks.math.columbia.edu/tag/0B44")[Stacks, projective schemes],
where H-projective corresponds to the convention used here.

Related exercise: #book-link(<exercise-ii-7-5>)[II.7.5]. PM-4 applies the very-ample tensor construction; it does not replace all five ampleness assertions.
