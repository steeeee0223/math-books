#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

== AL2 — Associated points and regular sequences <sup-al2>

The algebra in this section supplies the hypotheses needed for divisors,
conormal modules, and blowups. All rings are commutative with identity. A
regular element on a module means an element acting injectively; it need not
be a unit. Every purely algebraic result below is an exercise: *Proof left to
the reader.* The indicated routes identify the assertions that subsequent
geometric arguments use. Nakayama's lemma and localization of finite
presentations are available in #book-link(<sup-al-10>)[AL-10].

=== Associated primes and embedded structure

#metadata(none) <sup-al2-1>
#definition(number: "AL2-1", title: "Associated primes")[
  For an $A$-module $M$, put
  $
    ops.ass(M, over: A)=
    {idl.p in ops.spec A : idl.p=ops.ann (m) text(" for some ") 0!=m in M}.
  $
  A prime in this set is associated to $M$. An associated prime that is not
  minimal in $ops.supp (M)$ is called embedded.
  For a Noetherian scheme, a point is associated if the corresponding prime is
  associated on one, equivalently every, affine neighborhood; AL2-3 justifies
  this independence.
]

#metadata(none) <sup-al2-2>
#proposition(number: "AL2-2", title: "Finiteness and zero divisors")[
  If $A$ is Noetherian and $M$ is finite, then $ops.ass(M, over: A)$ is finite,
  is nonempty when $M!=0$, and its minimal members are precisely the minimal
  elements of $ops.supp (M)=V(ops.ann (M))$. Moreover,
  $
    {a in A : exists m!=0, a m=0}
    = union.big_(idl.p in ops.ass(M, over: A)) idl.p.
  $
  In particular, a local equation $a$ defines an effective Cartier divisor on
  $ops.spec A$ exactly when $a$ avoids $ops.ass(A, over: A)$. The empty divisor is
  allowed, so a unit is also an admissible equation.
]

*Proof left to the reader (commutative algebra).* First maximize the
annihilator of a nonzero element of a given nonzero submodule and show that
it is prime. For finiteness, construct a finite filtration with factors
$A\/idl.p_i$ and use
$ops.ass(M) subset.eq ops.ass(M') union ops.ass(M'')$
for a short exact sequence. To prove the displayed equality, apply the
maximal-annihilator argument to the submodule killed by $a$.

#metadata(none) <sup-al2-3>
#proposition(number: "AL2-3", title: "Localization of associated primes")[
  Let $S$ be a multiplicative subset of a Noetherian ring $A$, and let $M$ be
  finite. Under the prime correspondence for localization,
  $
    ops.ass(S^(-1)M, over: S^(-1)A)
    = {S^(-1)idl.p : idl.p in ops.ass(M, over: A), idl.p inter S=emptyset}.
  $
  In particular,
  $idl.p in ops.ass(M, over: A)$ if and only if the maximal ideal of $A_idl.p$
  is associated to $M_idl.p$.
]

*Proof left to the reader (commutative algebra).* Localize an element with
prime annihilator for one inclusion. For the reverse inclusion, contract
the annihilator prime, choose its finite set of generators, and multiply
the representative in $M$ by one common denominator killing all the
resulting relations. Noetherianity is used when choosing those generators.
The minimal primes of $ops.supp (M)$ are associated: localize at such a
prime and apply the nonempty-associated-prime assertion to the resulting
nonzero module with zero-dimensional support.

#metadata(none) <sup-al2-4>
#example(number: "AL2-4", title: "A section supported at an embedded point")[
  Let $A=k[u,v]\/(u^2,u v)$. Each element has a unique expression
  $p(v)+c u$, with $p in k[v]$ and $c in k$, and multiplication is
  $
    (p(v)+c u)(q(v)+d u)
    =p(v)q(v)+(p(0)d+q(0)c)u.
  $
  The following are calculations to complete:

  + $ops.ann (u)=(u,v)$, whereas $ops.ann (v)=(u)$.
  + $ops.ass(A, over: A)={(u),(u,v)}$. For the reverse containment, distinguish
    $p=0$, $p!=0$ with $p(0)=0$, and $p(0)!=0$ in the displayed normal form.
  + The zero divisors form $(u,v)$, although the only minimal prime is $(u)$.
  + $A_v=k[v,v^(-1)]$ and $ops.ker (A->A_v)=(u)$. In particular $u!=0$,
    $u^2=0$, and the nonzero section $u$ disappears on the dense open $D(v)$.

  *Proof left to the reader (commutative algebra).* The normal form makes all
  four assertions explicit. Geometrically, the underlying space is the affine
  line, but its structure sheaf has an additional section supported at its
  origin. Restriction to an open containing every generic point therefore
  need not be injective. The scheme-level criterion uses every associated
  point, as in the dense-open discussion in #book-link(<sup-lp>)[LP].

  For comparison, in $B=k[x,y]\/(x y)$ one has
  $ops.ass(B, over: B)={(x),(y)}$ and the zero divisors are $(x) union (y)$.
  *Proof left to the reader (commutative algebra).* Embed $B$ in
  $k[x] times k[y]$ as pairs with equal constant term. This reduced ring has
  two components and no embedded associated prime. Reducibility and embedded
  structure are distinct phenomena.
]

#metadata(none) <sup-al2-5>
#proposition(number: "AL2-5", title: "Total quotients and meromorphic frames")[
  Let $A$ be Noetherian, $S=A - union.big_(idl.p in ops.ass(A, over: A))idl.p$,
  and $Q(A)=S^(-1)A$.

  + The map $A->Q(A)$ is injective. The maximal ideals of $Q(A)$ correspond
    to the maximal members, under inclusion, of $ops.ass(A, over: A)$; in
    particular $Q(A)$ is semilocal.
  + Every invertible $Q(A)$-module is free of rank one. Here invertible means
    finite projective and locally of rank one, or equivalently tensor
    invertible.
  + If $P$ is an invertible $A$-module, a basis of $S^(-1)P$ spreads to a basis
    of $P_s$ for some $s in S$.
  + If $A$ has no embedded associated primes, then
    $Q(A) simeq product_(idl.p in op("Min")(A)) A_idl.p$;
    the factors are Artinian local rings. If $A$ is also reduced they are
    the fraction fields of $A\/idl.p$.
]

*Proof left to the reader (commutative algebra).* Use finite prime avoidance
to show that a prime disjoint from $S$ is contained in an associated prime.
For the second assertion, let $J$ be the Jacobson radical of the semilocal
ring. The Chinese remainder theorem chooses one element of $P$ forming a
basis modulo each maximal ideal. Nakayama makes it a generator; localization
at every maximal ideal makes the resulting surjection an isomorphism.
For the third assertion clear the finitely many coefficients and inverse
identities in a finite presentation (AL-10). For the fourth assertion use the
Artinian decomposition of a zero-dimensional Noetherian ring.

#remark(title: "Why embedded points affect meromorphic functions")[
  For AL2-4, $v$ becomes a unit at the generic point but is a zero divisor in
  $A$. Thus it is not a permitted denominator in $Q(A)$. In fact $Q(A)$ is
  $A_(u,v)$, while the map to the generic local ring $A_(u)=k(v)$ kills $u$.
  *Proof left to the reader (commutative algebra).* This is the obstruction to
  replacing meromorphic data by an arbitrary tuple of generic-point values.
]

=== Regular sequences, conormal modules, and equations

#metadata(none) <sup-al2-6>
#definition(number: "AL2-6", title: "Regular sequences and depth")[
  Let $(A,idl.m)$ be Noetherian local and $M$ a finite nonzero module. A sequence
  $f_1,dots,f_r in idl.m$ is $M$-regular if multiplication by $f_i$ is injective
  on $M\/(f_1,dots,f_(i-1))M$ for every $i$. The final quotient is nonzero by
  Nakayama. The depth of $M$ is the maximal length of such a sequence; the
  empty sequence has length zero. The depth of the zero module is not used.
]

#metadata(none) <sup-al2-7>
#proposition(number: "AL2-7", title: "Rules for using depth")[
  With these hypotheses:

  + $0<=op("depth")_A(M)<=dim(ops.supp (M))$;
  + $op("depth")_A(M)=0$ exactly when $idl.m in ops.ass(M, over: A)$;
  + for an $M$-regular $f in idl.m$,
    $op("depth")_(A\/(f))(M\/f M)=op("depth")_A(M)-1$;
  + any permutation of an $M$-regular sequence is $M$-regular;
  + after localization, an $M$-regular sequence remains regular wherever
    every element belongs to the prime and the localized module is nonzero.
]

*Proof left to the reader (commutative algebra).* Use AL2-1 and prime
avoidance for depth zero; use successive quotients and the exchange of two
adjacent regular elements for the depth and permutation assertions. In the
exchange argument finite generation and the local hypothesis are essential:
an intersection of powers of an ideal contained in the maximal ideal is
zero. Localization preserves injections and the quotient modules; the
stated hypotheses exclude a vanishing quotient or a unit in the sequence.

#metadata(none) <sup-al2-8>
#proposition(number: "AL2-8", title: "The conormal and associated graded maps")[
  Let $A$ be a Noetherian ring, let $f_1,dots,f_r$ be an $A$-regular sequence,
  and put $I=(f_1,dots,f_r)$, assumed proper. Then the canonical maps
  $
    (A\/I)^r -> I\/I^2, quad (a_1,dots,a_r) mapsto sum_i a_i overline(f_i),
  $
  and
  $
    op("Sym")_(A\/I)(I\/I^2) -> op("gr")_I A
    := bigOPlus(I^n\/I^(n+1), n>=0)
  $
  are isomorphisms. The second map multiplies representatives. In coordinates
  it is the graded map $(A\/I)[T_1,dots,T_r]->op("gr")_I A$ sending
  $T_i$ to the initial form of $f_i$. Consequently the degree-$n$ component
  is free over $A\/I$ on monomials of total degree $n$ in these initial forms.
]

*Proof left to the reader (commutative algebra).* Prove by induction on the
length and on the degree that a homogeneous relation of degree $n$ among
the monomials in the $f_i$, lying in $I^(n+1)$, has all its coefficients in
$I$. The relation statement uses regularity on successive quotients; it is
not valid for arbitrary generators. Equivalently one may use the Koszul
relations in AL2-9. The special Cohen–Macaulay local case is already part of
Hartshorne II.8.21A; this formulation specifies the canonical maps.

In geometry the degree-one map identifies the conormal module of
$ops.spec (A\/I) subset ops.spec A$. The second map is exactly what changes
the exceptional scheme $ops.proj (op("gr")_I A)$ of a blowup into
$sch.p (I\/I^2)$. The convention is that projectivization parametrizes
invertible quotients.

#metadata(none) <sup-al2-9>
#proposition(number: "AL2-9", title: "The Koszul complex needed here")[
  For $f=(f_1,dots,f_r)$, let $F=A^r$ with basis $e_1,dots,e_r$ and set
  $K_i=Lambda^i F$. Define
  $
    d(e_(j_1) and dots and e_(j_i))
    =sum_(q=1)^i (-1)^(q-1) f_(j_q)
    e_(j_1) and dots and hat(e_(j_q)) and dots and e_(j_i).
  $
  Here the hat means that the factor is omitted. One has $d^2=0$. If $f$ is
  an $A$-regular sequence, the augmented complex
  $
    0 -> K_r -> dots -> K_1 -> K_0=A -> A\/I -> 0
  $
  is exact. In particular, all relations among the $f_i$ are generated by
  $f_i e_j-f_j e_i$.
]

*Proof left to the reader (commutative algebra).* Cancellation in pairs
proves $d^2=0$, including in characteristic two. For exactness, split the
underlying modules for the last basis vector into
$K_i(f_1,dots,f_(r-1)) plus.o K_(i-1)(f_1,dots,f_(r-1))$.
The differential combines the preceding differential and multiplication
by $f_r$. Induction reduces positive-degree exactness to injectivity of
$f_r$ on $A\/(f_1,dots,f_(r-1))$; the remaining cokernel is $A\/I$.
This proof uses complexes and elementary exactness, without derived functors.

#metadata(none) <sup-al2-10>
#example(number: "AL2-10", title: "A regular ideal and a nonregular pair")[
  For $A=k[x,y]$ and $I=(x,y)$, the sequence $x,y$ is regular and
  $
    I\/I^2=k overline(x) plus.o k overline(y), quad
    op("gr")_I A=k[X,Y].
  $
  The Koszul maps are
  $
    0 -> A ->^c A^2 ->^b A -> k -> 0,
    quad c(h)=(-y h,x h), quad b(a,b)=x a+y b.
  $
  Check exactness directly by divisibility in $k[x,y]$. This supplies the
  exceptional $sch.p_k^1$ for the blowup of the origin.

  Now put $J=(x^2,x y)$. Although $x^2$ is regular, $x y$ is a zero divisor
  modulo $(x^2)$: the nonzero class of $x$ kills it. The relation
  $y x^2-x(x y)=0$ gives the nonzero vector $(y,-x)$ in the kernel of
  $(A\/J)^2->J\/J^2$. Thus the displayed generating pair is not a regular
  sequence and does not give a free conormal basis. The relation
  $y T_1-x T_2$ survives as a relation in the associated graded algebra.

  *Proof left to the reader (commutative algebra).* Retain the coefficient
  ring $A\/J$ when checking the last assertion. Counting two equations is
  insufficient: $V(J)$ has the underlying line $x=0$, of codimension one.
]

=== Depth, codimension, and singularities

#metadata(none) <sup-al2-11>
#proposition(number: "AL2-11", title: "Using the local-algebra theorems of II.8")[
  A Noetherian local ring is Cohen–Macaulay if its depth equals its dimension.
  The following are the forms of Hartshorne II.8.21A–8.23 used below.

  + A regular local ring is Cohen–Macaulay; localizations of a
    Cohen–Macaulay local ring are Cohen–Macaulay.
  + In a Cohen–Macaulay local ring $A$, a sequence
    $f_1,dots,f_r in idl.m$ is regular if and only if
    $dim(A\/(f_1,dots,f_r))=dim A-r$.
  + Its quotient is then Cohen–Macaulay of that dimension. In particular,
    a regular local ambient ring modulo a regular sequence has this property.
  + A Noetherian ring is normal if and only if it satisfies $R_1$ and $S_2$:
    its local rings at primes of height at most one are regular, and
    $op("depth") A_idl.p>=min(2, dim A_idl.p)$ for every prime $idl.p$.
]

*Proof left to the reader (commutative algebra; the theorems are stated in
II.8).* The point here is their hypotheses. The implication from the
number of equations to regularity uses a Cohen–Macaulay ambient local
ring and the displayed dimension equality. The condition $S_2$ controls
depth at higher-codimension points; $R_1$ controls codimension-one
singularities. Neither condition replaces the other.

#metadata(none) <sup-al2-12>
#lemma(number: "AL2-12", title: "A regular quotient of a regular local ring")[
  Let $(A,idl.m)$ be a Noetherian regular local ring and $I subset.eq idl.m$
  an ideal such that $A\/I$ is regular local. Put $d=dim A$ and
  $r=d-dim(A\/I)$. There is a regular system of parameters
  $f_1,dots,f_d$ of $A$ such that $I=(f_1,dots,f_r)$.
  In particular, $I$ is generated by an $A$-regular sequence of length $r$,
  and $I\/I^2$ is free of rank $r$ over $A\/I$.
]

*Proof left to the reader (commutative algebra).* Use the map from
$idl.m\/idl.m^2$ to the cotangent space of $A\/I$ to choose $r$ independent
classes represented by elements of $I$, and extend them to a parameter
system of $A$. The quotient by those $r$ elements is regular local and
surjects onto $A\/I$ with the same dimension. Prove that the kernel is zero,
using that a regular local ring is a domain and that a proper nonzero ideal
lowers its dimension. This specifies the algebra needed when both a closed
subscheme and its ambient scheme are regular; smoothness of a morphism is
not one of the hypotheses of this ring statement.

#metadata(none) <sup-al2-13>
#example(number: "AL2-13", title: "The cone and the cusp")[
  Let $k$ be algebraically closed of characteristic zero. The following
  coordinate-ring calculations are *left to the reader (commutative
  algebra)*.

  + For $A=k[x,y,z]\/(x y-z^2)$, the polynomial $x y-z^2$ is irreducible,
    so $A$ is a domain of dimension two. It is a hypersurface in a regular
    ring and hence its local rings are Cohen–Macaulay. Away from
    $idl.m=(x,y,z)$ the opens $D(x)$ and $D(y)$ cover and have rings
    $k[x,x^(-1),z]$ and $k[y,y^(-1),z]$. At the vertex,
    $dim_k idl.m\/idl.m^2=3>dim A_idl.m=2$.
  + For $B=k[t^2,t^3]=k[x,y]\/(y^2-x^3)$, the local ring at $(x,y)$ is
    a one-dimensional Cohen–Macaulay domain, but its cotangent space has
    dimension two. The element $t=y/x$ of its fraction field is integral,
    since $t^2=x$, and does not lie in that local ring. To check the last
    assertion, an equation $t=a/b$ with $a,b in k[t^2,t^3]$ and $b(0)!=0$
    would give a nonzero coefficient of $t$ in $a=t b$, which is impossible.

  The geometric conclusions are as follows. The cone is regular off its
  vertex because the two displayed charts are open subschemes of affine
  planes. All height-one points lie in these charts, whereas the vertex has
  height two. Thus it satisfies $R_1$; its Cohen–Macaulay local rings supply
  $S_2$, so it is normal by AL2-11. It is not regular at the vertex. For the
  cusp, the singular origin has height one. Thus its Cohen–Macaulay property
  does not supply $R_1$, and the explicit integral element confirms failure
  of normality. The checks of dimension and cotangent dimension above
  translate through the affine correspondence, and do not assert smoothness
  over an arbitrary imperfect field.
]

#exercise(title: "Exercises: equations and hidden hypotheses")[
  + In AL2-4 determine the elements that become units in $Q(A)$ and in
    $A_(u)$, and exhibit the difference.
  + Verify every map and kernel in the two-variable Koszul complex of
    AL2-10. Explain where the regularity of the second element is used.
  + Compute $J\/J^2$ for $J=(x^2,x y)$ at the generic point of $V(x)$ and
    at the origin. Determine why its two proposed generators cannot be a
    basis at the origin.
  + At the cone vertex verify that $x,y$ is a regular sequence: the quotient
    by $x$ is $k[y,z]\/(z^2)$ and multiplication by $y$ is injective. Compute
    the length of the final quotient. Compare this depth computation with
    the embedding dimension three.
]

Sources: Hartshorne II.8.21A–8.23; Liu, Sections 7.1.1–7.1.9
(associated points), 7.1.32 (semilocal meromorphic frames), and
8.2.9–8.2.19 (regular sequences and depth). The scheme-level locality
criteria belong to #book-link(<sup-lp>)[LP] and
#book-link(<sup-lp2>)[LP2].
