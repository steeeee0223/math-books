#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import "../defs.typ": *
#import "proof-layout.typ": proof
#show: show-theorion
#set enum(numbering: "(a)", indent: 1em)

== VS2 — Calculations on varieties <sup-vs2>

Throughout these cases $k$ is algebraically closed of characteristic zero,
except where another field is specified. Each case asks a geometric
question, gives coordinates, connects the calculation to the relevant
theorem, and ends with a variation. Long computations have their single
home in DV, PJ2, BU, DF or PM; the comparisons here explain how to use
them together. Purely algebraic or topological assertions mentioned as
exercises are left to the reader.

=== Divisors, sections and singular points

#metadata(none) <sup-vs2-1>
#example(number: "VS2-1", title: "The projective line")[
  *Question.* How does the equation of a divisor determine sections and
  differentials? #book-link(<sup-dv-14>)[DV-14] computes the frames of
  $shf.o (d[infinity]) simeq shf.o (d)$ and its global sections on the two
  standard charts of $sch.p^1$. Use that calculation as the divisor input.

  *Comparison.* On their overlap $s=t^(-1)$, differentiation gives
  $d t=-s^(-2)d s$ (Check!). Thus the same transition-function method
  gives the canonical divisor $-2[infinity]$. DV-14 supplies the section
  calculation; the new step here compares its line-bundle frames with
  the differential frames. No cohomology computation is needed.

  *Variation.* Over $bb(R)$ the point cut out by $t^2+1$ has degree two.
  After extension to $bb(C)$ it splits into two degree-one points;
  compare DV's residue-field weights rather than counting closed points.
]

#metadata(none) <sup-vs2-2>
#example(number: "VS2-2", title: "Two rulings on a product")[
  *Question.* Which part of a divisor determines a map?
  On $sch.p^1 times sch.p^1$, a bihomogeneous polynomial $F$ of
  bidegree $(a,b)$ is a section of $shf.o (a,b)$. Dividing by the
  chosen homogeneous coordinates to degrees $a,b$ on the four product
  charts gives its local equations, whose ratios are units. Its zero
  divisor therefore has associated line bundle $shf.o (a,b)$ when the
  section is nonzero. For $a,b>=0$, a basis of sections consists of
  $ x_0^(a-i)x_1^i y_0^(b-j)y_1^j, quad 0<=i<=a,quad 0<=j<=b. $
  With a negative index there are no nonzero global sections, by
  restriction to the corresponding ruling fibers and VS2-1.

  *Comparison.* #book-link(<sup-dv-16>)[DV-16] computes the two divisor
  classes and their transitions. #book-link(<sup-pm>)[PM] shows that
  $shf.o (a,b)$ is globally generated exactly for $a,b>=0$, and is
  ample, equivalently very ample in this example, exactly for $a,b>0$.
  The displayed basis defines the Segre–Veronese map in the positive
  case. A single equation $F$ specifies a divisor; its line-bundle
  class specifies all possible sections; a chosen generating system
  specifies a map. These are distinct pieces of data.

  *Variation.* Use $(a,b)=(1,0)$ to identify the map as a projection,
  and locate the ruling which it contracts.
]

#metadata(none) <sup-vs2-3>
#example(number: "VS2-3", title: "Three views of the quadric vertex")[
  *Question.* What fails at the vertex of
  $Q=ops.spec k[x,y,z]\/(x y-z^2)$? For $D=V(x,z)$,
  #book-link(<sup-dv-15>)[DV-15] computes
  $ops.dv(x)=2D$ and $ops.cl Q=ZZ\/2ZZ$, with $D$ non-Cartier at the
  vertex. In #book-link(<sup-df-7>)[DF-7],
  $
    Omega_(Q\/k)=(shf.o_Q d x plus.o shf.o_Q d y plus.o shf.o_Q d z)
    \/ (y d x+x d y-2z d z).
  $
  Tensoring at the vertex makes the relation zero, leaving a
  three-dimensional tangent space although $Q$ has dimension two.

  *Comparison.* The blowup calculation in #book-link(<sup-bu>)[BU]
  gives two smooth charts $(x,a)$ and $(y,b)$ with
  $z=x a$, $y=x a^2$, $b=a^(-1)$ on the overlap.
  The exceptional curve is $sch.p^1$, and its ideal generators transform
  as $y=a^2 x$. Thus its conormal bundle is $shf.o_(sch.p^1)(2)$ and
  its normal bundle is $shf.o_(sch.p^1)(-2)$. These are the explicit
  transition functions, so the sign follows from dualizing the ideal
  modulo its square. The non-Cartier ruling, excess tangent direction,
  and exceptional curve all refer to the same vertex.

  *Variation.* Replace the equation by $x y=z^r$ and compute the
  multiplicity of $V(x,z)$ in $ops.dv(x)$ before attempting a resolution.
]

=== Projective models and birational modifications

#metadata(none) <sup-vs2-4>
#example(number: "VS2-4", title: "A weighted twist that is not a line bundle")[
  *Question.* Does $shf.o (1)$ always name a line bundle? Apply
  #book-link(<sup-pj2-10>)[PJ2-10] to $S=k[x,y,z]$ with degrees $1,1,2$.
  That calculation identifies $ops.proj S$ with the quadric cone, makes
  $shf.o (2)$ its hyperplane bundle, and shows that $shf.o (1)$ is not
  locally free at the vertex.

  *Comparison.* Its chart at the vertex is the singularity of VS2-3.
  Thus the failure of the weighted twist to be invertible and the
  non-Cartier divisor class describe the same local obstruction. The
  Veronese changes the chosen twist while preserving the scheme;
  PJ2-10 contains the module presentation and multiplication-map calculation.

  *Variation.* Trivialize $shf.o (1)$ on $D_+(x)$ and $D_+(y)$ and
  identify exactly where those trivializations fail to cover.
]

#metadata(none) <sup-vs2-5>
#example(number: "VS2-5", title: "A pencil, a blowup, and a ruled surface")[
  *Question.* What does replacing the base point of a pencil accomplish?
  For $[x:y:z] mapsto [x:y]$, RM-9 gives the incidence surface
  $H=V(x v-y u) subset sch.p^2 times sch.p^1$. BU identifies its first
  projection with $op("Bl")_p sch.p^2$, $p=[0:0:1]$.
  Its second projection identifies $H$ with
  $F_1=sch.p_(sch.p^1)(shf.o plus.o shf.o (1))$ in the quotient convention.
]
#proof[
  The full chart identification is #book-link(<sup-bu-13>)[BU-13]:
  its transition $[y:z]=[a x:z]$, $a=v/u$, is precisely the quotient
  transition of $shf.o plus.o shf.o (1)$ with quotient coordinates
  $[z:x]$. The exceptional section is the quotient onto $shf.o$ and
  has normal bundle $shf.o (-1)$. This simultaneously identifies the
  contraction to the pencil's base point and the ruling by its directions.

  In the affine chart $z=1$, the blowup chart $y=a x$ changes a line
  through $p$, with equation $y-c x=0$, into $x(a-c)=0$. Its total
  transform is the exceptional divisor plus the strict transform
  $a=c$, with multiplicity one in each. A line missing $p$ has a unit
  equation near $p$; its total transform has no exceptional component
  and equals its strict transform. This computes both transforms from
  their equations, using BU's definition by closure away from the center.
]
#exercise(title: "Variation on VS2-5")[
  Compute the strict transform of a degree-$d$ curve with multiplicity
  $r$ at $p$ by removing the factor $x^r$ on this chart. Determine its
  intersection with the exceptional curve from its lowest-degree form.
]

#metadata(none) <sup-vs2-6>
#example(number: "VS2-6", title: "Relative and absolute positivity")[
  *Question.* Why can a relatively ample bundle fail to be ample?
  On $F_n=sch.p_(sch.p^1)(shf.o plus.o shf.o (n))$, $n>=0$, let $E$
  be the section from the quotient onto $shf.o$. PJ2 computes
  $shf.o_(F_n)(1)|_E simeq shf.o_E$ and
  $shf.n_(E\/F_n) simeq shf.o_E(-n)$: the normal bundle is
  $shf.hom (shf.o (n),shf.o)$, with these specified kernel and quotient.
  The tautological sheaf has degree one on each ruling fiber and is
  relatively ample, but cannot be absolutely ample because it is
  trivial on $E simeq sch.p^1$.

  *Comparison.* Twisting by $pi^*shf.o (m)$ changes the projectivized
  module to $shf.o (m) plus.o shf.o (n+m)$. For $m>=1$ its sections are
  the degree-$m$ monomials times the first fiber coordinate and the
  degree-$(n+m)$ monomials times the second. PM checks directly that
  their map is a closed immersion. The restriction to $E$ now has
  degree $m$, while the ruling fibers still have degree one.

  *Variation.* For $n=0$, identify this construction with
  $shf.o (1,m)$ on a product of projective lines and compare VS2-2.
]

#metadata(none) <sup-vs2-7>
#example(number: "VS2-7", title: "A cusp and a node")[
  *Question.* Can tangent dimension distinguish two curve singularities?
  The cusp $y^2=x^3$ and the node $y^2=x^2(x+1)$ both have a
  two-dimensional tangent space at the origin. Their tangent cones
  are respectively $y^2=0$ and $(y-x)(y+x)=0$.
  For the cusp the normalization is $(x,y)=(t^2,t^3)$, with one point
  over the origin. For the node it is
  $(x,y)=(t^2-1,t(t^2-1))$, with two points $t=1,-1$ over the origin.

  *Comparison.* BU's strict-transform charts give a smooth curve in
  both cases; DF computes the torsion killed in the maps of differential
  modules to $k[t]d t$. The cusp map on tangent directions loses the
  first-order parameter, whereas the two node branches have distinct
  tangent directions. Equal tangent *dimensions* have forgotten these
  equations and branch data. In each case the normalization is finite
  and birational; RM explains why its rational inverse need not be regular.

  *Variation.* Repeat the tangent-cone calculation in characteristic two.
  Explain which two-branch assertion can no longer be inferred from
  the displayed factorization.
]

=== Differentials and varying fibers

#metadata(none) <sup-vs2-8>
#example(number: "VS2-8", title: "Canonical forms on plane curves")[
  *Question.* How much canonical geometry is visible in one equation?
  Let $C=V(F) subset sch.p^2$ be a smooth degree-$d$ curve. Its
  conormal bundle is $shf.o_C(-d)$ and its normal bundle is
  $shf.o_C(d)$. The conormal sequence and the Euler sequence give
  $omega_C simeq shf.o_C(d-3)$ by DF's determinant calculation.
  On $z=1$, write $f(x,y)=F(x,y,1)$. The local differential
  $d x/f_y=-d y/f_x$ is defined where the respective denominator is
  invertible; DF follows its changes on the other projective charts.

  *Comparison.* DV gives $deg shf.o_C(1)=d$, so this canonical bundle
  has degree $d(d-3)$. On a conic, its identification with
  $sch.p^1$ turns it into $shf.o_(sch.p^1)(-2)$, agreeing with VS2-1.
  On a smooth cubic the local differentials glue to a nowhere-vanishing
  form, since $shf.o_C(d-3)=shf.o_C$. These conclusions use the explicit
  transition and conormal calculations, without Riemann–Roch.

  *Variation.* For a singular plane cubic, locate the failure of the
  short exact sequence of vector bundles used in this argument; do
  not apply the smooth canonical-bundle formula to its differential sheaf.
]

#metadata(none) <sup-vs2-9>
#example(number: "VS2-9", title: "The power map and Frobenius")[
  *Question.* Which finite flat maps are étale? For
  $k[s]->k[t]$, $s mapsto t^m$, $m>=1$, use the differential computation
  in #book-link(<sup-df-8>)[DF-8] and the étale criterion in LP2-3.
  The algebra is free over $k[s]$ with basis $1,t,dots,t^(m-1)$ (Check!).
  If $m>1$ is invertible in $k$, the étale locus is $D(t)$; for $m=1$
  it is the whole affine line.

  *Comparison in characteristic $p>0$.* For $m=p$, DF-8 shows that
  relative differentials have rank one, so the map is nowhere unramified.
  Its geometric fibers each have one point of length $p$, since
  $t^p-a=(t-b)^p$ over an algebraic closure (Check!). Combining the
  free-module and differential criteria therefore gives a finite flat
  map between smooth affine lines which is nowhere étale. Smoothness
  of the two schemes does not imply smoothness of this morphism.

  *Variation.* For $m=p r$ with $r$ prime to $p$, compute separately
  the number of geometric points and the multiplicity of each fiber.
]

#metadata(none) <sup-vs2-10>
#example(number: "VS2-10", title: "A flat family with a singular fiber")[
  *Question.* Can the total space be smooth while its projection is not?
  Let $T=ops.spec k[t]$ and
  $ X=V(X_0 X_1-t X_2^2) subset sch.p^2_T. $
  The projection $f:X->T$ is flat and projective, its total space is
  smooth over $k$, and it is smooth over $T$ except at the node
  $([0:0:1],0)$. The tautological bundle has degree two on each general
  fiber and degree one on each component of the special fiber.
]
#proof[
  *Charts and projectivity.* The homogeneous quotient
  $k[t][X_0,X_1,X_2]\/(X_0 X_1-t X_2^2)$ defines a closed immersion
  into $sch.p^2_T$ by PJ and CS. Thus $f$ is projective by LP-54
  and proper by II.4.9. On $X_0!=0$, put $z=X_2/X_0$; the equation
  eliminates $X_1/X_0=t z^2$, giving $ops.spec k[t,z]$. On $X_1!=0$
  one similarly gets $ops.spec k[t,w]$. On $X_2!=0$, put
  $x=X_0/X_2$, $y=X_1/X_2$, giving
  $B=k[t,x,y]\/(x y-t) simeq k[x,y]$ with $t mapsto x y$.
  The first chart meets the third at $x!=0$, where $z=x^(-1)$ and
  $y=t z$; the analogous formulas with $y$ describe the second overlap.
  These are the restrictions of the same homogeneous coordinate ratios.

  *Flatness.* The first two chart rings are free, hence flat, over
  $k[t]$. On the third chart, $k[t]->k[x,y]$, $t mapsto x y$, is
  injective: the monomials $x^i y^i$ are linearly independent.
  Since $k[x,y]$ is a domain, this module is torsion-free over $k[t]$.
  The algebraic theorem that a torsion-free module over a principal
  ideal domain is flat is left to the reader, as is the monomial
  independence check. The source affine-cover criterion for flatness
  in LP now proves $f$ flat. Equal fiber dimensions were not used.

  *Fibers and the smooth locus.* For $t=a!=0$, the homogeneous
  partial derivatives are $X_1,X_0,-2a X_2$; they have no common
  projective zero. The fiber is a smooth conic by LP2's Jacobian
  criterion. At $a=0$, its equation is $X_0 X_1=0$, the union of two
  reduced lines meeting at $[0:0:1]$. On the third chart,
  $ Omega_(B\/k[t])=(B d x plus.o B d y)\/(y d x+x d y). $
  Where $x$ or $y$ is a unit, one derivative is invertible and LP2
  proves smoothness of relative dimension one. At $x=y=0$, the
  relative tangent space has dimension two and the fiber local ring
  $k[x,y]_(x,y)\/(x y)$ is not regular. Thus $f$ is not smooth there.
  The other two charts are polynomial lines over $T$, so this is the
  entire nonsmooth locus. All three total-space charts are affine
  planes over $k$, proving that $X\/k$ is smooth by LP2's source locality.

  *The polarization.* On a nonzero fiber the map
  $[r:s] mapsto [r^2:a s^2:r s]$ identifies $sch.p^1$ with the conic;
  its degree-two generating monomials identify the pullback of
  $shf.o_X(1)$ with $shf.o_(sch.p^1)(2)$, by PJ's Veronese calculation.
  On either special-fiber line the inclusion is linear, so the same
  bundle restricts to $shf.o_(sch.p^1)(1)$. DV's degree computation
  gives the asserted values. The smoothness of the total space,
  smoothness of a fiber, and smoothness of the projection have thus
  been tested on their respective rings and differential modules.
]

#exercise(title: "Three further calculations")[
  + Resolve the three coordinate base points of the Cremona involution;
    use BU's charts to determine the images of the coordinate lines.
  + Revisit the degree-two point on $sch.p^1_(bb(R))$ under a field
    extension, keeping residue-field degrees and multiplicities separate.
  + Replace the pencil of lines by two homogeneous forms of the same
    degree. Determine their base *scheme*, its Rees algebra, and the
    graph closure. Explain why replacing the base ideal by its radical
    can change the blowup.
]
