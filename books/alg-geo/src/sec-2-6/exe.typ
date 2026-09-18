#import "@preview/theorion:0.4.0": *
#import "../defs.typ": *

=== Exercises

// Hartshorne II.6, Exercise 6.1
#metadata(none) <exercise-ii-6-1>
#exercise(title: "Exercise 6.1")[
  If $X$ satisfies $(star)$, show $X times sch.p^n$ does also and
  $ops.cl (X times sch.p^n) simeq ops.cl (X) times ZZ$.
]

#book-link(<sup-dv-16>)[DV-16] proves the product calculation for two projective lines; the general base remains part of this exercise.

// Hartshorne II.6, Exercise 6.2
#exercise(title: "Exercise 6.2 (Varieties in Projective Space)")[
  Let $X subset.eq sch.p^n$ be nonsingular in codimension one.

  + For a hypersurface $V$ not containing $X$, define the intersection
    divisor $V dot X$ using valuations of local equations, and extend this
    to divisors on $sch.p^n$ having no component containing $X$.
  + Show principal divisors restrict to principal divisors, inducing
    $ops.cl (sch.p^n)->ops.cl (X)$.
  + Identify the coefficients with intersection multiplicities and prove
    $deg(D dot X)=deg(D)deg(X)$.
  + Show every principal divisor on $X$ is $(f) dot X$ for a rational
    function on $sch.p^n$; deduce degree descends to $ops.cl (X)$ and the map from
    $ops.cl (sch.p^n)$ is injective.
]

// Hartshorne II.6, Exercise 6.3
#exercise(title: "Exercise 6.3 (Cones)")[
  Let $V subset.eq sch.p^n$ be projectively normal and nonsingular in
  codimension one, and let $X=C(V)$ with projective closure $bar(X)$ and
  vertex $P$.

  + Show $ops.cl (V) simeq ops.cl (bar(X)-P) simeq ops.cl (bar(X))$ using the projection.
  + Derive the exact sequence
    $ZZ->ops.cl (V)->ops.cl (X)->0$, where $1$ maps to a hyperplane section.
  + Characterize when the homogeneous coordinate ring of $V$ is a UFD.
  + Show $ops.cl (X) simeq ops.cl (ops.spec shf.o_(X,P))$.
]

// Hartshorne II.6, Exercise 6.4
#exercise(title: "Exercise 6.4")[
  If $ops.char (k)!=2$ and $f in k[x_1,dots.c,x_n]$ is square-free, prove
  $k[x_1,dots.c,x_n,z]\/(z^2-f)$ is integrally closed by using the quadratic
  Galois involution and the minimal polynomial of $g+h z$.
]

// Hartshorne II.6, Exercise 6.5
#metadata(none) <exercise-ii-6-5>
#exercise(title: "Exercise 6.5 (Quadric Hypersurfaces)")[
  For the affine quadric $X:sum x_i^2=0$ in characteristic not two:

  + prove normality in dimension at least two;
  + compute $ops.cl (X)$ as $ZZ\/2ZZ$ in dimension two, $ZZ$ in dimension three,
    and $0$ in dimensions at least four;
  + compute the projective quadric class groups as $ZZ$, $ZZ plus.o ZZ$,
    and $ZZ$ respectively, noting the hyperplane class in each case;
  + prove Klein's theorem that in dimension at least four every prime divisor
    on the projective quadric is a hypersurface section.
]

#book-link(<sup-dv-15>)[DV-15] computes the affine surface cone, and DV-16 computes the projective quadric surface. The higher-dimensional cases remain separate.

// Hartshorne II.6, Exercise 6.6
#exercise(title: "Exercise 6.6 (Plane Cubic Group Law)")[
  For $y^2 z=x^3-x z^2$ with origin $P_0$:

  + show $P,Q,R$ are collinear iff $P+Q+R=0$;
  + characterize points of orders two and three by tangents through $P_0$
    and inflection points;
  + over $CC$, show the rational-coordinate points form a subgroup and
    investigate its structure.
]

// Hartshorne II.6, Exercise 6.7
#exercise(title: "Exercise 6.7")[
  For the nodal cubic $y^2 z=x^3+x^2 z$, show the degree-zero Cartier divisor
  class group is naturally $shf.g_m$.
]

// Hartshorne II.6, Exercise 6.8
#exercise(title: "Exercise 6.8")[
  + Show pullback of invertible sheaves induces $f^*:ops.pic (Y)->ops.pic (X)$.
  + For a finite map of nonsingular curves, identify it under
    $ops.pic simeq ops.cl$ with divisor pullback.
  + For a locally factorial integral projective subscheme, identify it with
    the intersection homomorphism of Exercise 6.2.
]

// Hartshorne II.6, Exercise 6.9
#exercise(title: "Exercise 6.9 (Singular Curves)")[
  For a projective curve $X$, normalization $pi:tilde(X)->X$, and local
  integral closures $tilde(shf.o)_P$:

  + prove the exact sequence
    $0->bigOPlus(tilde(shf.o)_P^times\/shf.o_P^times, P)->ops.pic (X)->ops.pic (tilde(X))->0$;
  + use it to recover the additive and multiplicative degree-zero Picard
    groups of cuspidal and nodal plane cubics.
]

// Hartshorne II.6, Exercise 6.10
#exercise(title: "Exercise 6.10 (Grothendieck Group)")[
  Define $K(X)$ from coherent sheaves modulo short-exact-sequence relations.

  + Compute $K(ops.spec k)=ZZ$.
  + For integral $X$, show rank gives a surjection $K(X)->ZZ$.
  + For closed $Y subset.eq X$, prove
    $K(Y)->K(X)->K(X-Y)->0$ is exact, using filtrations for sheaves supported
    on $Y$ and extension of coherent sheaves.
]

// Hartshorne II.6, Exercise 6.11
#exercise(title: "Exercise 6.11 (Grothendieck Group of a Curve)")[
  For a nonsingular curve $X$:

  + construct $psi:ops.cl (X)->K(X)$ from skyscraper sheaves;
  + resolve coherent sheaves by locally free sheaves and construct
    $det:K(X)->ops.pic (X)$, with $det psi(D)=shf.l (D)$;
  + show a rank-$r$ coherent sheaf differs in $K(X)$ from
    $shf.l (D) plus.o shf.o_X^(r-1)$ by a torsion class;
  + deduce $K(X) simeq ops.pic (X) plus.o ZZ$.
]

// Hartshorne II.6, Exercise 6.12
#exercise(title: "Exercise 6.12 (Degree of a Coherent Sheaf)")[
  On a complete nonsingular curve, prove there is a unique additive degree on
  coherent sheaves such that $deg shf.l (D)=deg D$ and a torsion sheaf has degree
  $sum_P op("length")(shf.f_P)$.
]
