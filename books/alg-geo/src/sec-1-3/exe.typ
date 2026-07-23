#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Exercises

// Hartshorne I.3, Exercise 3.1
#exercise(title: "Exercise 3.1")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that any conic in $sch.a^2$ is isomorphic either to $sch.a^1$ or to
    $sch.a^1 without {0}$.
  + Show that $sch.a^1$ is not isomorphic to any proper open subset of itself.
  + Show that every conic in $sch.p^2$ is isomorphic to $sch.p^1$.
  + Show that $sch.a^2$ is not homeomorphic to $sch.p^2$.
  + If an affine variety is isomorphic to a projective variety, show that it
    consists of one point.
]

// Hartshorne I.3, Exercise 3.2
#exercise(title: "Exercise 3.2")[
  A morphism whose underlying map of topological spaces is a homeomorphism
  need not be an isomorphism.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Let $phi:sch.a^1->sch.a^2$ be $t mapsto (t^2,t^3)$. Show that it is a bijective
    bicontinuous morphism onto the curve $y^2=x^3$, but is not an isomorphism.
  + If $ops.char (k)=p>0$, show that the Frobenius morphism
    $phi:sch.a^1->sch.a^1$, $t mapsto t^p$, is bijective and bicontinuous but not an
    isomorphism.
]

// Hartshorne I.3, Exercise 3.3
#exercise(title: "Exercise 3.3")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that a morphism $phi:X->Y$ induces, for each $P in X$, a homomorphism
    of local rings $phi_P^sharp: shf.o_(phi(P),Y) -> shf.o_(P,X)$.
  + Show that $phi$ is an isomorphism if and only if it is a homeomorphism and
    every induced map $phi_P^sharp$ is an isomorphism.
  + If $phi(X)$ is dense in $Y$, show that every $phi_P^sharp$ is injective.
]

// Hartshorne I.3, Exercise 3.4
#exercise(title: "Exercise 3.4")[
  Show that the $d$-uple embedding of $sch.p^n$ is an isomorphism onto its image.
]

// Hartshorne I.3, Exercise 3.5
#exercise(title: "Exercise 3.5")[
  A variety is called *affine* if it is isomorphic to an affine variety. If
  $H subset.eq sch.p^n$ is any hypersurface, show that $sch.p^n without H$ is affine.

  _Hint:_ If $deg H=d$, use the $d$-uple embedding and the fact that projective
  space minus a hyperplane is affine.
]

// Hartshorne I.3, Exercise 3.6
#exercise(title: "Exercise 3.6")[
  Show that the quasi-affine variety $X=sch.a^2 without {(0,0)}$ is not affine.

  _Hint:_ Show that $shf.o (X)=k[x,y]$ and use Proposition 3.5.
]

// Hartshorne I.3, Exercise 3.7
#exercise(title: "Exercise 3.7")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that any two curves in $sch.p^2$ have nonempty intersection.
  + More generally, if $Y subset.eq sch.p^n$ is projective with $dim Y >= 1$ and
    $H$ is a hypersurface, show that $Y inter H != emptyset$.

  _Hint:_ Use Exercises 3.5 and 3.1(e).
]

// Hartshorne I.3, Exercise 3.8
#exercise(title: "Exercise 3.8")[
  Let $H_i,H_j$ be the hyperplanes $x_i=0$ and $x_j=0$ in $sch.p^n$, with
  $i != j$. Show that every regular function on
  $sch.p^n without (H_i inter H_j)$ is constant.
]

// Hartshorne I.3, Exercise 3.9
#exercise(title: "Exercise 3.9")[
  Let $X=sch.p^1$ and let $Y$ be its $2$-uple embedding in $sch.p^2$. Although
  $X simeq Y$, show that their homogeneous coordinate rings are not
  isomorphic. Thus the homogeneous coordinate ring of a projective variety is
  not invariant under isomorphism.
]

// Hartshorne I.3, Exercise 3.10
#exercise(title: "Exercise 3.10 (Subvarieties)")[
  A subset is *locally closed* if it is open in its closure, equivalently if it
  is the intersection of an open and a closed subset. An irreducible locally
  closed subset $Y$ of a quasi-affine or quasi-projective variety $X$ inherits
  a variety structure and is called a *subvariety*.

  Let $phi:X->Y$ be a morphism, and let $X' subset.eq X$ and
  $Y' subset.eq Y$ be irreducible locally closed subsets with
  $phi(X') subset.eq Y'$. Show that the restriction $phi|_(X'):X'->Y'$ is a
  morphism.
]

// Hartshorne I.3, Exercise 3.11
#exercise(title: "Exercise 3.11")[
  Let $X$ be a variety and $P in X$. Show that prime ideals of the local ring
  $shf.o_P$ correspond bijectively to closed subvarieties of $X$ containing $P$.
]

// Hartshorne I.3, Exercise 3.12
#exercise(title: "Exercise 3.12")[
  If $P$ is a point of a variety $X$, show that $dim shf.o_P = dim X$.

  _Hint:_ Reduce to the affine case and use Theorem 3.2(c).
]

// Hartshorne I.3, Exercise 3.13
#exercise(title: "Exercise 3.13 (The Local Ring of a Subvariety)")[
  Let $Y subset.eq X$ be a subvariety. Let $shf.o_(Y,X)$ consist of equivalence
  classes of pairs $(U,f)$, where $U subset.eq X$ is open,
  $U inter Y != emptyset$, and $f$ is regular on $U$, with two pairs equivalent
  when their functions agree on $U inter V$. Show that $shf.o_(Y,X)$ is a local
  ring with residue field $K(Y)$ and dimension $dim X-dim Y$. Note that
  $shf.o_(P,X)=shf.o_P$ and $shf.o_(X,X)=K(X)$.
]

// Hartshorne I.3, Exercise 3.14
#exercise(title: "Exercise 3.14 (Projection from a Point)")[
  Let $sch.p^n$ be a hyperplane in $sch.p^(n+1)$ and let
  $P in sch.p^(n+1) without sch.p^n$. Define
  $phi:sch.p^(n+1) without {P}->sch.p^n$ by sending $Q$ to the intersection of
  $sch.p^n$ with the line through $P,Q$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $phi$ is a morphism.
  + Let $Y subset.eq sch.p^3$ be the twisted cubic parametrized by
    $(x:y:z:w)=(t^3:t^2 u:t u^2:u^3)$. Take $P=(0:0:1:0)$ and the plane
    $z=0$. Show that projection of $Y$ from $P$ is a cuspidal plane cubic and
    find its equation.
]

// Hartshorne I.3, Exercise 3.15
#exercise(title: "Exercise 3.15 (Products of Affine Varieties)")[
  Let $X subset.eq sch.a^n$ and $Y subset.eq sch.a^m$ be affine varieties.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $X times Y subset.eq sch.a^(n+m)$ is irreducible in its induced
    topology. This affine variety is called the *product* of $X$ and $Y$.
  + Show that $A(X times Y) simeq tensor(A(X),A(Y),k)$.
  + Show that $X times Y$ is a categorical product: the projections are
    morphisms, and for morphisms $Z->X$ and $Z->Y$ there is a unique morphism
    $Z->X times Y$ with those composites.
  + Show that $dim(X times Y)=dim X+dim Y$.
]

// Hartshorne I.3, Exercise 3.16
#exercise(title: "Exercise 3.16 (Products of Quasi-projective Varieties)")[
  Use the Segre embedding to give $sch.p^n times sch.p^m$ a projective variety
  structure. For quasi-projective varieties $X subset.eq sch.p^n$ and
  $Y subset.eq sch.p^m$:

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $X times Y$ is quasi-projective.
  + If $X,Y$ are projective, show that $X times Y$ is projective.
  + Show that $X times Y$ is a product in the category of varieties.
]

// Hartshorne I.3, Exercise 3.17
#exercise(title: "Exercise 3.17 (Normal Varieties)")[
  A variety $Y$ is *normal at* $P$ if $shf.o_P$ is integrally closed, and *normal*
  if it is normal at every point.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that every conic in $sch.p^2$ is normal.
  + Show that the quadric surfaces $Q_1:x y=z w$ and $Q_2:x y=z^2$ in $sch.p^3$
    are normal.
  + Show that the cuspidal cubic $y^2=x^3$ in $sch.a^2$ is not normal.
  + If $Y$ is affine, show that $Y$ is normal if and only if $A(Y)$ is
    integrally closed.
  + Let $Y$ be affine. Show that there is a normal affine variety
    $tildeOf(Y)$ and a morphism $nu:tildeOf(Y)->Y$ such that every dominant
    morphism $phi:Z->Y$ from a normal variety factors uniquely as
    $phi=nu compose theta$. The variety $tildeOf(Y)$ is the *normalization* of
    $Y$. Use Theorem 3.9A.
]

// Hartshorne I.3, Exercise 3.18
#exercise(title: "Exercise 3.18 (Projectively Normal Varieties)")[
  A projective variety $Y subset.eq sch.p^n$ is *projectively normal* for the
  given embedding if $S(Y)$ is integrally closed.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that a projectively normal variety is normal.
  + Let $Y$ be the twisted quartic in $sch.p^3$ parametrized by
    $(x:y:z:w)=(t^4:t^3 u:t u^3:u^4)$. Show that $Y$ is normal but not
    projectively normal.
  + Show that this $Y$ is isomorphic to $sch.p^1$, which is projectively normal;
    thus projective normality depends on the embedding.
]

// Hartshorne I.3, Exercise 3.19
#exercise(title: "Exercise 3.19 (Automorphisms of Affine Space)")[
  Let $phi:sch.a^n->sch.a^n$ be given by polynomials $f_1,...,f_n$ in
  $x_1,...,x_n$, and let $J=det(partial f_i/partial x_j)$ be its Jacobian.

  #set enum(numbering: "a)", spacing: 0.8em)

  + If $phi$ is an automorphism, show that $J$ is a nonzero constant.
  + The converse is an unsolved problem even for $n=2$; see Vitushkin [1].
]

// Hartshorne I.3, Exercise 3.20
#exercise(title: "Exercise 3.20")[
  Let $Y$ be a variety of dimension $2$, let $P in Y$ be normal, and let $f$
  be regular on $Y without {P}$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $f$ extends to a regular function on $Y$.
  + Show that this is false in dimension $1$.
]

// Hartshorne I.3, Exercise 3.21
#exercise(title: "Exercise 3.21 (Group Varieties)")[
  A *group variety* is a variety $Y$ with a morphism $mu:Y times Y->Y$ whose
  operation makes the points of $Y$ a group and whose inversion map is also a
  morphism.

  #set enum(numbering: "a)", spacing: 0.8em)

  + The additive group $shf.g_a$ is $sch.a^1$ with
    $mu(a,b)=a+b$. Show that it is a group variety.
  + The multiplicative group $shf.g_m$ is $sch.a^1 without {0}$ with
    $mu(a,b)=a b$. Show that it is a group variety.
  + If $G$ is a group variety and $X$ any variety, show that
    $op("Hom")(X,G)$ has a natural group structure.
  + Show that $op("Hom")(X,shf.g_a) simeq shf.o (X)$ as additive groups.
  + Show that $op("Hom")(X,shf.g_m)$ is the group of units of $shf.o (X)$.
]
