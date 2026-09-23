#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Exercises

// Hartshorne I.5, Exercise 5.1
#exercise(title: "Exercise 5.1")[
  Assume $ops.char (k)!=2$. Locate the singular points and sketch these plane
  curves; identify the node, triple point, cusp, and tacnode:

  #set enum(numbering: "a)", spacing: 0.8em)

  + $x^2=x^4+y^4$;
  + $x y=x^6+y^6$;
  + $x^3=y^2+x^4+y^4$;
  + $x^2 y+x y^2=x^4+y^4$.
]

// Hartshorne I.5, Exercise 5.2
#exercise(title: "Exercise 5.2")[
  Assume $ops.char (k)!=2$. Locate and describe the singularities of the following
  surfaces in $sch.a^3$; identify the conical double point, double line, and pinch
  point:

  #set enum(numbering: "a)", spacing: 0.8em)

  + $x y^2=z^2$;
  + $x^2+y^2=z^2$;
  + $x y+x^3+y^3=0$.
]

// Hartshorne I.5, Exercise 5.3
#exercise(title: "Exercise 5.3 (Multiplicities)")[
  Let $Y subset.eq sch.a^2$ be $f(x,y)=0$ and move $P$ to $(0,0)$. Write
  $f=f_0+f_1+dots+f_d$ with $f_i$ homogeneous of degree $i$. The
  *multiplicity* $mu_P (Y)$ is the least $r$ with $f_r!=0$; the linear factors
  of $f_r$ are the tangent directions at $P$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $mu_P (Y)=1$ if and only if $P$ is nonsingular.
  + Find the multiplicities of the singular points in Exercise 5.1.
]

// Hartshorne I.5, Exercise 5.4
#exercise(title: "Exercise 5.4 (Intersection Multiplicity)")[
  For distinct plane curves $Y:f=0$ and $Z:g=0$ meeting at $P$, define
  $(Y dot Z)_P$ to be the length of the $shf.o_P$-module $shf.o_P\/(f,g)$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show it is finite and $(Y dot Z)_P >= mu_P (Y) mu_P (Z)$.
  + If $P in Y$, show that $(L dot Y)_P=mu_P (Y)$ for all but finitely many
    lines $L$ through $P$.
  + If $Y subset.eq sch.p^2$ has degree $d$ and $L!=Y$ is a line, show that
    $(L dot Y)=sum_(P in L inter Y) (L dot Y)_P=d$.
]

// Hartshorne I.5, Exercise 5.5
#exercise(title: "Exercise 5.5")[
  For every $d>0$ and every characteristic $p$ (zero or prime), give an
  equation for a nonsingular plane projective curve of degree $d$ over a field
  of characteristic $p$.
]

// Hartshorne I.5, Exercise 5.6
#exercise(title: "Exercise 5.6 (Blowing Up Curve Singularities)")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Blow up at $0$ the cusp and node from Exercise 5.1. Show that their strict
    transforms are nonsingular.
  + A node is a double point with distinct tangent directions. Show that the
    inverse image of a node consists of two distinct nonsingular points.
  + Show that blowing up a tacnode produces a node, so two successive blow-ups
    resolve it.
  + For $Y:y^3=x^5$, show that $0$ is a triple point, one blow-up gives a
    double point, and one further blow-up resolves it.
]

// Hartshorne I.5, Exercise 5.7
#exercise(title: "Exercise 5.7")[
  Let $Y subset.eq sch.p^2$ be a nonsingular plane curve of degree greater than
  $1$, defined by homogeneous $f$, and let $X=Z(f) subset.eq sch.a^3$ be its cone
  with vertex $P=0$. Blow up $X$ at $P$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $P$ is the only singular point of $X$.
  + Show that the blown-up variety is nonsingular by covering it with affines.
  + Show that the inverse image of $P$ is isomorphic to $Y$.
]

// Hartshorne I.5, Exercise 5.8
#exercise(title: "Exercise 5.8")[
  Let $Y subset.eq sch.p^n$ have dimension $r$, with homogeneous ideal generated
  by $f_1,...,f_t$. For $P=(a_0:...:a_n)$, show that $P$ is nonsingular if and
  only if the matrix $((partial f_i)/(partial x_j)(a_0,...,a_n))$ has rank
  $n-r$. Use Euler's identity
  $sum_i x_i (partial f)/(partial x_i)=(deg f)f$.
]

// Hartshorne I.5, Exercise 5.9
#exercise(title: "Exercise 5.9")[
  Let $f in k[x,y,z]$ be homogeneous and $Y=Z(f) subset.eq sch.p^2$. Suppose
  that at every $P in Y$ at least one of
  $(partial f)/(partial x)$, $(partial f)/(partial y)$, $(partial f)/(partial z)$ is
  nonzero. Show that $f$ is irreducible and hence $Y$ is nonsingular.
]

// Hartshorne I.5, Exercise 5.10
#exercise(title: "Exercise 5.10 (Zariski Tangent Space)")[
  For $P in X$, with maximal ideal $idl.m subset.eq shf.o_P$, define
  $T_P (X)=(idl.m\/idl.m^2)^ast$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that $dim T_P (X)>=dim X$, with equality if and only if $P$ is
    nonsingular.
  + Show that a morphism $phi:X->Y$ induces a natural linear map
    $T_P (phi):T_P (X)->T_(phi(P)) (Y)$.
  + For vertical projection of the parabola $x=y^2$ to the $x$-axis, show that
    the induced tangent map at the origin is zero.
]

// Hartshorne I.5, Exercise 5.11
#exercise(title: "Exercise 5.11 (The Elliptic Quartic Curve in $PP^3$)")[
  Let $Y subset.eq sch.p^3$ be defined by
  $x^2-x z-y w=0$ and $y z-x w-z w=0$. Let $P=(0:0:0:1)$ and project from $P$ to
  $w=0$. Show that this induces an isomorphism from $Y without {P}$ to the
  plane cubic $y^2 z-x^3+x z^2=0$ minus $(1:0:-1)$. Then show that $Y$ is an
  irreducible nonsingular curve.
]

// Hartshorne I.5, Exercise 5.12
#exercise(title: "Exercise 5.12 (Quadric Hypersurfaces)")[
  Assume $ops.char (k)!=2$ and let $f$ be homogeneous of degree $2$ in
  $x_0,...,x_n$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that a linear change of variables puts $f$ in the form
    $x_0^2+dots+x_r^2$ for some $0<=r<=n$.
  + Show that $f$ is irreducible if and only if $r>=2$.
  + For $r>=2$, let $Q=Z(f) subset.eq sch.p^n$. Show that $ops.sing Q$ is a linear
    variety of dimension $n-r-1$; in particular $Q$ is nonsingular if and
    only if $r=n$.
  + If $r<n$, show that $Q$ is a cone, with axis $ops.sing Q$, over a
    nonsingular quadric in $sch.p^r$.
]

// Hartshorne I.5, Exercise 5.13
#exercise(title: "Exercise 5.13")[
  Every regular local ring is an integrally closed domain. Show directly,
  without using Theorem 5.3, that the nonnormal points of a variety form a
  proper closed subset. Use finiteness of integral closure, Theorem 3.9A.
]

// Hartshorne I.5, Exercise 5.14
#exercise(title: "Exercise 5.14 (Analytically Isomorphic Singularities)")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that analytically isomorphic plane-curve singularities have the same
    multiplicity.
  + If $f=f_(s+t)+f_(s+t+1)+dots in k text("[[") x,y text("]] ")$
    and $f_(s+t)=g_s h_t$, where $g_s,h_t$ are homogeneous and have no common
    linear factor, show that $f=g h$ for formal power series beginning with
    $g_s$ and $h_t$ respectively.
  + An *ordinary $r$-fold point* is one whose leading form is a product of $r$
    distinct linear factors. Show that all ordinary double points are
    analytically isomorphic, as are all ordinary triple points, but ordinary
    fourfold points form a one-parameter family of mutually nonisomorphic
    singularities.
  + Assuming $ops.char (k)!=2$, show that every double point of a plane curve is
    analytically isomorphic to $y^2=x^r$ for a unique $r>=2$. The cases
    $r=2,3,4$ are respectively a node, cusp, and tacnode.
]

// Hartshorne I.5, Exercise 5.15
#exercise(title: "Exercise 5.15 (Families of Plane Curves)")[
  A homogeneous degree-$d$ polynomial in three variables has
  $binom(d+2, 2)$ coefficients, which determine a point of
  $sch.p^N$, $N=binom(d+2, 2)-1=d(d+3)/2$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + Show that points of $sch.p^N$ correspond to algebraic subsets of $sch.p^2$
    definable by an equation of degree $d$, one-to-one except when the
    polynomial has a multiple factor.
  + Show that irreducible nonsingular curves of degree $d$ correspond
    bijectively to a nonempty Zariski-open subset of $sch.p^N$. Use elimination
    theory on the three partial derivatives and Exercises 5.5, 5.8, and 5.9.
]
