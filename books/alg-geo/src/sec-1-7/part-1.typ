#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne I.7, Proposition 7.1
#proposition(number: "7.1", title: "Affine Dimension Theorem")[
  Let $Y,Z subset.eq sch.a^n$ be varieties of dimensions $r,s$. Every
  irreducible component $W$ of $Y inter Z$ has
  $dim W>=r+s-n$.
]


// Hartshorne I.7, Theorem 7.2
#theorem(number: "7.2", title: "Projective Dimension Theorem")[
  Let $Y,Z subset.eq sch.p^n$ have dimensions $r,s$. Every irreducible component
  of $Y inter Z$ has dimension at least $r+s-n$. If $r+s-n>=0$, then
  $Y inter Z!=emptyset$.
]


// Hartshorne I.7, Definition D1
#definition(number: none, title: "Numerical Polynomial")[
  A polynomial $P(z) in QQ[z]$ is *numerical* if $P(n) in ZZ$ for all
  sufficiently large integers $n$.
]

// Hartshorne I.7, Proposition 7.3
#proposition(number: "7.3")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Every numerical polynomial has a unique expression
    $P(z)=c_0 binom(z, r)+c_1 binom(z, r-1)+dots+c_r$ with $c_i in ZZ$.
    In particular, $P(n) in ZZ$ for every integer $n$.
  + If $f:ZZ->ZZ$ and the difference
    $Delta f(n)=f(n+1)-f(n)$ agrees eventually with a numerical polynomial,
    then $f$ eventually agrees with a numerical polynomial.
]


// Hartshorne I.7, Proposition 7.4
#proposition(number: "7.4")[
  Let $M$ be a finitely generated graded module over a noetherian graded ring
  $S$. There is a filtration by graded submodules
  $0=M_0 subset.eq dots subset.eq M_t=M$ with
  $M_i\/M_(i-1) simeq (S\/idl.p_i)(l_i)$ for homogeneous primes $idl.p_i$.

  #set enum(numbering: "a)", spacing: 0.8em)

  + A homogeneous prime contains $ops.ann (M)$ if and only if it contains some
    $idl.p_i$; hence the minimal $idl.p_i$ are the minimal primes of $M$.
  + For a minimal prime $idl.p$ of $M$, its number of occurrences among the
    $idl.p_i$ is $op("length")_(S_idl.p) (M_idl.p)$ and is independent of the filtration.
]


// Hartshorne I.7, Definition D2
#definition(number: none, title: "Multiplicity at a Minimal Prime")[
  If $idl.p$ is a minimal prime of a graded $S$-module $M$, define
  $mu_idl.p (M)=op("length")_(S_idl.p) (M_idl.p)$.
]

// Hartshorne I.7, Theorem 7.5
#theorem(number: "7.5", title: "Hilbert-Serre")[
  Let $M$ be a finitely generated graded module over
  $S=k[x_0,...,x_n]$. There is a unique $P_M (z) in QQ[z]$ such that
  $dim_k M_l=P_M (l)$ for all $l$ sufficiently large. Moreover,
  $deg P_M=dim Z(ops.ann (M))$ in $sch.p^n$.
]


// Hartshorne I.7, Definition D3
#definition(number: none, title: "Hilbert Polynomial of a Module")[
  The polynomial $P_M$ in Theorem 7.5 is the *Hilbert polynomial* of $M$.
]

// Hartshorne I.7, Definition D4
#definition(number: none, title: "Hilbert Polynomial and Degree of a Projective Set")[
  If $Y subset.eq sch.p^n$ is algebraic of dimension $r$, its *Hilbert polynomial*
  is $P_Y=P_(S(Y))$. Its *degree* is $r!$ times the leading coefficient of
  $P_Y$.
]

// Hartshorne I.7, Proposition 7.6
#proposition(number: "7.6")[
  #set enum(numbering: "a)", spacing: 0.8em)

  + Every nonempty algebraic set has positive integral degree.
  + If $Y=Y_1 union Y_2$, both $Y_i$ have dimension $r$, and
    $dim(Y_1 inter Y_2)<r$, then $deg Y=deg Y_1+deg Y_2$.
  + $deg sch.p^n=1$.
  + A hypersurface defined by a homogeneous polynomial of degree $d$ has
    degree $d$.
]


// Hartshorne I.7, Theorem 7.7
#theorem(number: "7.7")[
  Let $Y subset.eq sch.p^n$ have dimension $r$ and let $H$ be a hypersurface not
  containing $Y$. If $Z_1,...,Z_s$ are the irreducible components of
  $Y inter H$, then
  $sum_(j=1)^s i(Y,H;Z_j) deg Z_j=(deg Y)(deg H)$.
]


// Hartshorne I.7, Corollary 7.8
#corollary(number: "7.8", title: "Bézout's Theorem")[
  Let $Y,Z subset.eq sch.p^2$ be distinct curves of degrees $d,e$, and let
  $Y inter Z={P_1,...,P_s}$. Then
  $sum_i i(Y,Z;P_i)=d e$.
]


// Hartshorne I.7, Remark 7.8.1
#remark(title: "7.8.1")[
  This homogeneous-coordinate-ring intersection multiplicity differs in
  definition from the local one in Exercise 5.4, but the two agree for plane
  curves.
]

// Hartshorne I.7, Remark 7.8.2
#remark(title: "7.8.2")[
  The proof extends to reducible algebraic sets of dimension $1$ in $sch.p^2$
  provided they have no irreducible component in common.
]
