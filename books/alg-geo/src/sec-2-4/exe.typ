#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.4, Exercise 4.1
#exercise(title: "Exercise 4.1")[
  Show that every finite morphism is proper.
]

// Hartshorne II.4, Exercise 4.2
#exercise(title: "Exercise 4.2")[
  Let $X$ be reduced over $S$ and $Y$ separated over $S$. Show two
  $S$-morphisms $X->Y$ agreeing on a dense open are equal. Give counterexamples
  when $X$ is nonreduced and when $Y$ is nonseparated.
]

// Hartshorne II.4, Exercise 4.3
#exercise(title: "Exercise 4.3")[
  If $X$ is separated over affine $S$ and $U,V subset.eq X$ are affine open,
  show $U inter V$ is affine. Give a counterexample without separatedness.
]

// Hartshorne II.4, Exercise 4.4
#exercise(title: "Exercise 4.4")[
  Let $f:X->Y$ be a morphism of separated finite-type schemes over
  noetherian $S$, and let $Z subset.eq X$ be a closed subscheme proper over
  $S$. Show its scheme-theoretic image $f(Z)$ is closed in $Y$ and proper
  over $S$. Factor $f$ through its graph in $X times_S Y$.
]

// Hartshorne II.4, Exercise 4.5
#exercise(title: "Exercise 4.5 (Centers of Valuations)")[
  Let integral finite-type $X\/k$ have function field $K$. A valuation of
  $K\/k$ has center $x$ when its ring dominates $shf.o_(X,x)$.

  + If $X$ is separated, show a center is unique.
  + If $X$ is proper, show every valuation has a unique center.
  + Prove the converses.
  + If $X$ is proper and $k$ algebraically closed, show
    $Gamma(X,shf.o_X)=k$.
]

// Hartshorne II.4, Exercise 4.6
#exercise(title: "Exercise 4.6")[
  Show a proper morphism between affine varieties over $k$ is finite, using
  Theorem 4.11A.
]

// Hartshorne II.4, Exercise 4.7
#exercise(title: "Exercise 4.7 (Schemes over $RR$)")[
  For $X_0\/RR$, put $X=X_0 times_RR CC$ with its semilinear conjugation
  involution.

  + Conversely, descend a separated finite-type $CC$-scheme with semilinear
    involution to a unique $X_0\/RR$, assuming every two points lie in a
    common affine open.
  + Show $X_0$ is affine iff $X$ is.
  + Show real morphisms correspond to complex morphisms commuting with the
    involutions.
  + Determine the real forms when $X simeq sch.a^1_CC$ and when
    $X simeq sch.p^1_CC$; in the latter case include the anisotropic conic.
]

// Hartshorne II.4, Exercise 4.8
#exercise(title: "Exercise 4.8")[
  Suppose a property $P$ of morphisms contains closed immersions, is stable
  under composition, and is stable under base extension. Prove it is stable
  under products; if $g compose f$ has $P$ and $g$ is separated then $f$
  has $P$; and $X_(red)->Y_(red)$ has $P$ whenever $X->Y$ does.
]

// Hartshorne II.4, Exercise 4.9
#exercise(title: "Exercise 4.9")[
  Show composites of projective morphisms are projective, using the Segre
  closed immersion $sch.p^r times sch.p^s->sch.p^(r s+r+s)$. Deduce projective
  morphisms have all properties from Exercise 4.8.
]

// Hartshorne II.4, Exercise 4.10
#exercise(title: "Exercise 4.10 (Chow's Lemma)")[
  If $X$ is proper over noetherian $S$, construct a projective $X'->S$ and
  $g:X'->X$ that is an isomorphism over a dense open of $X$.

  + Reduce to irreducible $X$ and cover it by finitely many quasi-projective
    opens $V_i->P_i$ with $P_i$ projective over $S$.
  + For $V=inter V_i$, take the scheme-theoretic closure of its graph in
    $X times_S P_1 times_S dots times_S P_n$.
  + Show projection to the product of the $P_i$ is a closed immersion and
    projection to $X$ is an isomorphism over $V$.
]

// Hartshorne II.4, Exercise 4.11
#exercise(title: "Exercise 4.11")[
  + Let $(A,idl.m)$ be a noetherian local domain with fraction field $K$ and
    $L\/K$ finitely generated. Prove that a DVR of $L$ dominates $A$, reducing
    to a finite extension and using a one-dimensional localization together
    with Krull–Akizuki.
  + Deduce that for finite-type morphisms of noetherian schemes, the
    valuative criteria for separatedness and properness need only be tested
    on discrete valuation rings.
]

// Hartshorne II.4, Exercise 4.12
#exercise(title: "Exercise 4.12 (Examples of Valuation Rings)")[
  + For a one-dimensional function field $K\/k$, show every nontrivial
    valuation ring is discrete and identify them with the points of the
    abstract nonsingular curve $C_K$.
  + For the function field of a smooth complete surface, analyze valuations
    centered at the generic point of a curve, exceptional divisors under
    birational maps, and the local union obtained from an infinite sequence
    of blowups at chosen closed points; determine when the resulting
    dominating valuation is discrete.
]
