#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.4, Definition D1
#definition(number: none, title: "Diagonal and Separated Morphisms")[
  For a morphism $f:X->Y$, the *diagonal morphism* is the unique map
  $Delta:X->X times_Y X$ whose composite with either projection is
  $ops.id_X$. The morphism $f$ is *separated* if $Delta$ is a closed immersion;
  then $X$ is separated over $Y$. A scheme is separated if it is separated
  over $ops.spec ZZ$.
]

// Hartshorne II.4, Proposition 4.1
#proposition(number: "4.1")[
  Every morphism of affine schemes is separated.
]


// Hartshorne II.4, Corollary 4.2
#corollary(number: "4.2")[
  A morphism $f:X->Y$ is separated if and only if the image of its diagonal
  is closed in $X times_Y X$.
]


// Hartshorne II.4, Theorem 4.3
#theorem(number: "4.3", title: "Valuative Criterion of Separatedness")[
  Let $f:X->Y$ be a morphism with $X$ noetherian. For every valuation ring
  $R$ with fraction field $K$, put $T=ops.spec R$ and $U=ops.spec K$. Then $f$ is
  separated if and only if, in every commutative square
  $U->X$, $T->Y$, there is at most one morphism $T->X$ extending $U->X$
  and commuting over $Y$.
]

// Hartshorne II.4, Lemma 4.4
#lemma(number: "4.4")[
  Let $R$ be a valuation ring of $K$, $T=ops.spec R$, and $U=ops.spec K$.

  + A morphism $U->X$ is equivalent to a point $x_1 in X$ and an inclusion
    $kappa(x_1) subset.eq K$.
  + A morphism $T->X$ is equivalent to points $x_0,x_1$ with $x_0$ a
    specialization of $x_1$, an inclusion $kappa(x_1) subset.eq K$, and the
    condition that $R$ dominate the local ring of $x_0$ on the reduced
    induced subscheme $overline({x_1})$.
]


// Hartshorne II.4, Lemma 4.5
#lemma(number: "4.5")[
  If $f:X->Y$ is quasi-compact, then $f(X)$ is closed if and only if it is
  stable under specialization.
]



// Hartshorne II.4, Corollary 4.6
#corollary(number: "4.6")[
  For noetherian schemes:

  + open and closed immersions are separated;
  + composites and base extensions of separated morphisms are separated;
  + products of separated morphisms over a base are separated;
  + if $g compose f$ is separated, then $f$ is separated;
  + separatedness is local on the base.
]


// Hartshorne II.4, Definition D2
#definition(number: none, title: "Proper Morphism")[
  A morphism is *proper* if it is separated, of finite type, and universally
  closed. Here *universally closed* means every base extension is a closed
  map on underlying spaces.
]

// Hartshorne II.4, Theorem 4.7
#theorem(number: "4.7", title: "Valuative Criterion of Properness")[
  Let $f:X->Y$ be of finite type with $X$ noetherian. Then $f$ is proper if
  and only if every square $U=ops.spec K->X$, $T=ops.spec R->Y$, for a valuation
  ring $R$ with fraction field $K$, admits a unique lift $T->X$.
]


// Hartshorne II.4, Corollary 4.8
#corollary(number: "4.8")[
  For noetherian schemes:

  + closed immersions are proper;
  + composites, base extensions, and products of proper morphisms are proper;
  + if $g compose f$ is proper and $g$ is separated, then $f$ is proper;
  + properness is local on the base.
]


// Hartshorne II.4, Definition D3
#definition(number: none, title: "Projective and Quasi-projective Morphisms")[
  For a scheme $Y$, set $sch.p^n_Y=fiber(sch.p^n_ZZ, Y, base: ops.spec ZZ)$.

  - A morphism $X->Y$ is *projective* if it factors as a closed immersion $X->sch.p^n_Y$ followed by projection.
  - It is *quasi-projective* if it factors as an open immersion followed by a projective morphism.
]

// Hartshorne II.4, Theorem 4.9
#theorem(number: "4.9")[
  A projective morphism of noetherian schemes is proper. A quasi-projective
  morphism of noetherian schemes is of finite type and separated.
]


// Hartshorne II.4, Proposition 4.10
#proposition(number: "4.10")[
  For algebraically closed $k$, the image of
  $t:op("Var")(k)->op("Sch")(k)$ is exactly the quasi-projective integral
  $k$-schemes; projective varieties correspond exactly to projective
  integral $k$-schemes. Thus every variety gives an integral separated
  finite-type $k$-scheme.
]


// Hartshorne II.4, Definition D4
#definition(number: none, title: "Abstract Variety")[
  An *abstract variety* over an algebraically closed field is an integral
  separated scheme of finite type. It is *complete* if it is proper over the
  field.
]

// Hartshorne II.4, Remark 4.10.1
#remark(title: "4.10.1")[
  From here on, “variety” means abstract variety. Chapter I varieties are
  identified with their associated quasi-projective schemes; curve, surface,
  and three-fold mean abstract varieties of dimensions $1,2,3$.
]

// Hartshorne II.4, Remark 4.10.2
#remark(title: "4.10.2")[
  Weil introduced abstract varieties to construct Jacobians algebraically.
  Complete varieties need not be projective: complete curves and smooth
  complete surfaces are projective, but singular complete surfaces and
  smooth complete three-folds may fail to be. Every variety nevertheless
  embeds as a dense open in a complete variety.
]

// Hartshorne II.4, Theorem 4.11A
#theorem(number: "4.11A")[
  If $A$ is a subring of a field $K$, its integral closure in $K$ is the
  intersection of all valuation rings of $K$ containing $A$.
]
