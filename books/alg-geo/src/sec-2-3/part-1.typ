#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

// Hartshorne II.3, Definition D1
#definition(number: none, title: "Connected and Irreducible Schemes")[
  A scheme is *connected*, respectively *irreducible*, when its underlying
  topological space has that property.
]

// Hartshorne II.3, Definition D2
#definition(number: none, title: "Reduced Scheme")[
  A scheme $X$ is *reduced* when every $shf.o_X (U)$ has no nonzero nilpotent;
  equivalently, every local ring $shf.o_(X,P)$ is reduced.
]

// Hartshorne II.3, Definition D3
#definition(number: none, title: "Integral Scheme")[
  A scheme $X$ is *integral* when $shf.o_X (U)$ is an integral domain for every
  open $U subset.eq X$.
]

// Hartshorne II.3, Proposition 3.1
#proposition(number: "3.1")[
  A scheme is integral if and only if it is reduced and irreducible.
]


// Hartshorne II.3, Definition D4
#definition(number: none, title: "Locally Noetherian and Noetherian Schemes")[
  A scheme is *locally noetherian* if it has an affine cover $ops.spec A_i$ with
  every $A_i$ noetherian. It is *noetherian* if it is locally noetherian and
  its underlying space is noetherian.
]

// Hartshorne II.3, Proposition 3.2
#proposition(number: "3.2")[
  A scheme $X$ is locally noetherian if and only if every open affine
  $U=ops.spec A subset.eq X$ has $A$ noetherian. In particular, an affine scheme
  $ops.spec A$ is noetherian exactly when $A$ is noetherian.
]


// Hartshorne II.3, Definition D5
#definition(number: none, title: "Morphisms of Finite Type")[
  A morphism $f:X->Y$ is *locally of finite type* if $Y$ has an affine cover
  $V_i=ops.spec B_i$ such that each $f^(-1) (V_i)$ has an affine cover
  $ops.spec A_(i j)$ with every $A_(i j)$ a finitely generated $B_i$-algebra.
  It is *of finite type* if those inverse images can be covered by finitely
  many such affines.
]

// Hartshorne II.3, Definition D6
#definition(number: none, title: "Finite Morphism")[
  A morphism $f:X->Y$ is *finite* if $Y$ has an affine cover
  $V_i=ops.spec B_i$ such that $f^(-1) (V_i)=ops.spec A_i$ is affine and each $A_i$ is
  a finite $B_i$-module.
]

// Hartshorne II.3, Definition D7
#definition(number: none, title: "Open and Closed Subschemes")[
  An *open subscheme* of $X$ has an open underlying subset and the restricted
  structure sheaf. A *closed subscheme* is the image data of a closed
  immersion into $X$.
]

// Hartshorne II.3, Definition D8
#definition(number: none, title: "Closed Immersion")[
  A morphism $f:Y->X$ is a *closed immersion* if it is a homeomorphism onto
  a closed subset of $ops.sp (X)$ and $f^sharp:shf.o_X->f_*shf.o_Y$ is surjective.
]

// Hartshorne II.3, Definition D9
#definition(number: none, title: "Dimension and Codimension")[
  The dimension of a scheme is the dimension of its underlying topological
  space. If $Z$ is irreducible closed, its codimension in $X$ is the supremum
  of lengths of chains of irreducible closed subsets from $Z$ upward; for
  arbitrary closed $Y$, take the infimum over its irreducible components.
]

// Hartshorne II.3, Definition D10
#definition(number: none, title: "Fibred Product")[
  For $X,Y$ over $S$, a fibred product is an $S$-scheme $X times_S Y$ with
  projections to $X,Y$ such that every $S$-scheme mapping compatibly to both
  factors admits a unique map to $X times_S Y$.
]

// Hartshorne II.3, Theorem 3.3
#theorem(number: "3.3", title: "Existence of Fibred Products")[
  For any schemes $X,Y$ over $S$, the fibred product $X times_S Y$ exists
  and is unique up to unique isomorphism.
]


// Hartshorne II.3, Definition D11
#definition(number: none, title: "Fibre of a Morphism")[
  For $f:X->Y$ and $y in Y$, the *fibre over* $y$ is
  $X_y=X times_Y ops.spec kappa(y)$, where $ops.spec kappa(y)->Y$ is the natural
  morphism associated with $y$.
]
