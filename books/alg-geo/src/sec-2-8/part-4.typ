#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Applications

We define some invariants of nonsingular varieties.
// Hartshorne II.8, Definition D5
#definition(number: none)[
  Let $X$ be a nonsingular variety over $k$ of dimension $n$.
  - *(Tangent Sheaf).* The _tangent sheaf_ of $X$ is // defined to be
  $shf.t_X := shf.hom_(shf.o_X) (Omega_(X\/k), shf.o_X) in cat.mod(shf.o_X)$, which is locally free of rank $n$.
  - *(Canonical Sheaf).* The _canonical sheaf_ of $X$ is defined to be $omega_X := and.big^n Omega_(X\/k) in cat.mod(shf.o_X)$, which is an invertible sheaf.
  - *(Geometric Genus).* If, in addition, $X$ is projective, we define the _geometric genus_ of $X$ to be $p_g := ops.dim(Gamma(X,omega_X), over:k) >= 0$.
]

// Hartshorne II.8, Remark 8.18.2
#remark(title: "8.18.2")[
  For a nonsingular projective curve, the arithmetic and geometric genera
  agree by Serre duality. In higher dimension they need not agree.
]

// Hartshorne II.8, Remark 8.18.3
#remark(title: "8.18.3")[
  Differentials, the tangent sheaf, and the canonical sheaf are intrinsic.
  Thus their numerical invariants are isomorphism invariants; Theorem 8.19
  strengthens this for geometric genus to birational invariance.
]
// Hartshorne II.8, Theorem 8.19
#theorem(number: "8.19")[
  Let $X$ and $X'$ be two birationally equivalent nonsingular projective varieties over $k$. Then, $p_g (X)=p_g (X')$.
]
#proof[
  Recall that for $X$ and $X'$ to be birationally equivalent, there are rational maps $X to X'$ and $X' to X$ which are inverses to each other. We consider the rational map $X to X'$ represented by the morphism $V morph(f,cat.sch) X'$, where $V subset X$ is the largest defining open set. By _(8.11)_, we have a map $f^ast Omega_(X'\/k) arrow.r.long Omega_(V\/k)$. Note that
  - $ops.dim(X)=ops.dim(X')=n$.
  - $X$ and $X'$ being nonsingular yields that $Omega_(V\/k)=(Omega_(X\/k))|_V, Omega_(X'\/k)$, and thus $f^ast Omega_(X'\/k)$ are locally free sheaves of rank $n$.
  - _Check._ $omega_X|_V=( and.big^n Omega_(X\/k))|_V isoBy(text("(?)")) and.big^n (Omega_(X\/k)|_V)attach(simeq, b: text("(8.10)")) and.big^n Omega_(V\/k)=omega_V$
  - _Check._ $f^ast omega_(X')=f^ast ( and.big^n Omega_(X'\/k))attach(simeq, b: text("(?)")) and.big^n (f^ast Omega_(X'\/k))$.
  Thus, this induces a natural map $f^ast omega_(X') simeq and.big^n (f^ast Omega_(X'\/k)) arrow.r.long and.big^n Omega_(V\/k)=omega_V$. By _Adjoint Property_, we have a morphism $omega_(X') morph(phi,cat.mod(shf.o_(X'))) f_ast omega_V$, which gives a map $Gamma(X',omega_(X')) morph(phi^sharp,cat.mod(k)) Gamma(V,omega_V)$ of $k$-vector spaces.\
  (I) _Claim._ $phi^sharp$ is injective.
  - As $f$ is birational, it follows from _(I, 4.5)_ that $exists  U subset V$ open such that $f(U) subset X'$ is open and that $f:U morph(tilde.op,cat.sch) f(U)$ is an isomorphism. Thus, an isomorphism $omega_V|_U attach(arrow.l.long,t:tilde.op) omega_(X')|_(f(U))$ of sheaves.
  - Now, suppose $s in ops.ker phi^sharp$, we look at the following diagram:
  #align(center)[
    #diagram(cell-size: 11mm, $
      Gamma(X',omega_(X')) edge("dr", ↻, stroke: #none, label-side: #center, label-fill: #false) edge("r", (dot)|_(f(U)), "hook->") edge("d", phi^sharp, ->) & Gamma(f(U),omega_(X')) edge("dr", ↻, stroke: #none, label-side: #center, label-fill: #false) edge("r", tilde.op, ->) edge("d", phi_(f(U))^sharp, ->) & Gamma(f(U),omega_(X')|_(f(U))) edge("d", tilde.op, ->) \
      Gamma(V,omega_V) edge("r", (dot)|_U, "hook->") & Gamma(U,omega_V) edge("r", tilde.op, ->) & Gamma(U,omega_V|_U)
    $)
  ]
  Note that $omega_(X')$ and $omega_V$ are both invertible sheaves on an integral scheme, so the restriction maps $( dot )|_(f(U))$ and $( dot )|_U$ are both injective. Further, $phi_(f(U))^sharp$ is an isomorphism, so $s|_(f(U))=0$. But $f(U) subset X$ is an open dense subset (as $X$ is irreducible), whence $s=0$. Therefore, $phi^sharp$ is injective.
  (II) _Claim._ Let $X$ be nonsingular and $X'$ be projective, with a rational morphism $f:X to X'$ defined on the open set $V subset X$. Set $Z := X without V$, then $ops.codim(Z,X) >= 2$.
  - Note that $V != emptyset$, and $X$ is irreducible, so $ops.codim(Z,X) >= 1$.
  - Given any point $P in X$ with $ops.dim(shf.o_(X,P))=1$. As $X$ is nonsingular, $shf.o_(X,P)$ is a regular (Noetherian local domain), whence a DVR by _(I, 6.2)_.
  - Note that $f|_U:U morph(tilde.op,cat.top) f(U) subset X'$ is a homeomorphism, which must map the generic point $eta in U subset V$ to the generic point $eta' in X'$.
  - Recall that $f(P) in X'$ and an inclusion $k(f(P)) arrow.r.hook k(P)$ (induced by $shf.o_(X',f(P)) to shf.o_(V,P)$) determine the morphism $ops.spec k(P) morph(alpha,cat.sch) X'$ by _[2.7]_. Now, $X' morph(pi',cat.sch) ops.spec k$ is projective, thus, proper by _(4.9)_. It follows from the _Valuative Criterion (4.7)_ that $exists$ unique morphism $ops.spec shf.o_(X,P) morph(theta,cat.sch) X'$ such that the whole diagram below commute:
  #align(center)[
    #diagram(cell-size: 18mm, $
      ops.spec k(P) edge("r", alpha, ->) edge("d", i, "hook->") & X' edge("d", pi', ->, label-side: #left) edge("d", text("proper"), label-side: #right) \
      ops.spec shf.o_(X,P) edge("r", beta, ->) edge("ur", theta, ->, stroke: #(dash: "dashed")) & ops.spec k
    $)
  ]
  - *(?)* Further, note that $ops.spec shf.o_(X,P)$ is the intersection of all neighborhoods of $P$ in $X$, so we may choose a small $W in shf.n_P (X)$ and consider the morphism $theta':ops.spec shf.o_(X,P) inclusion(j,cat.sch) W morph(f,frak("Rat")) X'$. _Check._ $theta'$ is also compatible with the diagram, and hence, $theta=theta'$ by uniqueness. So, $f$ extends to a morphism in a neighborhood of $P$. But $V subset X$ is the largest defining domain, whence $P in V$.
  - _Conclusion._ We see that $Z$ contains no point with $ops.dim(shf.o_(X,P))=1$. Thus, by _[3.20(c)]_, we have $ops.codim(Z,X) >= 2$.
  (III) _Claim._ The map $Gamma(X,omega_X) arrow.r.long Gamma(V,omega_V)$ is bijective, and thus, a $k$-linear isomorphism.
  - The _injectivity_ part is easy since $omega_V simeq omega_X|_V$ is an invertible $shf.o_V$-module on the integral scheme $V subset X$. It suffices to show that: for any $x in X, exists$ open affine $U in shf.n_x (X)$ such that $Gamma(U,omega_X) arrow.r.long Gamma(U inter V,omega_V)$ is bijective.
  - Indeed, as $omega_X$ is invertible, we may choose a small neighborhood $U=ops.spec A$, on which $omega_X|_U simeq shf.o_X|_U$. Then, we must show that $Gamma(U, shf.o_X|_U) arrow.r.long Gamma(U inter V,omega_X|_(U inter V))$ is bijective. At this point, we may replace $(X,V)$ by $(U=ops.spec A,U inter V)$.
  - Since $X=ops.spec A$ is nonsingular, every local ring $A_idl.p$ ($idl.p in ops.spec A$) is a regular domain, thus, UFD and integrally closed. So, $A$ is also an integrally closed domain (AM, Ch3).
  - Now, from (II), $ops.codim(Z,X) >= 2$, so every prime ideal $idl.p lt.closed A$ with $ops.ht idl.p =1$ must be contained in $V$ (which gives the following first map). It follows that
  $
    Gamma(V, shf.o_X) arrow.r.hook inter.big_(ops.ht idl.p=1) A_idl.p attach(=, b: text("(6.3)"))A arrow.r.hook K(X)
  $
  as subrings of $K(X)$. Therefore, $A=Gamma(X, shf.o_X) arrow.r.hook Gamma(V, shf.o_X)$ is bijective.\
  (IV) Finally, combining the results above gives
  $
    p_g (X)=ops.dim(Gamma(X,omega_X), over:k)attach(=, b: text("(III)"))ops.dim(Gamma(V,omega_V), over:k)attach(>=, b: text("(I)"))ops.dim(Gamma(X',omega_(X')), over:k)=p_g (X').
  $
  We obtain the converse ($<=$) by symmetry, whence $p_g (X)=p_g (X')$.
]
// Hartshorne II.8, Definition D6
#definition(number: none)[
  Let $Y$ be a nonsingular subvariety of a nonsingular variety $X$ over $k$.
  - *(Conormal Sheaf).* The _conormal sheaf_ of $Y$ in $X$ is $shf.i \/ shf.i^2 in cat.mod(shf.o_Y)$ as in _(8.17)_.
  - *(Normal Sheaf).* The _normal sheaf_ of $Y$ in $X$ is the dual $shf.n_(Y\/X) := ( shf.i \/ shf.i^2)^or in cat.mod(shf.o_Y)$, which is locally free of rank $r= ops.codim(Y,X)$.
]
#remark[
  Note that the dual functor $( dot )^or =ops.hom(-,shf.o_Y,over:shf.o_Y)$ of locally free $shf.o_Y$-modules is an exact (contravariant) functor. Applying this to _(8.17)_, we have the following exact sequence:
  $
    0 arrow.l.long shf.n_(Y\/X) arrow.l.long shf.t_X times.o_(shf.o_X) shf.o_Y arrow.l.long shf.t_Y arrow.l.long 0.
  $
  Here, the middle term comes from the isomorphism
  $
    (Omega_(X\/Y) times.o_(shf.o_X) shf.o_Y)^or =(i^ast Omega)^or simeq i^ast (Omega_(X\/Y)^or )=i^ast shf.t_X= shf.t_X times.o_(shf.o_X) shf.o_Y,
  $
  where $i$ is the closed immersion $Y arrow.r.hook X$.
]
// Hartshorne II.8, Proposition 8.20
#proposition(number: "8.20")[
  Let $Y$ be a nonsingular subvariety of codimension $r$ in a nonsingular variety $X$ over $k$. Then, $omega_Y simeq omega_X times.o_(shf.o_X) and.big^r shf.n_(Y\/X)$ (as $shf.o_Y$-modules). In case $r=1$, consider $Y$ as a divisor, and let $shf.l in cat.mod(shf.o_X)$ be the associated invertible sheaf $shf.l (Y)$. Then, $omega_Y simeq omega_X times.o shf.l times.o shf.o_Y$.
]
#proof[
  (i) We have the exact sequence $0 to shf.i \/ shf.i^2 to Omega_(X\/k) times.o shf.o_Y to Omega_(Y\/k) to 0$ of $shf.o_Y$-modules from _(8.17)_. Then, we have
  #math.equation(block: true, numbering: (..nums) => [(⋆)])[
    $and.big^r (shf.i\/shf.i^2) times.o_(shf.o_Y) omega_Y
      &=and.big^r (shf.i\/shf.i^2) times.o_(shf.o_Y) and.big^(n-r) Omega_(Y\/k) \
      &isoBy(text("[5.16d]")) and.big^n (Omega_(X\/k) times.o_(shf.o_X) shf.o_Y) \
      &=and.big^n (i^ast Omega_(X\/k)) eqBy(text("[5.16e]")) i^ast (and.big^n Omega_(X\/k)) \
      &=omega_X times.o_(shf.o_X) shf.o_Y.$
  ]
  Thus, we see that
  $
    omega_X times.o_(shf.o_X) and.big^r shf.n_(Y\/X)
      &=omega_X times.o_(shf.o_X) and.big^r (shf.i\/shf.i^2)^or \
      &isoBy(text("(Check)")) omega_X times.o_(shf.o_X) (and.big^r shf.i\/shf.i^2)^or \
      &=(omega_X times.o_(shf.o_X) shf.o_Y) times.o_(shf.o_Y) (and.big^r shf.i\/shf.i^2)^or \
      &isoBy((star)) underbrace(and.big^r shf.i\/shf.i^2,text("invertible")) times.o_(shf.o_Y) (and.big^r shf.i\/shf.i^2)^or times.o_(shf.o_Y) omega_Y simeq omega_Y.
  $
  (ii) In the special case $r=1$, we have $shf.i_Y simeq shf.l^or$ by _(6.18)_. It follows that $shf.i \/ shf.i^2 simeq shf.l^or times.o_(shf.o_X) shf.o_Y$ and $shf.n_(Y\/X) simeq shf.l times.o_(shf.o_X) shf.o_Y$. Now, applying (i) gives the desired result.
]
#example(title: "8.20.1")[
  Let $X= sch.p_k^n$ ($n >= 0$). Then, $omega_X simeq shf.o_X (-n-1)$ and $p_g ( sch.p_k^n)=0$. Thus, every nonsingular projective _rational_ (i.e. birational to some $sch.p_k^n$) variety $X$ has genus $p_g (X)=0$. This allows us to demonstrate the existence of nonrational varieties in all dimensions.
]
#proof[
  We have the exact sequence $0 to Omega_(X\/k) to shf.o_X (-1)^(plus.o (n+1)) to shf.o_X to 0$ of locally free $shf.o_X$-modules by _(8.13)_. Note that $and.big^1 shf.o_X= shf.o_X$, so we see that
  $
    omega_X &simeq and.big^1 shf.o_X times.o_(shf.o_X) and.big^n Omega_(X\/k) \
      &isoBy(text("[5.16d]")) and.big^(n+1) shf.o_(X)(-1)^(plus.o (n+1)) \
      &isoBy(text("[5.16d]")) and.big^n shf.o_(X)(-1)^(plus.o n) times.o_(shf.o_X) and.big^1 shf.o_(X)(-1)=dots.c \
      &=lr((and.big^1 shf.o_(X)(-1)))^(times.o (n+1))=shf.o_(X)(-n-1).
  $
  Moreover, since $shf.o_X (l)$ has no global sections for $l<0$, it follows that $p_g ( sch.p_k^n)=0$ for every $n >= 0$.
]
