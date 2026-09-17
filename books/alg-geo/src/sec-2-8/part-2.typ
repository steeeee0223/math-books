#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Sheaves of Differentials

Let $f:X morph("", cat.sch) Y$ be a morphism. Note that the diagonal morphism $Delta:X morph("", cat.sch) fiber(X,X,base:Y)$ is an immersion, i.e. $Delta$ gives an isomorphism of $X$ onto its image $Delta(X)$, which is a _locally closed subscheme_ of $fiber(X,X,base:Y)$, i.e. a closed subscheme of an open subset $W subset fiber(X,X,base:Y)$.
// Hartshorne II.8, Definition D3
#definition(title: "Sheaf of Relative Differentials")[
  Let $shf.i$ be the ideal sheaf of $Delta(X)$ corresponding to the closed immersion $Delta(X) morph(i, cat.sch) W$. We define the _sheaf of relative differentials_ of $X$ over $Y$ (via $f$) to be the sheaf $Omega_(X\/Y) := Delta^ast (shf.i \/ shf.i^2) in cat.mod(shf.o_X)$.
]
// Hartshorne II.8, Remark 8.9.1
#remark(title: "8.9.1")[
  Recall that $shf.i = ops.ker (shf.o_W attach(arrow.r.twohead, t: i^sharp) i_ast shf.o_(Delta(X))) in cat.qcoh(W)$ by _(5.9)_, so $shf.i \/ shf.i^2 in cat.qcoh(W)$. Now, we factorize $Delta$ into
  #align(center)[
    #diagram(cell-size: 15mm, $
      & W edge("dr", text("open"), "hook->") & \
      X edge("ur", tildeOf(Delta), ->) edge("rr", Delta, ->) & edge("u", ↻, stroke: #none, label-side: #center, label-fill: #false) & fiber(X,X,base:Y)
    $)
  ]
  Now, we have
  $
    Omega_(X\/Y)=Delta^ast (shf.i \/ shf.i^2)=tildeOf(Delta)^ast (shf.i \/ shf.i^2) attach(in, b: text("(5.8)")) cat.qcoh(X).
  $
  Further, if $Y$ is a Noetherian scheme and $f$ is of finite type, then $fiber(X,X,base:Y)$ is also Noetherian, whence $Omega_(X\/Y) in cat.coh(X)$.
]
// Hartshorne II.8, Remark 8.9.2
#remark(title: "8.9.2")[
  If $U=ops.spec A$ is an open affine of $Y$, we choose an open affine $V=ops.spec B$ of $X$ for which $f(V) subset U$, then we have $Omega_(V\/U) simeq tildeOf(Omega_(B\/A))$. This shows that we may define $Omega_(X\/Y)$ by covering $X$ and $Y$ with open affines $V$ and $U$, respectively, and gluing the corresponding sheaves $tildeOf(Omega_(B\/A))$. Now, the deriviation $d in ops.der_A (B,Omega_(B\/A))$ patch together to give a map $d: shf.o_X morph("", cat.ab_X) Omega_(X\/Y)$, which is a deriviation of the local rings at each point.
]
#proof[
  Note that $fiber(V,V,base:U) simeq ops.spec (tensor(B,B,over:A))$ is an open affine subset of $fiber(X,X,base:Y)$, and that $Delta:X morph(tilde.op, cat.top) Delta(X)$ is a homoemorphism onto to its image. Further, $f|_V$ is separated by _(4.1)_, so we have the diagram:
  #align(center)[
    #diagram(cell-size: 14mm, $
      B & V edge("dr", ↻, stroke: #none, label-side: #center, label-fill: #false) edge("r", Delta, ->) edge("d", Delta_(V\/U), ->, label-side: #left) edge("d", text("closed"), label-side: #right) & Delta(V) edge("d", simeq, ->) \
      tensor(B,B,over:A) edge("u", phi, ->>) & fiber(V,V,base:U) & Delta(X) inter (fiber(V,V,base:U)) edge("l", j, "hook->", label-side: #left) edge("l", text("closed"), label-side: #right)
    $)
  ]
  From _(5.10)_, the closed subscheme $Delta(V) subset fiber(V,V,base:U)$ is uniquely determined by an ideal $I lt.closed tensor(B,B,over:A)$. Moreover, $shf.i_(Delta(V))=ops.ker j^sharp=tildeOf(ops.ker phi)$ is the ideal sheaf of $Delta(V)$ in $fiber(V,V,base:U)$, it follows from _(5.9)_ that its defining ideal must be $I=ops.ker phi$, i.e. $shf.i_(Delta(V))=tildeOf(I)$. Therefore,
  $
    Omega_(V\/U) &= Delta_(V\/U)^ast (shf.i_(Delta(V))\/shf.i_(Delta(V))^2) = Delta_(V\/U)^ast tildeOf(I\/I^2) \
    &isoBy(text("(5.2)")) tildeOf(tensor(I\/I^2,B,over:tensor(B,B,over:A))) = attach(tildeOf(I\/I^2), bl: B) eqBy(text("(8.1)")) tildeOf(Omega_(B\/A)).
  $
]
// Hartshorne II.8, Proposition 8.10
#proposition(number: "8.10")[
  Given a morphism $X morph(f,cat.sch) Y$, and let $X'=fiber(X,Y',base:Y) morph(f',cat.sch) Y'$ be the base extension of $f$ through $Y' morph(g,cat.sch) Y$, i.e. the fibre square
  #align(center)[
    #diagram(cell-size: 15mm, $
      fiber(X,Y',base:Y) edge("r", f', ->) edge("d", g', ->) edge("dr", □, stroke: #none, label-side: #center, label-fill: #false) & Y' edge("d", g, ->) \
      X edge("r", f, ->) & Y
    $)
  ]
  Then, we have $Omega_(X'\/Y') simeq (g')^ast Omega_(X\/Y)$.
]
#proof[
  From _(8.9.2)_, the question is local, so we may reduce to the affine case. Suppose $Y, Y', X, X'$ are the spectra of the rings $A, A', B, B'$, respectively. Then $B' simeq tensor(B,A',over:A)$. Thus, we have
  $
    Omega_(X'\/Y') &isoBy(text("(8.9.2)")) tildeOf(Omega_(B'\/A')) isoBy(text("(8.2)")) tildeOf(tensor(Omega_(B\/A),B',over:B)) \
    &isoBy(text("(5.2e)")) (g')^ast tildeOf(Omega_(B\/A)) isoBy(text("(8.9.2)")) (g')^ast Omega_(X\/Y).
  $
]
// Hartshorne II.8, Proposition 8.11
#proposition(number: "8.11")[
  Given morphisms $X morph(f,cat.sch) Y morph(g,cat.sch) Z$. Then there is an exact sequence of $shf.o_X$-modules:
  $
    f^ast Omega_(Y\/Z) to Omega_(X\/Z) to Omega_(X\/Y) to 0.
  $
]
#proof[
  From _(8.9.2)_, the question is local, so we may reduce to the affine case. Suppose $Z, Y, X$ are the spectra of the rings $A, B, C$, respectively. By _(8.3)_, we have the exact sequence $tensor(Omega_(B\/A),C,over:B) to Omega_(C\/A) to Omega_(C\/B) to 0$ of $C$-modules. Taking the exact functor $M mapsto tildeOf(M)$ gives
  #align(center)[
    #diagram(cell-size: 8mm, $
      f^ast tildeOf(Omega_(B\/A)) edge("r", text("(5.2)"), "=") edge("d", "=") & tildeOf(tensor(Omega_(B\/A),C,over:B)) edge("r", ->) & tildeOf(Omega_(C\/A)) edge("r", ->) edge("d", "=") & tildeOf(Omega_(C\/B)) edge("r", ->) edge("d", "=") & 0 \
      f^ast Omega_(Y\/Z) edge("rr", ->) & & Omega_(X\/Z) edge("r", ->) & Omega_(X\/Y) edge("r", ->) & 0
    $)
  ]
  an exact sequence of $shf.o_X$-modules.
]
// Hartshorne II.8, Proposition 8.12
#proposition(number: "8.12")[
  Given a morphism $X morph(f,cat.sch) Y$, and let $Z subset X$ be a closed subscheme with its ideal sheaf $shf.i$. Then there is an exact sequence of $shf.o_Z$-modules:
  $
    shf.i \/ shf.i^2 morph(delta,"") tensor(Omega_(X\/Y),shf.o_Z) to Omega_(Z\/Y) to 0.
  $
]
#proof[
  From _(8.9.2)_, the question is local, so we may reduce to the affine case. Suppose $Y, X$ are the spectra of the rings $A, B$, respectively. Now, the closed subscheme $Z subset X$ is determined by an ideal $I lt.closed B$, for which $Z simeq ops.spec B\/I$ and $shf.i simeq tildeOf(I)$ by _(5.10)_. Now, _(8.4)_ gives the exact sequence $I\/I^2 morph(delta,"") tensor(Omega_(B\/A),C,over:B) to Omega_(C\/A) to 0$ of $C=B\/I$-modules. Taking the exact functor $M mapsto tildeOf(M)$ gives
  #align(center)[
    #diagram(cell-size: 12mm, $
      tildeOf(I\/I^2) edge("r", ->) edge("d", "=") & tildeOf(tensor(Omega_(B\/A),C,over:B)) edge("r", ->) edge("d", "=") & tildeOf(Omega_(C\/A)) edge("r", ->) edge("d", "=") & 0 \
      shf.i\/shf.i^2 edge("r", ->) & tensor(Omega_(X\/Z),shf.o_Z,over:shf.o_X) edge("r", ->) & Omega_(Z\/Y) edge("r", ->) & 0
    $)
  ]
  an exact sequence of $shf.o_Z$-modules.
]
#example(title: "8.12.1")[
  If $X=sch.a_Y^n$ for any scheme $Y$, then $Omega_(X\/Y) in cat.mod(shf.o_X)$ is a free module of rank $n$, generated by global sections ${d x_i}_(i=1)^n$.
]
#proof[
  Consider the fibre square
  #align(center)[
    #diagram(cell-size: 15mm, $
      X=fiber(sch.a_bb("Z")^n,Y,base:bb("Z")) edge("r", f, ->) edge("d", g, ->) edge("dr", □, stroke: #none, label-side: #center, label-fill: #false) & Y edge("d", ->) \
      Z=sch.a_bb("Z")^n edge("r", ->) & ops.spec bb("Z")=S
    $)
  ]
  We have
  $
    Omega_(X\/Y) isoBy(text("(8.10)")) g^ast Omega_(Z\/S) isoBy(text("(8.9.2)")) g^ast tildeOf(Omega_(bb("Z")[x_1,dots.c,x_n]\/bb("Z"))).
  $
  Further, $tildeOf(Omega_(bb("Z")[x_1,dots.c,x_n]\/bb("Z")))$ is a free $shf.o_Z$-module generated by the global sections ${d x_i}_(i=1)^n$, whence $Omega_(X\/Y)$ is a free $shf.o_X$-module generated by the global sections ${g^ast d x_i}_(i=1)^n$.
]
// Hartshorne II.8, Theorem 8.13
#theorem(number: "8.13")[
  Let $A in cat.ring, Y=ops.spec A$, and $X=sch.p_A^n$. Then there is an exact sequence of $shf.o_X$-modules:
  $
    0 to Omega_(X\/Y) to shf.o_(X)(-1)^(plus.o (n+1)) to shf.o_X to 0.
  $
]
#proof[
  (I) Construct the exact sequence.
  - Write $S=A[x_0,dots.c,x_n]$, then $X=ops.proj S$. Let $E := S(-1)^(plus.o (n+1)) in cat.gr cat.mod(S)$ be the free graded module with an $S$-basis ${e_i}_(i=0)^n$ where $e_i=(0,dots.c,attach(limits(1),b:i "th"),dots.c,0) in S_0^(plus.o (n+1))=E_1$.
  - For each $x_i in S_1$, we have a natural graded homomorphism
  $
    alpha_i:S(-1) to S, quad 1 in S(-1)_1 mapsto x_i in S_1.
  $
  Then $alpha := alpha_0 plus.o dots.c plus.o alpha_n$ gives a graded homomorphism $E to S$. Let $M := ops.ker alpha$, then we have the exact sequence $0 to M to E to S$ of graded $S$-modules. By taking the functor $N mapsto tildeOf(N)$, it induces an exact sequence of $shf.o_X$-modules:
  $
    0 to tildeOf(M) to tildeOf(E)=shf.o_(X)(-1)^(plus.o (n+1)) to shf.o_X to 0.
  $
  - Note that the map $alpha$ is NOT surjective (as $E_0=S_(-1)^(plus.o (n+1))=emptyset$), but it is surjective in $E_(>=1) to S_(>=1)$, so the corresponding sheaf map $tildeOf(E) to tildeOf(S)$ is still surjective!

  (II) _Claim._ $tildeOf(M) simeq Omega_(X\/Y)$ as $shf.o_X$-modules.
  - First, we localize at each $x_i$. Then, $alpha_(x_i):E_(x_i) to S_(x_i)$ is clearly a surjective graded  homomorphism of free $S_(x_i)$-modules. We see in the following that $M_(x_i)$ is also a free $S_(x_i)$-modules of rank $n$ with an $S_(x_i)$-basis ${frac(e_j x_i-e_i x_j,x_i):j != i}$. Obviously, we have $alpha_(x_i)(frac(e_j x_i-e_i x_j,x_i))=frac(x_j x_i-x_i x_j,x_i)=0$ for every $j != i$. On the other hand, suppose $s in M_(x_i)=ops.ker alpha_(x_i)$, we write $s := sum_(j != i) frac(a_j e_j,x_i^k)$ ($a_j in S$), which sends via $alpha_(x_i)$ to $sum_(j != i) frac(a_j e_j,x_i^k)=0$. So, $exists l>0$ for which $x_i^l sum_(j != i) a_j x_j=0$. Now,
  we obtain
  $
    s &= frac(sum_(j != i) a_j e_j x_i,x_i^(k+1))-underbrace(frac(e_i sum_(j != i) a_j x_j,x_i^(k+1)),=0) \
    &= sum_(j != i) frac(a_j,x_i^k) lr((frac(e_j x_i-e_i x_j,x_i))) in S_(x_i) spn lr({frac(e_j x_i-e_i x_j,x_i):j != i}).
  $
  Moreover, it is easy to check that they are $S_(x_i)$-linearly independent, whence they form a basis over $S_(x_i)$.
  - Let $U_i := D_+(x_i)$ for each $i$. Now, it follows from the previous discussion that $tildeOf(M)|_(U_i) simeq tildeOf(M_((x_i)))$ is a free $shf.o_X|_(U_i)$-module generated by the sections ${frac(e_j x_i-e_i x_j,x_i^2):j != i}$ on $U_i$. (Here we need the additional factor $1/x_i$ since $x_i in S_1 subset E_2$, and $x_i^2 in S_1 dot E_2 subset E_3$).
  - For each $i$, we define a map $phi_i:Omega_(X\/Y)|_(U_i) to tildeOf(M)|_(U_i)$ as follows. Note that $U_i simeq ops.spec S_((x_i))=ops.spec A[frac(x_0,x_i),dots.c,frac(x_n,x_i)]$, so $Omega_(X\/Y)|_(U_i) simeq tildeOf(Omega_(S_((x_i)\/A)))$ is a free $shf.o_X|_(U_i)$-module generated by the global sections ${d(x_j/x_i):j != i}$ on $U_i$. Now, we define
  $
    beta_i:Omega_(S_((x_i))\/A) to M_((x_i)), quad d lr((frac(x_j,x_i))) mapsto frac(e_j x_i-e_i x_j,x_i^2),
  $
  which is thus an $S_((x_i))$-module isomorphism. From _[5.3]_, $beta_i$ corresponds to an isomorphism $phi_i:Omega_(X\/Y)|_(U_i) to tildeOf(M)|_(U_i)$ of free $shf.o_X|_(U_i)$-modules.
  - _Claim._ The isomorphisms $phi_i$ glue to give an isomorphism $Omega_(X\/Y) morph(phi,cat.mod(shf.o_X)) tildeOf(M)$.

  We look at the intersection $U_(i j)=U_i inter U_j simeq ops.spec S_((x_i x_j))$, we have $frac(x_k,x_i)=frac(x_k,x_j)frac(x_j,x_i)$ for any $k$, which gives
  $
    d lr((frac(x_k,x_i)))=frac(x_k,x_j) d lr((frac(x_j,x_i)))+frac(x_j,x_i) d lr((frac(x_k,x_j))) quad "in" Omega_(S_((x_i x_j))\/A).
  $
  (Here, $d=d_(S_(x_i x_j)\/A)$). Now, we have
  $
    phi_i|_(i j) lr((d lr((frac(x_k,x_i)))-frac(x_k,x_j) d lr((frac(x_j,x_i))))) &= frac(e_k x_i-e_i x_k,x_i^2)-frac(x_k,x_j)frac(e_j x_i-e_i x_j,x_i^2) \
    &= frac(x_j,x_i)frac(e_k x_j-e_j x_k,x_j^2) \
    &= phi_j|_(i j) lr((frac(x_j,x_i) d lr((frac(x_k,x_j)))))
  $
  for every $k$. Therefore, the ismorphisms ${phi_i}$ glue on ${U_i}$ and obtain such isomorphism $phi$.
]
