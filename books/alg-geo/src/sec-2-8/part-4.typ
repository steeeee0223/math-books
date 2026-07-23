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
  - *(Tangent Sheaf).* The _tangent sheaf_ of $X$ is % defined to be
  $shf.t_X := shf.hom_shf.o_X (op("Omega")_(X\/k), shf.o_X) in cat.mod(shf.o_X)$, which is locally free of rank $n$.
  - *(Canonical Sheaf).* The _canonical sheaf_ of $X$ is defined to be $op("omega")_X := op("wedge")^op("nop") ("Omega")_(X\/k) in cat.mod(shf.o_X)$, which is an invertible sheaf.
  - *(Geometric Genus).* If, in addition, $X$ is projective, we define the _geometric genus_ of $X$ to be $p_g := ops.dim(("Gamma")(X,op("omega")_X), over: op("kop")) >= 0$.
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
  Recall that for $X$ and $X'$ to be birationally equivalent, there are rational maps $X to X'$ and $X' to X$ which are inverses to each other. We consider the rational map $X to X'$ represented by the morphism $V arrow.r.long X'$, where $V subset X$ is the largest defining open set. By _(8.11)_, we have a map $f^ast op("Omega")_(X'\/k) arrow.r.long op("Omega")_(V\/k)$. Note that
  - $ops.dim(X)=ops.dim(X')=n$.
  - $X$ and $X'$ being nonsingular yields that $op("Omega")_(V\/k)=(op("Omega")_(X\/k))|_V,\ op("Omega")_(X'\/k)$, and thus $f^ast op("Omega")_(X'\/k)$ are locally free sheaves of rank $n$.
  - _Check._ $op("omega")_X|_V=( op("wedge")^op("nop") ("Omega")_(X\/k))|_op("Vattach") (simeq, b: "text(\"(?)\")") op("wedge")^n (op("Omega")_(X\/k)|_V)attach(simeq, b: "text(\"(8.10)\")") op("wedge")^op("nop") ("Omega")_(V\/k)=op("omega")_V$
  - _Check._ $f^ast op("omega")_(X')=f^ast ( op("wedge")^op("nop") ("Omega")_(X'\/k))attach(simeq, b: "text(\"(?)\")") op("wedge")^n (f^ast op("Omega")_(X'\/k))$.
  Thus, this induces a natural map $f^ast op("omega")_(X') simeq op("wedge")^n (f^ast op("Omega")_(X'\/k)) arrow.r.long op("wedge")^op("nop") ("Omega")_(V\/k)=op("omega")_V$. By _Adjoint Property_, we have a morphism $op("omega")_(X') arrow.r.long f_ast op("omega")_V$, which gives a map $op("Gamma")(X',op("omega")_(X')) arrow.r.long op("Gamma")(V,op("omega")_V)$ of $k$-vector spaces.\
  (I) _Claim._ $op("phi")^op("hash")$ is injective.
  - As $f$ is birational, it follows from _(I, 4.5)_ that $exists \ U subset V$ open such that $f(U) subset X'$ is open and that $f:U arrow.r.long f(U)$ is an isomorphism. Thus, an isomorphism $op("omega")_V|_U arrow.l.long op("omega")_(X')|_f (U)$ of sheaves.
  - Now, suppose $s in ops.ker op("phi")^op("hash")$, we look at the following diagram:
  #remark[Diagram.]
  Note that $op("omega")_(X')$ and $op("omega")_V$ are both invertible sheaves on an integral scheme, so the restriction maps $( dot )|_f (U)$ and $( dot )|_U$ are both injective. Further, $op("phi")_(f(U))^op("hash")$ is an isomorphism, so $s|_f (U)=0$. But $f(U) subset X$ is an open dense subset (as $X$ is irreducible), whence $s=0$. Therefore, $op("phi")^op("hash")$ is injective.
  (II) _Claim._ Let $X$ be nonsingular and $X'$ be projective, with a rational morphism $f:X to X'$ defined on the open set $V subset X$. Set $Z := op("Xop")("setm in us") V$, then $ops.codim(Z,X) >= 2$.
  - Note that $V != op("emptyset")$, and $X$ is irreducible, so $ops.codim(Z,X) >= 1$.
  - Given any point $P in X$ with $ops.dim(shf.o_X),P=1$. As $X$ is nonsingular, $shf.o_X,P$ is a regular (Noetherian local domain), whence a DVR by _(I, 6.2)_.
  - Note that $f|_U:U arrow.r.long f(U) subset X'$ is a homeomorphism, which must map the generic point $op("eta") in U subset V$ to the generic point $op("eta")' in X'$.
  - Recall that $f(P) in X'$ and an inclusion $k(f(P)) arrow.r.hook k(P)$ (induced by $shf.o_X',f(P) to shf.o_V,P$) determine the morphism $ops.spec k(P) arrow.r.long X'$ by _[2.7]_. Now, $X' arrow.r.long ops.spec k$ is projective, thus, proper by _(4.9)_. It follows from the _Valuative Criterion (4.7)_ that $exists$ unique morphism $ops.spec shf.o_X,P arrow.r.long X'$ such that the whole diagram below commute:
  #remark[Diagram.]
  - *(?)* Further, note that $ops.spec shf.o_X,P$ is the intersection of all neighborhoods of $P$ in $X$, so we may choose a small $W in shf.n_P (X)$ and consider the morphism $op("theta")':ops.spec shf.o_X,P arrow.r.hook W arrow.r.long X'$. _Check._ $op("theta")'$ is also compatible with the diagram, and hence, $op("theta")=op("theta")'$ by uniqueness. So, $f$ extends to a morphism in a neighborhood of $P$. But $V subset X$ is the largest defining domain, whence $P in V$.
  - _Conclusion._ We see that $Z$ contains no point with $ops.dim(shf.o_X),P=1$. Thus, by _[3.20(c)]_, we have $ops.codim(Z,X) >= 2$.
  (III) _Claim._ The map $op("Gamma")(X,op("omega")_X) arrow.r.long op("Gamma")(V,op("omega")_V)$ is bijective, and thus, a $k$-linear isomorphism.
  - The _injectivity_ part is easy since $op("omega")_V simeq op("omega")_X|_V$ is an invertible $shf.o_V$-module on the integral scheme $V subset X$. It suffices to show that: for any $x in X,\ exists$ open affine $U in shf.n_x (X)$ such that $op("Gamma")(U,op("omega")_X) arrow.r.long op("Gamma")(op("Uop")("cap") V,op("omega")_V)$ is bijective.
  - Indeed, as $op("omega")_X$ is invertible, we may choose a small neighborhood $U=ops.spec A$, on which $op("omega")_X|_U simeq shf.o_X|_U$. Then, we must show that $op("Gamma")(U, shf.o_X|_U) arrow.r.long op("Gamma")(op("Uop")("cap") V,op("omega")_X|_op("Uop") ("cap") V)$ is bijective. At this point, we may replace $(X,V)$ by $(U=ops.spec A,op("Uop")("cap") V)$.
  - Since $X=ops.spec A$ is nonsingular, every local ring $A_idl.p$ ($idl.p in ops.spec A$) is a regular domain, thus, UFD and integrally closed. So, $A$ is also an integrally closed domain (AM, Ch3).
  - Now, from (II), $ops.codim(Z,X) >= 2$, so every prime ideal $idl.p op("triangleleft") A$ with $ops.ht idl.p =1$ must be contained in $V$ (which gives the following first map). It follows that
  $
    op("Gamma")(V, shf.o_X) arrow.r.hook op("cap")_ops.ht idl.p =1A_idl.p attach(=, b: "text(\"(6.3)\")")A arrow.r.hook K(X)
  $
  as subrings of $K(X)$. Therefore, $A=op("Gamma")(X, shf.o_X) arrow.r.hook op("Gamma")(V, shf.o_X)$ is bijective.\
  (IV) Finally, combining the results above gives
  $
    p_g (X)=ops.dim(("Gamma")(X,op("omega")_X), over: op("kop"))attach(=, b: "text(\"(III)\")")ops.dim(("Gamma")(V,op("omega")_V), over: op("kop"))attach(>=, b: "text(\"(I)\")")ops.dim(("Gamma")(X',op("omega")_(X')), over: op("kop"))=p_g (X').
  $
  We obtain the converse ($<=$) by symmetry, whence $p_g (X)=p_g (X')$.
]
// Hartshorne II.8, Definition D6
#definition(number: none)[
  Let $Y$ be a nonsingular subvariety of a nonsingular variety $X$ over $k$.
  - *(Conormal Sheaf).* The _conormal sheaf_ of $Y$ in $X$ is $shf.i \/ shf.i^2 in cat.mod(shf.o_Y)$ as in _(8.17)_.
  - *(Normal Sheaf).* The _normal sheaf_ of $Y$ in $X$ is the dual $shf.n_Y\/X := ( shf.i \/ shf.i^2)^op("vee") in cat.mod(shf.o_Y)$, which is locally free of rank $r= ops.codim(Y,X)$.
]
#remark[
  Note that the dual functor $( dot )^op("vee") =op("Hom")_(shf.o_Y) (-, shf.o_Y)$ of locally free $shf.o_Y$-modules is an exact (contravariant) functor. Applying this to _(8.17)_, we have the following exact sequence:
  $
    0 arrow.l.long shf.n_Y\/X arrow.l.long shf.t_X times.o_shf.o_X shf.o_Y arrow.l.long shf.t_Y arrow.l.long 0.
  $
  Here, the middle term comes from the isomorphism
  $
    (op("Omega")_(X\/Y) times.o_shf.o_X shf.o_Y)^op("vee") =(i^ast op("Omega"))^op("vee") simeq i^ast (op("Omega")_(X\/Y)^op("vee") )=i^ast shf.t_X= shf.t_X times.o_shf.o_X shf.o_Y,
  $
  where $i$ is the closed immersion $Y arrow.r.hook X$.
]
// Hartshorne II.8, Proposition 8.20
#proposition(number: "8.20")[
  Let $Y$ be a nonsingular subvariety of codimension $r$ in a nonsingular variety $X$ over $k$. Then, $op("omega")_Y simeq op("omega")_X times.o_shf.o_X op("wedge")^r shf.n_Y\/X$ (as $shf.o_Y$-modules). In case $r=1$, consider $Y$ as a divisor, and let $shf.l in cat.mod(shf.o_X)$ be the associated invertible sheaf $shf.l (Y)$. Then, $op("omega")_Y simeq op("omega")_X times.o shf.l times.o shf.o_Y$.
]
#proof[
  (i) We have the exact sequence $0 to shf.i \/ shf.i^2 to op("Omega")_(X\/k) times.o shf.o_Y to op("Omega")_(Y\/k) to 0$ of $shf.o_Y$-modules from _(8.17)_. Then, we have
  $op("wedge")^r ( shf.i \/ shf.i^2) times.o_shf.o_op("Yop") ("omega")_Y &= op("wedge")^r ( shf.i \/ shf.i^2) times.o_shf.o_Y op("wedge")^n-op("rop")("Omega")_(Y\/k)attach(simeq, b: "text(\"[5.16d]\")") op("wedge")^n (op("Omega")_(X\/k) times.o_shf.o_X shf.o_Y)\ &= op("wedge")^n (i^ast op("Omega")_(X\/k))attach(=, b: "text(\"[5.16e]\")")i^ast ( op("wedge")^n op("Omega")_(X\/k))=op("omega")_X times.o_shf.o_X shf.o_Y. op("tag")$op("star")$$
  Thus, we see that
  $
    op("omega")_X times.o_shf.o_X op("wedge")^r shf.n_Y\/X &=op("omega")_X times.o_shf.o_X op("wedge")^r ( shf.i \/ shf.i^2)^op("vee") attach(simeq, b: "text(\"(Check)\")")op("omega")_X times.o_shf.o_X ( op("wedge")^r shf.i \/ shf.i^2)^op("vee") \ &=(op("omega")_X times.o_shf.o_X shf.o_Y) times.o_shf.o_Y ( op("wedge")^r shf.i \/ shf.i^2)^op("vee") \ &attach(simeq, b: "(op(\"star\"))")op("underbrace") op("wedge")^r shf.i \/ shf.i^2_text("invertible") times.o_shf.o_Y ( op("wedge")^r shf.i \/ shf.i^2)^op("vee") times.o_shf.o_op("Yop") ("omega")_Y simeq op("omega")_Y.
  $
  (ii) In the special case $r=1$, we have $shf.i_Y simeq shf.l^op("vee")$ by _(6.18)_. It follows that $shf.i \/ shf.i^2 simeq shf.l^op("vee") times.o_shf.o_X shf.o_Y$ and $shf.n_Y\/X simeq shf.l times.o_shf.o_X shf.o_Y$. Now, applying (i) gives the desired result.
]
#example(title: "8.20.1")[
  Let $X= sch.p_k^n$ ($n >= 0$). Then, $op("omega")_X simeq shf.o_X (-n-1)$ and $p_g ( sch.p_k^n)=0$. Thus, every nonsingular projective _rational_ (i.e. birational to some $sch.p_k^n$) variety $X$ has genus $p_g (X)=0$. This allows us to demonstrate the existence of nonrational varieties in all dimensions.
]
#proof[
  We have the exact sequence $0 to op("Omega")_(X\/k) to shf.o_X (-1)^(plus.o (n+1)) to shf.o_X to 0$ of locally free $shf.o_X$-modules by _(8.13)_. Note that $op("wedge")^1 shf.o_X= shf.o_X$, so we see that
  $
    op("omega")_X & simeq op("wedge")^1 shf.o_X times.o_shf.o_X op("wedge")^n op("Omega")_(X\/k)attach(simeq, b: "text(\"[5.16d]\")") op("wedge")^n+1 shf.o_X (-1)^(plus.o (n+1))\ &attach(simeq, b: "text(\"[5.16d]\")") op("wedge")^n shf.o_X (-1)^(plus.o n) times.o_shf.o_X op("wedge")^1 shf.o_X (-1)= dots.c \ &=op("Big")( op("wedge")^1 shf.o_X (-1)op("Big"))^(times.o (n+1))= shf.o_X (-n-1).
  $
  Moreover, since $shf.o_X (l)$ has no global sections for $l<0$, it follows that $p_g ( sch.p_k^n)=0$ for every $n >= 0$.
]
