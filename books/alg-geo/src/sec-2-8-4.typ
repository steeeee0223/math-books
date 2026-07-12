#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "defs.typ": *

=== Applications

We define some invariants of nonsingular varieties.
#definition(number: none)[
  Let $X$ be a nonsingular variety over $k$ of dimension $n$.
  - *(Tangent Sheaf).* The _tangent sheaf_ of $X$ is % defined to be
  $TT_X := HHom_OO_X(op("Omega")_(X/k), OO_X) in MOD(OO_X)$, which is locally free of rank $n$.
  - *(Canonical Sheaf).* The _canonical sheaf_ of $X$ is defined to be $op("omega")_X := op("wedge")^op("nop")("Omega")_(X/k) in MOD(OO_X)$, which is an invertible sheaf.
  - *(Geometric Genus).* If, in addition, $X$ is projective, we define the _geometric genus_ of $X$ to be $p_g := op("dim")_op("kop")("Gamma")(X,op("omega")_X) >= 0$.
]
#theorem(number: "8.19")[
  Let $X$ and $X'$ be two birationally equivalent nonsingular projective varieties over $k$. Then, $p_g(X)=p_g(X')$.
]
#proof[
  Recall that for $X$ and $X'$ to be birationally equivalent, there are rational maps $X to X'$ and $X' to X$ which are inverses to each other. We consider the rational map $X to X'$ represented by the morphism $V arrow.r.long X'$, where $V subset X$ is the largest defining open set. By _(8.11)_, we have a map $f^ast op("Omega")_(X'/k) arrow.r.long op("Omega")_(V/k)$. Note that
  - $op("dim") X=op("dim") X'=n$.
  - $X$ and $X'$ being nonsingular yields that $op("Omega")_(V/k)=(op("Omega")_(X/k))|_V,\ op("Omega")_(X'/k)$, and thus $f^ast op("Omega")_(X'/k)$ are locally free sheaves of rank $n$.
  - _Check._ $op("omega")_X|_V=( op("wedge")^op("nop")("Omega")_(X/k))|_op("Vattach")(simeq, b: "text(\"(?)\")") op("wedge")^n(op("Omega")_(X/k)|_V)attach(simeq, b: "text(\"(8.10)\")") op("wedge")^op("nop")("Omega")_(V/k)=op("omega")_V$
  - _Check._ $f^ast op("omega")_(X')=f^ast ( op("wedge")^op("nop")("Omega")_(X'/k))attach(simeq, b: "text(\"(?)\")") op("wedge")^n(f^ast op("Omega")_(X'/k))$.
  Thus, this induces a natural map $f^ast op("omega")_(X') simeq op("wedge")^n(f^ast op("Omega")_(X'/k)) arrow.r.long op("wedge")^op("nop")("Omega")_(V/k)=op("omega")_V$. By _Adjoint Property_, we have a morphism $op("omega")_(X') arrow.r.long f_ast op("omega")_V$, which gives a map $op("Gamma")(X',op("omega")_(X')) arrow.r.long op("Gamma")(V,op("omega")_V)$ of $k$-vector spaces.\
  (I) _Claim._ $op("phi")^op("hash")$ is injective.
  - As $f$ is birational, it follows from _(I, 4.5)_ that $exists \ U subset V$ open such that $f(U) subset X'$ is open and that $f:U arrow.r.long f(U)$ is an isomorphism. Thus, an isomorphism $op("omega")_V|_U arrow.l.long op("omega")_(X')|_f(U)$ of sheaves.
  - Now, suppose $s in Ker op("phi")^op("hash")$, we look at the following diagram:
  #remark[Diagram.]
  Note that $op("omega")_(X')$ and $op("omega")_V$ are both invertible sheaves on an integral scheme, so the restriction maps $( dot )|_f(U)$ and $( dot )|_U$ are both injective. Further, $op("phi")_(f(U))^op("hash")$ is an isomorphism, so $s|_f(U)=0$. But $f(U) subset X$ is an open dense subset (as $X$ is irreducible), whence $s=0$. Therefore, $op("phi")^op("hash")$ is injective.
  (II) _Claim._ Let $X$ be nonsingular and $X'$ be projective, with a rational morphism $f:X to X'$ defined on the open set $V subset X$. Set $Z := op("Xop")("setm in us") V$, then $codim (Z,X) >= 2$.
  - Note that $V != op("emptyset")$, and $X$ is irreducible, so $codim (Z,X) >= 1$.
  - Given any point $P in X$ with $op("dim") OO_X,P=1$. As $X$ is nonsingular, $OO_X,P$ is a regular (Noetherian local domain), whence a DVR by _(I, 6.2)_.
  - Note that $f|_U:U arrow.r.long f(U) subset X'$ is a homeomorphism, which must map the generic point $op("eta") in U subset V$ to the generic point $op("eta")' in X'$.
  - Recall that $f(P) in X'$ and an inclusion $k(f(P)) arrow.r.hook k(P)$ (induced by $OO_X',f(P) to OO_V,P$) determine the morphism $Spec k(P) arrow.r.long X'$ by _[2.7]_. Now, $X' arrow.r.long Spec k$ is projective, thus, proper by _(4.9)_. It follows from the _Valuative Criterion (4.7)_ that $exists$ unique morphism $Spec OO_X,P arrow.r.long X'$ such that the whole diagram below commute:
  #remark[Diagram.]
  - *(?)* Further, note that $Spec OO_X,P$ is the intersection of all neighborhoods of $P$ in $X$, so we may choose a small $W in NN_P(X)$ and consider the morphism $op("theta")':Spec OO_X,P arrow.r.hook W arrow.r.long X'$. _Check._ $op("theta")'$ is also compatible with the diagram, and hence, $op("theta")=op("theta")'$ by uniqueness. So, $f$ extends to a morphism in a neighborhood of $P$. But $V subset X$ is the largest defining domain, whence $P in V$.
  - _Conclusion._ We see that $Z$ contains no point with $op("dim") OO_X,P=1$. Thus, by _[3.20(c)]_, we have $codim (Z,X) >= 2$.
  (III) _Claim._ The map $op("Gamma")(X,op("omega")_X) arrow.r.long op("Gamma")(V,op("omega")_V)$ is bijective, and thus, a $k$-linear isomorphism.
  - The _injectivity_ part is easy since $op("omega")_V simeq op("omega")_X|_V$ is an invertible $OO_V$-module on the integral scheme $V subset X$. It suffices to show that: for any $x in X,\ exists$ open affine $U in NN_x(X)$ such that $op("Gamma")(U,op("omega")_X) arrow.r.long op("Gamma")(op("Uop")("cap") V,op("omega")_V)$ is bijective.
  - Indeed, as $op("omega")_X$ is invertible, we may choose a small neighborhood $U=Spec A$, on which $op("omega")_X|_U simeq OO_X|_U$. Then, we must show that $op("Gamma")(U, OO_X|_U) arrow.r.long op("Gamma")(op("Uop")("cap") V,op("omega")_X|_op("Uop")("cap") V)$ is bijective. At this point, we may replace $(X,V)$ by $(U=Spec A,op("Uop")("cap") V)$.
  - Since $X=Spec A$ is nonsingular, every local ring $A_pp$ ($pp in Spec A$) is a regular domain, thus, UFD and integrally closed. So, $A$ is also an integrally closed domain (AM, Ch3).
  - Now, from (II), $codim (Z,X) >= 2$, so every prime ideal $pp op("triangleleft") A$ with $Ht pp =1$ must be contained in $V$ (which gives the following first map). It follows that
  $
    op("Gamma")(V, OO_X) arrow.r.hook op("cap")_Ht pp =1A_pp attach(=, b: "text(\"(6.3)\")")A arrow.r.hook K(X)
  $
  as subrings of $K(X)$. Therefore, $A=op("Gamma")(X, OO_X) arrow.r.hook op("Gamma")(V, OO_X)$ is bijective.\
  (IV) Finally, combining the results above gives
  $
    p_g(X)=op("dim")_op("kop")("Gamma")(X,op("omega")_X)attach(=, b: "text(\"(III)\")")op("dim")_op("kop")("Gamma")(V,op("omega")_V)attach(>=, b: "text(\"(I)\")")op("dim")_op("kop")("Gamma")(X',op("omega")_(X'))=p_g(X').
  $
  We obtain the converse ($<=$) by symmetry, whence $p_g(X)=p_g(X')$.
]
#definition(number: none)[
  Let $Y$ be a nonsingular subvariety of a nonsingular variety $X$ over $k$.
  - *(Conormal Sheaf).* The _conormal sheaf_ of $Y$ in $X$ is $II / II^2 in MOD(OO_Y)$ as in _(8.17)_.
  - *(Normal Sheaf).* The _normal sheaf_ of $Y$ in $X$ is the dual $NN_Y/X := ( II / II^2)^op("vee") in MOD(OO_Y)$, which is locally free of rank $r= codim (Y,X)$.
]
#remark[
  Note that the dual functor $( dot )^op("vee") =op("Hom")_(OO_Y)(-, OO_Y)$ of locally free $OO_Y$-modules is an exact (contravariant) functor. Applying this to _(8.17)_, we have the following exact sequence:
  $
    0 arrow.l.long NN_Y/X arrow.l.long TT_X times.o_OO_X OO_Y arrow.l.long TT_Y arrow.l.long 0.
  $
  Here, the middle term comes from the isomorphism
  $
    (op("Omega")_(X/Y) times.o_OO_X OO_Y)^op("vee") =(i^ast op("Omega"))^op("vee") simeq i^ast (op("Omega")_(X/Y)^op("vee") )=i^ast TT_X= TT_X times.o_OO_X OO_Y,
  $
  where $i$ is the closed immersion $Y arrow.r.hook X$.
]
#proposition(number: "8.20")[
  Let $Y$ be a nonsingular subvariety of codimension $r$ in a nonsingular variety $X$ over $k$. Then, $op("omega")_Y simeq op("omega")_X times.o_OO_X op("wedge")^r NN_Y/X$ (as $OO_Y$-modules). In case $r=1$, consider $Y$ as a divisor, and let $LL in MOD(OO_X)$ be the associated invertible sheaf $LL (Y)$. Then, $op("omega")_Y simeq op("omega")_X times.o LL times.o OO_Y$.
]
#proof[
  (i) We have the exact sequence $0 to II / II^2 to op("Omega")_(X/k) times.o OO_Y to op("Omega")_(Y/k) to 0$ of $OO_Y$-modules from _(8.17)_. Then, we have
  $op("wedge")^r( II / II^2) times.o_OO_op("Yop")("omega")_Y &= op("wedge")^r( II / II^2) times.o_OO_Y op("wedge")^n-op("rop")("Omega")_(Y/k)attach(simeq, b: "text(\"[5.16d]\")") op("wedge")^n(op("Omega")_(X/k) times.o_OO_X OO_Y)\ &= op("wedge")^n(i^ast op("Omega")_(X/k))attach(=, b: "text(\"[5.16e]\")")i^ast ( op("wedge")^n op("Omega")_(X/k))=op("omega")_X times.o_OO_X OO_Y. op("tag")$op("star")$$
  Thus, we see that
  $
    op("omega")_X times.o_OO_X op("wedge")^r NN_Y/X &=op("omega")_X times.o_OO_X op("wedge")^r( II / II^2)^op("vee") attach(simeq, b: "text(\"(Check)\")")op("omega")_X times.o_OO_X( op("wedge")^r II / II^2)^op("vee") \ &=(op("omega")_X times.o_OO_X OO_Y) times.o_OO_Y( op("wedge")^r II / II^2)^op("vee") \ &attach(simeq, b: "(op(\"star\"))")op("underbrace") op("wedge")^r II / II^2_text("invertible") times.o_OO_Y ( op("wedge")^r II / II^2)^op("vee") times.o_OO_op("Yop")("omega")_Y simeq op("omega")_Y.
  $
  (ii) In the special case $r=1$, we have $II_Y simeq LL^op("vee")$ by _(6.18)_. It follows that $II / II^2 simeq LL^op("vee") times.o_OO_X OO_Y$ and $NN_Y/X simeq LL times.o_OO_X OO_Y$. Now, applying (i) gives the desired result.
]
#example(title: "8.20.1")[
  Let $X= PP_k^n$ ($n >= 0$). Then, $op("omega")_X simeq OO_X(-n-1)$ and $p_g( PP_k^n)=0$. Thus, every nonsingular projective _rational_ (i.e. birational to some $PP_k^n$) variety $X$ has genus $p_g(X)=0$. This allows us to demonstrate the existence of nonrational varieties in all dimensions.
]
#proof[
  We have the exact sequence $0 to op("Omega")_(X/k) to OO_X(-1)^(plus.o (n+1)) to OO_X to 0$ of locally free $OO_X$-modules by _(8.13)_. Note that $op("wedge")^1 OO_X= OO_X$, so we see that
  $
    op("omega")_X & simeq op("wedge")^1 OO_X times.o_OO_X op("wedge")^n op("Omega")_(X/k)attach(simeq, b: "text(\"[5.16d]\")") op("wedge")^n+1 OO_X(-1)^(plus.o (n+1))\ &attach(simeq, b: "text(\"[5.16d]\")") op("wedge")^n OO_X(-1)^(plus.o n) times.o_OO_X op("wedge")^1 OO_X(-1)= dots.c \ &=op("Big")( op("wedge")^1 OO_X(-1)op("Big"))^(times.o (n+1))= OO_X(-n-1).
  $
  Moreover, since $OO_X(l)$ has no global sections for $l<0$, it follows that $p_g( PP_k^n)=0$ for every $n >= 0$.
]
