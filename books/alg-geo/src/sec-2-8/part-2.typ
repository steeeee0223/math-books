#import "@preview/theorion:0.4.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import cosmos.clouds: *
#show: show-theorion
#import "../defs.typ": *

=== Sheaves of Differentials

Let $f:X arrow.r.long Y$ be a morphism. Note that the diagonal morphism $op("Delta"):X arrow.r.long op("Xop")("times")_op("YX")$ is an immersion, i.e. $op("Delta")$ gives an isomorphism of $X$ onto its image $op("Delta")(X)$, which is a _locally closed subscheme_ of $op("Xop")("times")_op("YX")$, i.e. a closed subscheme of an open subset $W subset op("Xop")("times")_op("YX")$.
// Hartshorne II.8, Definition D3
#definition(title: "Sheaf of Relative Differentials")[
  Let $shf.i$ be the ideal sheaf of $op("Delta")(X)$ corresponding to the closed immersion $op("Delta")(X) arrow.r.long W$. We define the _sheaf of relative differentials_ of $X$ over $Y$ (via $f$) to be the sheaf $op("Omega")_(X\/Y) := op("Delta")^ast ( shf.i \/ shf.i^2) in cat.mod(shf.o_X)$.
]
// Hartshorne II.8, Remark 8.9.1
#remark(title: "8.9.1")[
  Recall that $shf.i = ops.ker ( shf.o_op("Wattach") (arrow.r.twohead, t: "i^ op(\"hash\")")i_ast shf.o_op("Delta") (X)) in cat.qcoh (W)$ by _(5.9)_, so $shf.i \/ shf.i^2 in cat.qcoh (W)$. Now, we factorize $op("Delta")$ into
  #remark[Diagram.]
  Now, we have
  $
    op("Omega")_(X\/Y)=op("Delta")^ast ( shf.i \/ shf.i^2)=op("widetilde")op("Delta")^ast ( shf.i \/ shf.i^2)attach(in, b: "text(\"(5.8)\")") cat.qcoh (X).
  $
  Further, if $Y$ is a Noetherian scheme and $f$ is of finite type, then $op("Xop")("times")_op("YX")$ is also Noetherian, whence $op("Omega")_(X\/Y) in cat.coh (X)$.
]
// Hartshorne II.8, Remark 8.9.2
#remark(title: "8.9.2")[
  If $U=ops.spec A$ is an open affine of $Y$, we choose an open affine $V=ops.spec B$ of $X$ for which $f(V) subset U$, then we have $op("Omega")_(V\/U) simeq (op("Omega")_(B\/A))op("widetilde")$. This shows that we may define $op("Omega")_(X\/Y)$ by covering $X$ and $Y$ with open affines $V$ and $U$, respectively, and gluing the corresponding sheaves $(op("Omega")_(B\/A))op("widetilde")$. Now, the deriviation $d in ops.der_A (B,op("Omega")_(B\/A))$ patch together to give a map $d: shf.o_X arrow.r.long op("Omega")_(X\/Y)$, which is a deriviation of the local rings at each point.
]
#proof[
  Note that $op("Vop")("times")_op("UV") simeq ops.spec (B times.o_op("AB"))$ is an open affine subset of $op("Xop")("times")_op("YX")$, and that $op("Delta"):X arrow.r.long op("Delta")(X)$ is a homoemorphism onto to its image. Further, $f|_V$ is separated by _(4.1)_, so we have the diagram:
  #remark[Diagram.]
  From _(5.10)_, the closed subscheme $op("Delta")(V) subset op("Vop")("times")_op("UV")$ is uniquely determined by an ideal $op("Iop")("triangleleft") B times.o_op("AB")$. Moreover, $shf.i_op("Delta") (V)= ops.ker j^op("hash") =( ops.ker op("phi"))op("widetilde")$ is the ideal sheaf of $op("Delta")(V)$ in $op("Vop")("times")_op("UV")$, it follows from _(5.9)_ that its defining ideal must be $I= ops.ker op("phi")$, i.e. $shf.i_op("Delta") (V)=op("widetilde")I$. Therefore,
  $
    op("Omega")_(V\/U)=op("Delta")^ast_V\/U( shf.i_op("Delta") (V)\/ shf.i_op("Delta") (V)^2)=op("Delta")_(V\/U)^ast (I\/I^2)op("widetilde")attach(simeq, b: "text(\"(5.2)\")")(I\/I^2 times.o_B times.o_op("ABB"))op("widetilde")=_B (I\/I^2)op("widetilde")attach(=, b: "text(\"(8.1)\")")(op("Omega")_(B\/A))op("widetilde").
  $
]
// Hartshorne II.8, Proposition 8.10
#proposition(number: "8.10")[
  Given a morphism $X arrow.r.long Y$, and let $X'=op("Xop")("times")_op("YY")' arrow.r.long Y'$ be the base extension of $f$ through $Y' arrow.r.long Y$, i.e. the fibre square
  #remark[Diagram.]
  Then, we have $op("Omega")_(X'\/Y') simeq (g')^ast \ op("Omega")_(X\/Y)$.
]
#proof[
  From _(8.9.2)_, the question is local, so we may reduce to the affine case. Suppose $Y,\ Y',\ X,\ X'$ are the spectra of the rings $A,\ A',\ B,\ B'$, respectively. Then $B' simeq B times.o_sch.a'$. Thus, we have
  $
    op("Omega")_(X'\/Y')attach(simeq, b: "text(\"(8.9.2)\")")(op("Omega")_(B'\/A'))op("widetilde")attach(simeq, b: "text(\"(8.2)\")")(op("Omega")_(B\/A) times.o_op("BB")')op("widetilde")attach(simeq, b: "text(\"(5.2e)\")")(g')^ast (op("Omega")_(B\/A))op("widetilde")attach(simeq, b: "text(\"(8.9.2)\")")(g')^ast \ op("Omega")_(X\/Y).
  $
]
// Hartshorne II.8, Proposition 8.11
#proposition(number: "8.11")[
  Given morphisms $X arrow.r.long Y arrow.r.long Z$. Then there is an exact sequence of $shf.o_X$-modules:
  $
    f^ast op("Omega")_(Y\/Z) arrow.r.long op("Omega")_(X\/Z) arrow.r.long op("Omega")_(X\/Y) arrow.r.long 0.
  $
]
#proof[
  From _(8.9.2)_, the question is local, so we may reduce to the affine case. Suppose $Z,\ Y,\ X$ are the spectra of the rings $A,\ B,\ C$, respectively. By _(8.3)_, we have the exact sequence $op("Omega")_(B\/A) times.o_op("BC") to op("Omega")_(C\/A) to op("Omega")_(C\/B) to 0$ of $C$-modules. Taking the exact functor $M mapsto op("widetilde")M$ gives
  #remark[Diagram.]
  an exact sequence of $shf.o_X$-modules.
]
// Hartshorne II.8, Proposition 8.12
#proposition(number: "8.12")[
  Given a morphism $X arrow.r.long Y$, and let $Z subset X$ be a closed subscheme with its ideal sheaf $shf.i$. Then there is an exact sequence of $shf.o_Z$-modules:
  $
    shf.i \/ shf.i^2 arrow.r.long op("Omega")_(X\/Y) times.o shf.o_Z arrow.r.long op("Omega")_(Z\/Y) arrow.r.long 0.
  $
]
#proof[
  From _(8.9.2)_, the question is local, so we may reduce to the affine case. Suppose $Y,\ X$ are the spectra of the rings $A,\ B$, respectively. Now, the closed subscheme $Z subset X$ is determined by an ideal $op("Iop")("triangleleft") B$, for which $Z simeq ops.spec B\/I$ and $shf.i simeq op("widetilde")I$ by _(5.10)_. Now, _(8.4)_ gives the exact sequence $I\/I^2 arrow.r.long op("Omega")_(B\/A) times.o_op("BC") to op("Omega")_(C\/A) to 0$ of $C=B\/I$-modules. Taking the exact functor $M mapsto op("widetilde")M$ gives
  #remark[Diagram.]
  an exact sequence of $shf.o_Z$-modules.
]
#example(title: "8.12.1")[
  If $X= sch.a_Y^n$ for any scheme $Y$, then $op("Omega")_(X\/Y) in cat.mod(shf.o_X)$ is a free module of rank $n$, generated by global sections $op("dx")_i_i=1^n$.
]
#proof[
  Consider the fibre square
  #remark[Diagram.]
  We have
  $
    op("Omega")_(X\/Y)attach(simeq, b: "text(\"(8.10)\")")g^ast op("Omega")_(Z\/S)attach(simeq, b: "text(\"(8.9.2)\")")g^ast (op("Omega")_(ZZ[x_1, dots.c ,x_n]\/ZZ))op("widetilde").
  $
  Further, $(op("Omega")_(ZZ[x_1, dots.c ,x_n]\/ZZ))op("widetilde")$ is a free $shf.o_Z$-module generated by the global sections $op("dx")_i_i=1^n$, whence $op("Omega")_(X\/Y)$ is a free $shf.o_X$-module generated by the global sections $g^ast op("dx")_i_i=1^n$.
]
// Hartshorne II.8, Theorem 8.13
#theorem(number: "8.13")[
  Let $A in cat.ring ,\ Y=ops.spec A$, and $X= sch.p_A^n$. Then there is an exact sequence of $shf.o_X$-modules:
  $
    0 arrow.r.long op("Omega")_(X\/Y) arrow.r.long shf.o_X (-1)^(plus.o (n+1)) arrow.r.long shf.o_X arrow.r.long 0.
  $
]
#proof[
  (I) Construct the exact sequence.
  - Write $S=A[x_0, dots.c ,x_n]$, then $X= ops.proj S$. Let $E := S(-1)^(plus.o (n+1)) in cat.gr cat.mod(S)$ be the free graded module with an $S$-basis $e_i_i=0^n$ where $e_i=(0, dots.c ,attach(1, b: "op(\"itext\")(\"th\")"), dots.c ,0) in S_0^(plus.o (n+1))=E_1$.
  - For each $x_i in S_1$, we have a natural graded homomorphism
  $
    op("alpha")_i:S(-1) arrow.r.long S,op("quad")1 in S(-1)_1 mapsto x_i in S_1.
  $
  Then $op("alpha") := op("alpha")_0 plus.o dots.c plus.o op("alpha")_n$ gives a graded homomorphism $E to S$. Let $M := ops.ker op("alpha")$, then we have the exact sequence $0 to M to E to S$ of graded $S$-modules. By taking the functor $N mapsto op("widetilde")N$, it induces an exact sequence of $shf.o_X$-modules:
  $
    0 arrow.r.long op("widetilde")M arrow.r.long op("widetilde")E= shf.o_X (-1)^(plus.o (n+1)) arrow.r.long shf.o_X arrow.r.long 0.
  $
  - Note that the map $op("alpha")$ is NOT surjective (as $E_0=S_(-1)^(plus.o (n+1))=op("emptyset")$), but it is surjective in $E_(>= 1) to S_(>= 1)$, so the corresponding sheaf map $op("widetilde")E to op("widetilde")S$ is still surjective!
  (II) _Claim._ $op("widetilde")M simeq op("Omega")_(X\/Y)$ as $shf.o_X$-modules.
  - First, we localize at each $x_i$. Then, $op("alpha")_(x_i):E_(x_i) to S_(x_i)$ is clearly a surjective graded  homomorphism of free $S_(x_i)$-modules. We see in the following that $M_(x_i)$ is also a free $S_(x_i)$-modules of rank $n$ with an $S_(x_i)$-basis $(e_op("jx")_i-e_op("ix")_j)/(x_i):j != i$. Obviously, we have $op("alpha")_(x_i) ((e_op("jx")_i-e_op("ix")_j)/(x_i))=(x_op("jx")_i-x_op("ix")_j)/(x_i)=0$ for every $j != i$. On the other hand, suppose $s in M_(x_i)= ops.ker op("alpha")_(x_i)$, we write $s := op("sum")_(j != i) (a_op("je")_j)/(x_i^k)$ ($a_j in S$), which sends via $op("alpha")_(x_i)$ to $op("sum")_(j != i) (a_op("je")_j)/(x_i^k)=0$. So, $exists \ l>0$ for which $x_i^op("lop") ("sum")_(j != i)a_op("jx")_j=0$. Now, %since
  we obtain
  $
    s=op("frac")op("sum")_(j != i)a_op("je")_op("jx")_op("ix")_i^(k+1)-op("underbrace")op("frac")e_op("iop") ("sum")_(j != i)a_op("jx")_op("jx")_i^(k+1)_=0=op("sum")_(j != i) (a_j)/(x_i^k)op("bigg")((e_op("jx")_i-e_op("ix")_j)/(x_i)op("bigg")) in S_(x_i) spn op("bigg")(e_op("jx")_i-e_op("ix")_j)/(x_i):j != op("iop")("bigg").
  $
  Moreover, it is easy to check that they are $S_(x_i)$-linearly independent, whence they form a basis over $S_(x_i)$.
  - Let $U_i := D_+(x_i)$ for each $i$. Now, it follows from the previous discussion that $op("widetilde")M|_U_i simeq (M_((x_i)))op("widetilde")$ is a free $shf.o_X|_U_i$-module generated by the sections $(e_op("jx")_i-e_op("ix")_j)/(x_i^2):j != i$ on $U_i$. (Here we need the additional factor $1/x_i$ since $x_i in S_1 subset E_2$, and $x_i^2 in S_1 dot E_2 subset E_3$).
  - For each $i$, we define a map $op("phi")_i:op("Omega")_(X\/Y)|_U_i to op("widetilde")M|_U_i$ as follows. Note that $U_i simeq ops.spec S_((x_i))=ops.spec A[(x_0)/(x_i), dots.c ,(x_n)/(x_i)]$, so $op("Omega")_(X\/Y)|_U_i simeq (op("Omega")_S_((x_i)\/A))op("widetilde")$ is a free $shf.o_X|_U_i$-module generated by the global sections $d(x_j/x_i):j != i$ on $U_i$. Now, we define
  $
    op("beta")_i:op("Omega")_S_((x_i))\/A arrow.r.long M_((x_i)),op("quad") op("dop")("Big")((x_j)/(x_i)op("Big")) mapsto (e_op("jx")_i-e_op("ix")_j)/(x_i^2),
  $
  which is thus an $S_((x_i))$-module isomorphism. From _[5.3]_, $op("beta")_i$ corresponds to an isomorphism $op("phi")_i:op("Omega")_(X\/Y)|_U_i to op("widetilde")M|_U_i$ of free $shf.o_X|_U_i$-modules.
  - _Claim._ The isomorphisms $op("phi")_i$ glue to give an isomorphism $op("Omega")_(X\/Y) arrow.r.long op("widetilde")M$.
  We look at the intersection $U_(op("ij"))=U_op("iop") ("cap") U_j simeq ops.spec S_((x_op("ix")_j))$, we have $(x_k)/(x_i)=(x_k)/(x_j)(x_j)/(x_i)$ for any $k$, which gives
  $
    op("dop")("Big")((x_k)/(x_i)op("Big"))=(x_k)/(x_j)op("dop")("Big")((x_j)/(x_i)op("Big"))+(x_j)/(x_i)op("dop")("Big")((x_k)/(x_j)op("Big")) idl.q op("uadtext")("in")\ op("Omega")_S_((x_op("ix")_j))\/A.
  $
  (Here, $d=d_S_(x_op("ix")_j)\/A$). Now, we have
  $
    op("phi")_i|_op("ijop") ("bigg")(op("dop")("Big")((x_k)/(x_i)op("Big"))-(x_k)/(x_j)op("dop")("Big")((x_j)/(x_i)op("Big"))op("bigg")) &=(e_op("kx")_i-e_op("ix")_k)/(x_i^2)-(x_k)/(x_j)(e_op("jx")_i-e_op("ix")_j)/(x_i^2)=(x_j)/(x_i)(e_op("kx")_j-e_op("jx")_k)/(x_j^2)=op("phi")_j|_op("ijop") ("bigg")((x_j)/(x_i)op("dop")("Big")((x_k)/(x_j)op("Big"))op("bigg"))
  $
  for every $k$. Therefore, the ismorphisms $op("phi")_i$ glue on $U_i$ and obtain such isomorphism $op("phi")$.
]
